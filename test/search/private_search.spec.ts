import { assert } from "chai";
import { readFile } from "fs/promises";
import { resolve, dirname } from "path";
import { fileURLToPath } from "url";
import { describe_circuit } from "../helpers.js";
import { Poseidon } from "@iden3/js-crypto";

const __dirname = dirname(fileURLToPath(import.meta.url));

const P = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

interface EmbeddingFixture {
    sentences: {
        id: string;
        quantized: number[];
    }[];
}

function toField(x: number): bigint {
    return x >= 0 ? BigInt(x) : P + BigInt(x);
}

function toFieldArray(quantized: number[]): bigint[] {
    return quantized.map(toField);
}

function getEmbedding(fixture: EmbeddingFixture, id: string): number[] {
    const s = fixture.sentences.find(s => s.id === id);
    if (!s) throw new Error(`Embedding not found: ${id}`);
    return s.quantized;
}

/** JS reference implementation of VectorCommit. */
function vectorCommit(v: bigint[], chunkSize: number): bigint {
    const nChunks = v.length / chunkSize;
    let hashes: bigint[] = [];
    for (let i = 0; i < nChunks; i++) {
        hashes.push(Poseidon.hash(v.slice(i * chunkSize, (i + 1) * chunkSize)));
    }
    while (hashes.length > 1) {
        const next: bigint[] = [];
        for (let i = 0; i < hashes.length; i += 2) {
            next.push(Poseidon.hash([hashes[i], hashes[i + 1]]));
        }
        hashes = next;
    }
    return hashes[0];
}

/** Build a Merkle tree from leaves and return all layers (bottom-up). */
function buildMerkleTree(leaves: bigint[]): bigint[][] {
    const layers: bigint[][] = [leaves];
    let current = leaves;
    while (current.length > 1) {
        const next: bigint[] = [];
        for (let i = 0; i < current.length; i += 2) {
            next.push(Poseidon.hash([current[i], current[i + 1]]));
        }
        layers.push(next);
        current = next;
    }
    return layers;
}

/** Get Merkle proof for leaf at given index. */
function getMerkleProof(index: number, layers: bigint[][], depth: number) {
    const pathIndices: number[] = [];
    const siblings: bigint[] = [];

    let idx = index;
    for (let i = 0; i < depth; i++) {
        pathIndices.push(idx % 2);
        const sibIdx = idx % 2 === 0 ? idx + 1 : idx - 1;
        siblings.push(layers[i][sibIdx]);
        idx = Math.floor(idx / 2);
    }

    return { pathIndices, siblings };
}

/** Compute Euclidean distance squared between two quantized vectors. */
function jsEuclideanDistSq(a: number[], b: number[]): bigint {
    let sum = 0n;
    for (let i = 0; i < a.length; i++) {
        const d = BigInt(a[i]) - BigInt(b[i]);
        sum += d * d;
    }
    return sum;
}

// Database: 8 embeddings → 3-level Merkle tree
const DB_IDS = [
    "cat_mat", "kitten_rug", "ml_datasets", "neural_gradient",
    "sun_mountains", "sunset_hills", "stock_market", "piano_sonata",
];
const DB_DEPTH = 3;
const CHUNK_SIZE = 12;

let fixture: EmbeddingFixture;
let dbLeaves: bigint[];
let merkleLayers: bigint[][];
let merkleRoot: bigint;

before(async function () {
    const fixturePath = resolve(__dirname, "../fixtures/embeddings.json");
    fixture = JSON.parse(await readFile(fixturePath, "utf-8"));

    // Compute vector commitments for all DB entries
    dbLeaves = DB_IDS.map(id => {
        const fieldVec = toFieldArray(getEmbedding(fixture, id));
        return vectorCommit(fieldVec, CHUNK_SIZE);
    });

    // Build Merkle tree
    merkleLayers = buildMerkleTree(dbLeaves);
    merkleRoot = merkleLayers[merkleLayers.length - 1][0];
});

describe_circuit("PrivateSearch", {
    ps: {
        path: "search/private_search.circom",
        template: "PrivateSearch",
        params: [384, 12, DB_DEPTH, 64],
        publicInputs: ["merkleRoot", "maxDistSq"],
    },
}, (calculators) => {
    it("accepts valid match (cat_mat → kitten_rug, cos≈0.61)", async () => {
        const query = getEmbedding(fixture, "cat_mat");
        const docId = "kitten_rug";
        const docIdx = DB_IDS.indexOf(docId);
        const document = getEmbedding(fixture, docId);

        const distSq = jsEuclideanDistSq(query, document);
        const maxDistSq = 1000000n;
        assert.isTrue(distSq < maxDistSq,
            `expected distSq=${distSq} < maxDistSq=${maxDistSq}`);

        const { pathIndices, siblings } = getMerkleProof(docIdx, merkleLayers, DB_DEPTH);

        await calculators.ps.calculate({
            query: toFieldArray(query),
            document: toFieldArray(document),
            pathIndices,
            siblings,
            merkleRoot,
            maxDistSq,
        });
    });

    it("rejects distant pair (cat_mat → stock_market, cos≈0.04)", async () => {
        const query = getEmbedding(fixture, "cat_mat");
        const docId = "stock_market";
        const docIdx = DB_IDS.indexOf(docId);
        const document = getEmbedding(fixture, docId);

        const distSq = jsEuclideanDistSq(query, document);
        const maxDistSq = 1000000n;
        assert.isTrue(distSq > maxDistSq,
            `expected distSq=${distSq} > maxDistSq=${maxDistSq}`);

        const { pathIndices, siblings } = getMerkleProof(docIdx, merkleLayers, DB_DEPTH);

        try {
            await calculators.ps.calculate({
                query: toFieldArray(query),
                document: toFieldArray(document),
                pathIndices,
                siblings,
                merkleRoot,
                maxDistSq,
            });
            assert.fail("should have rejected: distance exceeds threshold");
        } catch (e: any) {
            assert.notEqual(e.message, "should have rejected: distance exceeds threshold");
        }
    });

    it("rejects invalid Merkle proof (wrong sibling)", async () => {
        const query = getEmbedding(fixture, "cat_mat");
        const docId = "kitten_rug";
        const docIdx = DB_IDS.indexOf(docId);
        const document = getEmbedding(fixture, docId);

        const { pathIndices, siblings } = getMerkleProof(docIdx, merkleLayers, DB_DEPTH);

        // Corrupt the first sibling
        const badSiblings = [...siblings];
        badSiblings[0] = 999n;

        try {
            await calculators.ps.calculate({
                query: toFieldArray(query),
                document: toFieldArray(document),
                pathIndices,
                siblings: badSiblings,
                merkleRoot,
                maxDistSq: 1000000n,
            });
            assert.fail("should have rejected: invalid Merkle proof");
        } catch (e: any) {
            assert.notEqual(e.message, "should have rejected: invalid Merkle proof");
        }
    });

    it("rejects document not in database (baked_bread)", async () => {
        const query = getEmbedding(fixture, "cat_mat");
        // baked_bread is not in the DB
        const document = getEmbedding(fixture, "baked_bread");

        // Use Merkle proof for index 0 (cat_mat) — leaf won't match
        const { pathIndices, siblings } = getMerkleProof(0, merkleLayers, DB_DEPTH);

        try {
            await calculators.ps.calculate({
                query: toFieldArray(query),
                document: toFieldArray(document),
                pathIndices,
                siblings,
                merkleRoot,
                maxDistSq: 2000000n, // generous threshold so distance isn't the issue
            });
            assert.fail("should have rejected: document not in database");
        } catch (e: any) {
            assert.notEqual(e.message, "should have rejected: document not in database");
        }
    });
});
