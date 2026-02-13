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

    dbLeaves = DB_IDS.map(id => {
        const fieldVec = toFieldArray(getEmbedding(fixture, id));
        return vectorCommit(fieldVec, CHUNK_SIZE);
    });

    merkleLayers = buildMerkleTree(dbLeaves);
    merkleRoot = merkleLayers[merkleLayers.length - 1][0];
});

describe_circuit("PrivateDedup", {
    dedup: {
        path: "search/dedup.circom",
        template: "PrivateDedup",
        params: [384, 12, DB_DEPTH, 64],
        publicInputs: ["documentCommit", "merkleRoot", "minDistSq"],
    },
}, (calculators) => {
    it("accepts dissimilar pair (cat_mat vs stock_market)", async () => {
        const docRaw = getEmbedding(fixture, "cat_mat");
        const candId = "stock_market";
        const candIdx = DB_IDS.indexOf(candId);
        const candRaw = getEmbedding(fixture, candId);

        const distSq = jsEuclideanDistSq(docRaw, candRaw);
        const minDistSq = 1500000n;
        assert.isTrue(distSq > minDistSq,
            `expected distSq=${distSq} > minDistSq=${minDistSq}`);

        const docField = toFieldArray(docRaw);
        const documentCommit = vectorCommit(docField, CHUNK_SIZE);
        const { pathIndices, siblings } = getMerkleProof(candIdx, merkleLayers, DB_DEPTH);

        await calculators.dedup.calculate({
            document: docField,
            candidate: toFieldArray(candRaw),
            pathIndices,
            siblings,
            documentCommit,
            merkleRoot,
            minDistSq,
        });
    });

    it("rejects similar pair (cat_mat vs kitten_rug)", async () => {
        const docRaw = getEmbedding(fixture, "cat_mat");
        const candId = "kitten_rug";
        const candIdx = DB_IDS.indexOf(candId);
        const candRaw = getEmbedding(fixture, candId);

        const distSq = jsEuclideanDistSq(docRaw, candRaw);
        const minDistSq = 1000000n;
        assert.isTrue(distSq < minDistSq,
            `expected distSq=${distSq} < minDistSq=${minDistSq}`);

        const docField = toFieldArray(docRaw);
        const documentCommit = vectorCommit(docField, CHUNK_SIZE);
        const { pathIndices, siblings } = getMerkleProof(candIdx, merkleLayers, DB_DEPTH);

        try {
            await calculators.dedup.calculate({
                document: docField,
                candidate: toFieldArray(candRaw),
                pathIndices,
                siblings,
                documentCommit,
                merkleRoot,
                minDistSq,
            });
            assert.fail("should have rejected: distance below threshold");
        } catch (e: any) {
            assert.notEqual(e.message, "should have rejected: distance below threshold");
        }
    });

    it("rejects wrong document commitment", async () => {
        const docRaw = getEmbedding(fixture, "cat_mat");
        const candId = "stock_market";
        const candIdx = DB_IDS.indexOf(candId);
        const candRaw = getEmbedding(fixture, candId);

        const docField = toFieldArray(docRaw);
        // Use kitten_rug's commitment instead of cat_mat's
        const wrongCommit = vectorCommit(toFieldArray(getEmbedding(fixture, "kitten_rug")), CHUNK_SIZE);
        const { pathIndices, siblings } = getMerkleProof(candIdx, merkleLayers, DB_DEPTH);

        try {
            await calculators.dedup.calculate({
                document: docField,
                candidate: toFieldArray(candRaw),
                pathIndices,
                siblings,
                documentCommit: wrongCommit,
                merkleRoot,
                minDistSq: 1500000n,
            });
            assert.fail("should have rejected: wrong document commitment");
        } catch (e: any) {
            assert.notEqual(e.message, "should have rejected: wrong document commitment");
        }
    });

    it("rejects candidate not in database (baked_bread)", async () => {
        const docRaw = getEmbedding(fixture, "cat_mat");
        // baked_bread is not in the 8-entry DB
        const candRaw = getEmbedding(fixture, "baked_bread");

        const docField = toFieldArray(docRaw);
        const documentCommit = vectorCommit(docField, CHUNK_SIZE);
        // Use Merkle proof for index 0 (cat_mat's position) — leaf won't match
        const { pathIndices, siblings } = getMerkleProof(0, merkleLayers, DB_DEPTH);

        try {
            await calculators.dedup.calculate({
                document: docField,
                candidate: toFieldArray(candRaw),
                pathIndices,
                siblings,
                documentCommit,
                merkleRoot,
                minDistSq: 100000n, // low threshold so distance isn't the issue
            });
            assert.fail("should have rejected: candidate not in database");
        } catch (e: any) {
            assert.notEqual(e.message, "should have rejected: candidate not in database");
        }
    });
});
