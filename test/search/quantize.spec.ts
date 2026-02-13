import { assert } from "chai";
import { readFile } from "fs/promises";
import { resolve, dirname } from "path";
import { fileURLToPath } from "url";
import { describe_circuit } from "../helpers.js";
import { Poseidon } from "@iden3/js-crypto";

const __dirname = dirname(fileURLToPath(import.meta.url));

const P = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

const SCALE = 1000;
const PRECISION = 20;
const CHUNK_SIZE = 12;

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

/**
 * Derive a fixed-point embedding from quantized values.
 * embedding[i] = round(quantized[i] * 2^precision / scale)
 * This produces valid (embedding, quantized) pairs by construction.
 */
function deriveFixedPoint(quantized: number[]): bigint[] {
    const fullRange = 1 << PRECISION;
    return quantized.map(q => {
        const fp = Math.round(q * fullRange / SCALE);
        return toField(fp);
    });
}

let fixture: EmbeddingFixture;

before(async function () {
    const fixturePath = resolve(__dirname, "../fixtures/embeddings.json");
    fixture = JSON.parse(await readFile(fixturePath, "utf-8"));
});

describe_circuit("QuantizationProof", {
    qp: {
        path: "search/quantize.circom",
        template: "QuantizationProof",
        params: [384, CHUNK_SIZE, SCALE, PRECISION],
        publicInputs: ["embeddingCommit", "quantizedCommit"],
    },
}, (calculators) => {
    it("accepts correct quantization", async () => {
        const raw = getEmbedding(fixture, "cat_mat");
        const quantizedField = toFieldArray(raw);
        const embeddingField = deriveFixedPoint(raw);

        const embeddingCommit = vectorCommit(embeddingField, CHUNK_SIZE);
        const quantizedCommit = vectorCommit(quantizedField, CHUNK_SIZE);

        const w = await calculators.qp.calculate({
            embedding: embeddingField,
            quantized: quantizedField,
            embeddingCommit,
            quantizedCommit,
        });

        assert.equal(w.value("main.embeddingCommit"), embeddingCommit);
        assert.equal(w.value("main.quantizedCommit"), quantizedCommit);
    });

    it("rejects perturbed quantized value", async () => {
        const raw = getEmbedding(fixture, "cat_mat");
        const perturbed = [...raw];
        perturbed[0] += 1; // off-by-one in quantized

        const quantizedField = toFieldArray(perturbed);
        const embeddingField = deriveFixedPoint(raw); // derived from original

        const embeddingCommit = vectorCommit(embeddingField, CHUNK_SIZE);
        const quantizedCommit = vectorCommit(quantizedField, CHUNK_SIZE);

        try {
            await calculators.qp.calculate({
                embedding: embeddingField,
                quantized: quantizedField,
                embeddingCommit,
                quantizedCommit,
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects wrong embedding commitment", async () => {
        const raw = getEmbedding(fixture, "cat_mat");
        const quantizedField = toFieldArray(raw);
        const embeddingField = deriveFixedPoint(raw);

        // Use a different embedding's commitment
        const wrongRaw = getEmbedding(fixture, "kitten_rug");
        const wrongEmbeddingField = deriveFixedPoint(wrongRaw);
        const wrongEmbeddingCommit = vectorCommit(wrongEmbeddingField, CHUNK_SIZE);

        const quantizedCommit = vectorCommit(quantizedField, CHUNK_SIZE);

        try {
            await calculators.qp.calculate({
                embedding: embeddingField,
                quantized: quantizedField,
                embeddingCommit: wrongEmbeddingCommit,
                quantizedCommit,
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});
