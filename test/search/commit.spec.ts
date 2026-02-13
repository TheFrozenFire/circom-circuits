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

/** JS reference implementation of VectorCommit: chunked Poseidon + binary tree. */
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

let fixture: EmbeddingFixture;

before(async function () {
    const fixturePath = resolve(__dirname, "../fixtures/embeddings.json");
    fixture = JSON.parse(await readFile(fixturePath, "utf-8"));
});

describe_circuit("VectorCommit", {
    vc: { path: "search/commit.circom", template: "VectorCommit", params: [384, 12] },
}, (calculators) => {
    it("hash matches JS reference for real embedding", async () => {
        const raw = getEmbedding(fixture, "cat_mat");
        const fieldVec = toFieldArray(raw);
        const expected = vectorCommit(fieldVec, 12);

        const w = await calculators.vc.calculate({ v: fieldVec });
        assert.equal(w.value("main.out"), expected);
    });

    it("different vectors produce different hashes", async () => {
        const vec1 = toFieldArray(getEmbedding(fixture, "cat_mat"));
        const vec2 = toFieldArray(getEmbedding(fixture, "kitten_rug"));

        const w1 = await calculators.vc.calculate({ v: vec1 });
        const h1 = w1.value("main.out");

        const w2 = await calculators.vc.calculate({ v: vec2 });
        const h2 = w2.value("main.out");

        assert.notEqual(h1, h2);

        // Also verify both match their JS references
        assert.equal(h1, vectorCommit(vec1, 12));
        assert.equal(h2, vectorCommit(vec2, 12));
    });
});
