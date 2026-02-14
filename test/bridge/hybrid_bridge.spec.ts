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

function polyUHF(r: bigint, x: bigint[]): bigint {
    let acc = x[x.length - 1];
    for (let i = x.length - 2; i >= 0; i--) {
        acc = ((acc * r % P) + x[i]) % P;
    }
    return ((acc % P) + P) % P;
}

let fixture: EmbeddingFixture;

before(async function () {
    const fixturePath = resolve(__dirname, "../fixtures/embeddings.json");
    fixture = JSON.parse(await readFile(fixturePath, "utf-8"));
});

describe_circuit("HybridBridge", {
    hb: {
        path: "bridge/hybrid_bridge.circom",
        template: "HybridBridge",
        params: [384, 12],
        publicInputs: ["poseidonCommit", "uhfValue", "challenge"],
    },
}, (calculators) => {
    it("happy path: correct poseidonCommit + uhfValue + challenge", async () => {
        const raw = getEmbedding(fixture, "cat_mat");
        const data = toFieldArray(raw);
        const poseidonCommit = vectorCommit(data, 12);
        const challenge = 999n;
        const uhfValue = polyUHF(challenge, data);

        const w = await calculators.hb.calculate({
            data, poseidonCommit, uhfValue, challenge,
        });

        assert.equal(w.value("main.poseidonCommit"), poseidonCommit);
        assert.equal(w.value("main.uhfValue"), uhfValue);
        assert.equal(w.value("main.challenge"), challenge);
    });

    it("rejects wrong poseidonCommit", async () => {
        const raw = getEmbedding(fixture, "cat_mat");
        const data = toFieldArray(raw);
        const wrongCommit = vectorCommit(toFieldArray(getEmbedding(fixture, "kitten_rug")), 12);
        const challenge = 999n;
        const uhfValue = polyUHF(challenge, data);

        try {
            await calculators.hb.calculate({
                data, poseidonCommit: wrongCommit, uhfValue, challenge,
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects wrong uhfValue", async () => {
        const raw = getEmbedding(fixture, "cat_mat");
        const data = toFieldArray(raw);
        const poseidonCommit = vectorCommit(data, 12);
        const challenge = 999n;
        const wrongUhf = polyUHF(challenge, data) + 1n;

        try {
            await calculators.hb.calculate({
                data, poseidonCommit, uhfValue: wrongUhf, challenge,
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects wrong challenge", async () => {
        const raw = getEmbedding(fixture, "cat_mat");
        const data = toFieldArray(raw);
        const poseidonCommit = vectorCommit(data, 12);
        const rightChallenge = 999n;
        const uhfValue = polyUHF(rightChallenge, data);
        const wrongChallenge = 1000n;

        try {
            await calculators.hb.calculate({
                data, poseidonCommit, uhfValue, challenge: wrongChallenge,
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});
