import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { Poseidon } from "@iden3/js-crypto";

// ── Sigma ──────────────────────────────────────────────────────────
// S-box: out = in^5

describe_circuit("Sigma", {
    sigma: { path: "hash/poseidon.circom", template: "Sigma" },
}, (calculators) => {
    it("computes x^5 for small values", async () => {
        const w = await calculators.sigma.calculate({ in: 2 });
        assert.equal(w.value("main.out"), 32n); // 2^5
    });

    it("computes 0^5 = 0", async () => {
        const w = await calculators.sigma.calculate({ in: 0 });
        assert.equal(w.value("main.out"), 0n);
    });

    it("computes 1^5 = 1", async () => {
        const w = await calculators.sigma.calculate({ in: 1 });
        assert.equal(w.value("main.out"), 1n);
    });

    it("computes 3^5 = 243", async () => {
        const w = await calculators.sigma.calculate({ in: 3 });
        assert.equal(w.value("main.out"), 243n);
    });
});

// ── Ark ────────────────────────────────────────────────────────────
// Add round constants: out[i] = in[i] + C[i + r]
// Tested via TestArk wrapper (t=3, uses real Poseidon constants)

describe_circuit("Ark", {
    ark: { path: "hash/test_poseidon_parts.circom", template: "TestArk" },
}, (calculators) => {
    it("adds round constants to input", async () => {
        const w = await calculators.ark.calculate({ in: [0, 0, 0] });
        const out = w.array("main.out");
        // With zero input, output should be the first 3 round constants
        // They should be non-zero field elements
        for (const v of out) {
            assert.notEqual(v, 0n, "round constants should be non-zero");
        }
    });

    it("is additive with input", async () => {
        const w0 = await calculators.ark.calculate({ in: [0, 0, 0] });
        const c = w0.array("main.out"); // these are the constants

        const w1 = await calculators.ark.calculate({ in: [1, 2, 3] });
        const out = w1.array("main.out");

        // out[i] should be in[i] + C[i], so out[i] - C[i] = in[i]
        for (let i = 0; i < 3; i++) {
            assert.equal(out[i] - c[i], BigInt(i + 1));
        }
    });
});

// ── Mix ────────────────────────────────────────────────────────────
// Full MDS matrix multiplication: out[i] = sum_j(M[j][i] * in[j])

describe_circuit("Mix", {
    mix: { path: "hash/test_poseidon_parts.circom", template: "TestMix" },
}, (calculators) => {
    it("maps zero to zero (linear)", async () => {
        const w = await calculators.mix.calculate({ in: [0, 0, 0] });
        assert.deepEqual(w.array("main.out"), [0n, 0n, 0n]);
    });

    it("produces non-trivial output for non-zero input", async () => {
        const w = await calculators.mix.calculate({ in: [1, 0, 0] });
        const out = w.array("main.out");
        // M * [1,0,0] should give the first column of M
        const allZero = out.every((v) => v === 0n);
        assert.isFalse(allZero, "MDS mix should produce non-zero output");
    });
});

// ── MixLast ────────────────────────────────────────────────────────
// Extracts a single output element from MDS mix

describe_circuit("MixLast", {
    ml: { path: "hash/test_poseidon_parts.circom", template: "TestMixLast" },
}, (calculators) => {
    it("extracts element 0 of MDS mix", async () => {
        const w = await calculators.ml.calculate({ in: [1, 2, 3] });
        const out = w.value("main.out");
        assert.notEqual(out, 0n);
    });

    it("zero input gives zero", async () => {
        const w = await calculators.ml.calculate({ in: [0, 0, 0] });
        assert.equal(w.value("main.out"), 0n);
    });
});

// ── MixS ───────────────────────────────────────────────────────────
// Sparse matrix mix for partial rounds

describe_circuit("MixS", {
    ms: { path: "hash/test_poseidon_parts.circom", template: "TestMixS" },
}, (calculators) => {
    it("maps zero to zero", async () => {
        const w = await calculators.ms.calculate({ in: [0, 0, 0] });
        assert.deepEqual(w.array("main.out"), [0n, 0n, 0n]);
    });

    it("produces non-trivial output for non-zero input", async () => {
        const w = await calculators.ms.calculate({ in: [1, 0, 0] });
        const out = w.array("main.out");
        const allZero = out.every((v) => v === 0n);
        assert.isFalse(allZero);
    });
});

// ── PoseidonEx ─────────────────────────────────────────────────────
// Extended Poseidon with configurable initial state and output count

describe_circuit("PoseidonEx", {
    pex: { path: "hash/poseidon.circom", template: "PoseidonEx", params: [2, 1] },
}, (calculators) => {
    it("with initialState=0, matches Poseidon(2)", async () => {
        const expected = Poseidon.hash([3n, 7n]);
        const w = await calculators.pex.calculate({
            inputs: [3, 7],
            initialState: 0,
        });
        assert.equal(w.value("main.out[0]"), expected);
    });

    it("different inputs give different outputs", async () => {
        const w0 = await calculators.pex.calculate({
            inputs: [3, 7],
            initialState: 0,
        });
        const out0 = w0.value("main.out[0]");

        const w1 = await calculators.pex.calculate({
            inputs: [7, 3],
            initialState: 0,
        });
        const out1 = w1.value("main.out[0]");

        assert.notEqual(out0, out1);
    });
});
