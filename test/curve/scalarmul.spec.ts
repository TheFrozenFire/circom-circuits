import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { scalarMul, babyAdd, BASE8_X, BASE8_Y } from "../babyjub_utils.js";

// Convert a scalar to n LE bits.
function scalarToBitsLE(scalar: bigint, n: number): number[] {
    const bits: number[] = [];
    for (let i = 0; i < n; i++) {
        bits.push(Number((scalar >> BigInt(i)) & 1n));
    }
    return bits;
}

describe_circuit("EscalarMulFix (via TestEscalarMulFixBase8)", {
    fix: { path: "curve/test_scalarmul.circom", template: "TestEscalarMulFixBase8" },
}, (calculators) => {
    it("scalar=1 → BASE8", async () => {
        const bits = scalarToBitsLE(1n, 8);
        const w = await calculators.fix.calculate({ e: bits });
        assert.equal(w.value("main.out[0]"), BASE8_X);
        assert.equal(w.value("main.out[1]"), BASE8_Y);
    });

    it("scalar=2 → 2*BASE8", async () => {
        const [ex, ey] = scalarMul(2n, BASE8_X, BASE8_Y);
        const bits = scalarToBitsLE(2n, 8);
        const w = await calculators.fix.calculate({ e: bits });
        assert.equal(w.value("main.out[0]"), ex);
        assert.equal(w.value("main.out[1]"), ey);
    });

    it("scalar=7 → 7*BASE8", async () => {
        const [ex, ey] = scalarMul(7n, BASE8_X, BASE8_Y);
        const bits = scalarToBitsLE(7n, 8);
        const w = await calculators.fix.calculate({ e: bits });
        assert.equal(w.value("main.out[0]"), ex);
        assert.equal(w.value("main.out[1]"), ey);
    });

    it("scalar=255 → 255*BASE8", async () => {
        const [ex, ey] = scalarMul(255n, BASE8_X, BASE8_Y);
        const bits = scalarToBitsLE(255n, 8);
        const w = await calculators.fix.calculate({ e: bits });
        assert.equal(w.value("main.out[0]"), ex);
        assert.equal(w.value("main.out[1]"), ey);
    });
});

describe_circuit("EscalarMulAny", {
    any: { path: "curve/scalarmul.circom", template: "EscalarMulAny", params: [8] },
}, (calculators) => {
    it("scalar=7 × BASE8 → 7*BASE8", async () => {
        const [ex, ey] = scalarMul(7n, BASE8_X, BASE8_Y);
        const bits = scalarToBitsLE(7n, 8);
        const w = await calculators.any.calculate({
            e: bits,
            p: [BASE8_X, BASE8_Y],
        });
        assert.equal(w.value("main.out[0]"), ex);
        assert.equal(w.value("main.out[1]"), ey);
    });

    it("scalar=3 × 2*BASE8 → 6*BASE8", async () => {
        const [px, py] = scalarMul(2n, BASE8_X, BASE8_Y);
        const [ex, ey] = scalarMul(6n, BASE8_X, BASE8_Y);
        const bits = scalarToBitsLE(3n, 8);
        const w = await calculators.any.calculate({
            e: bits,
            p: [px, py],
        });
        assert.equal(w.value("main.out[0]"), ex);
        assert.equal(w.value("main.out[1]"), ey);
    });

    it("scalar=1 × BASE8 → BASE8", async () => {
        const bits = scalarToBitsLE(1n, 8);
        const w = await calculators.any.calculate({
            e: bits,
            p: [BASE8_X, BASE8_Y],
        });
        assert.equal(w.value("main.out[0]"), BASE8_X);
        assert.equal(w.value("main.out[1]"), BASE8_Y);
    });
});
