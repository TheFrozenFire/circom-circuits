import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// ── CheckCarryToZero ───────────────────────────────────────────────
// Verifies that a k-limb value with n-bit limbs sums to zero via carries.
// Template params: (n, m, k) where m bounds carry size.

describe_circuit("CheckCarryToZero", {
    ccz: {
        path: "arithmetic/bigint.circom",
        template: "CheckCarryToZero",
        params: [4, 4, 3],
    },
}, (calculators) => {
    it("accepts all-zero limbs", async () => {
        // [0, 0, 0] trivially sums to zero
        const w = await calculators.ccz.calculate({ in: [0, 0, 0] });
        assert.ok(w);
    });

    it("accepts limbs that cancel via carries", async () => {
        // n=4, so 2^n = 16
        // in[0]=16 → carry[0] = 1, residue = 0
        // in[1]=-1 + carry[0] = 0 → carry[1] = 0
        // in[2]=0 + carry[1] = 0 → satisfied
        // Actually: in[0] = 16, in[1] = -1, in[2] = 0 doesn't work because
        // in[k-1] + carry[k-2] === 0 needs in[2] = -carry[1].
        //
        // Simpler: in = [16, 0, -1]
        // carry[0] = 16/16 = 1 (in[0] = 1 * 16)
        // in[1] + carry[0] = 0 + 1 = carry[1] * 16 → carry[1] = 0, but 1 ≠ 0*16
        //
        // Let's use: in = [32, -16, -1]
        // carry[0] = 32/16 = 2, check: 32 = 2*16 ✓
        // in[1] + carry[0] = -16 + 2 = -14, need -14 = carry[1]*16 → no integer carry
        //
        // Simplest valid: in = [16, -16, 0]
        // carry[0] = 16/16 = 1, check: 16 = 1*16 ✓
        // in[2] + carry[1-1=0] → need in[1] + carry[0] = 0 → -16 + 1 ≠ 0
        //
        // For k=3: in[0] = carry[0]*2^n, in[1]+carry[0] = carry[1]*2^n, in[2]+carry[1] = 0
        // Let carry[0]=1, carry[1]=1: in[0]=16, in[1]=16-1=15... nope, 15+1=16=1*16 works!
        // in[2]+1=0 → in[2]=-1
        // So in = [16, 15, -1]... but -1 is negative in field arithmetic
        //
        // Better: use the field's representation. Circom field is ~2^253.
        // -1 in circom field is p-1.
        const p = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
        const w = await calculators.ccz.calculate({
            in: [16, 15, p - 1n],
        });
        assert.ok(w);
    });

    it("accepts [48, -48, 0] pattern", async () => {
        // carry[0] = 48/16 = 3, check: 48 = 3*16 ✓
        // in[1] + carry[0] = -48 + 3 = -45... not divisible by 16
        // Try [48, -3, 0]: carry[0]=3, in[1]+carry[0] = -3+3 = 0 = carry[1]*16, carry[1]=0
        // in[2]+carry[1] = 0+0 = 0 ✓
        const p = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
        const w = await calculators.ccz.calculate({
            in: [48, p - 3n, 0],
        });
        assert.ok(w);
    });
});

// ── LongToShortNoEndCarry ──────────────────────────────────────────
// Converts oversized limbs to proper n-bit limbs via carry propagation.
// Template params: (n, k)

describe_circuit("LongToShortNoEndCarry", {
    l2s: {
        path: "arithmetic/bigint.circom",
        template: "LongToShortNoEndCarry",
        params: [4, 3],
    },
}, (calculators) => {
    it("identity for already-valid limbs", async () => {
        // n=4 → max limb value 15. Input [5, 10, 3] is already valid.
        const w = await calculators.l2s.calculate({ in: [5, 10, 3] });
        assert.equal(w.value("main.out[0]"), 5n);
        assert.equal(w.value("main.out[1]"), 10n);
        assert.equal(w.value("main.out[2]"), 3n);
    });

    it("carries overflow from lower to higher limbs", async () => {
        // n=4, 2^n=16. Input [20, 0, 0].
        // out[0] = 20 % 16 = 4, carry = 20 >> 4 = 1
        // out[1] = (0 + 1) % 16 = 1, carry = 0
        // out[2] = 0 + 0 = 0
        const w = await calculators.l2s.calculate({ in: [20, 0, 0] });
        assert.equal(w.value("main.out[0]"), 4n);
        assert.equal(w.value("main.out[1]"), 1n);
        assert.equal(w.value("main.out[2]"), 0n);
    });

    it("cascading carries", async () => {
        // [255, 0, 0]: 255 = 15*16 + 15
        // out[0] = 255 % 16 = 15, carry = 15
        // out[1] = (0+15) % 16 = 15, carry = 0
        // out[2] = 0 + 0 = 0
        const w = await calculators.l2s.calculate({ in: [255, 0, 0] });
        assert.equal(w.value("main.out[0]"), 15n);
        assert.equal(w.value("main.out[1]"), 15n);
        assert.equal(w.value("main.out[2]"), 0n);
    });

    it("preserves total value across limbs", async () => {
        // Total value = sum(out[i] * 2^(n*i)) should equal sum(in[i] * 2^(n*i))
        const inp = [30, 20, 1]; // 30 + 20*16 + 1*256 = 30 + 320 + 256 = 606
        const w = await calculators.l2s.calculate({ in: inp });
        const totalIn = 30n + 20n * 16n + 1n * 256n;
        const totalOut =
            w.value("main.out[0]") +
            w.value("main.out[1]") * 16n +
            w.value("main.out[2]") * 256n;
        assert.equal(totalOut, totalIn);
    });
});
