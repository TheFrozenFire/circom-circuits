import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// BigMultNoCarry(n, ma, mb, ka, kb):
//   n=4 (limb bit width), ma=4 (a limb bit width), mb=4 (b limb bit width)
//   ka=2 (a limb count), kb=2 (b limb count)
//   Output has ka+kb-1 = 3 limbs, each potentially wider than n bits.

describe_circuit("BigMultNoCarry", {
    mul: { path: "arithmetic/bigint.circom", template: "BigMultNoCarry", params: [4, 4, 4, 2, 2] },
}, (calculators) => {
    it("multiplies single-limb values", async () => {
        // [3, 0] × [4, 0] = 3*4 = 12 → out = [12, 0, 0]
        const w = await calculators.mul.calculate({ a: [3, 0], b: [4, 0] });
        const out = w.array("main.out");
        assert.equal(out[0], 12n);
        assert.equal(out[1], 0n);
        assert.equal(out[2], 0n);
    });

    it("multiplies with cross-limb products", async () => {
        // [15, 1] × [2, 0]:
        //   products[0][0] = 15*2 = 30
        //   products[1][0] = 1*2 = 2
        //   out[0] = 30, out[1] = 2, out[2] = 0
        const w = await calculators.mul.calculate({ a: [15, 1], b: [2, 0] });
        const out = w.array("main.out");
        assert.equal(out[0], 30n);
        assert.equal(out[1], 2n);
        assert.equal(out[2], 0n);
    });

    it("multiplies with all limbs contributing", async () => {
        // [2, 3] × [4, 5]:
        //   sums[0] = 2*4 = 8
        //   sums[1] = 2*5 + 3*4 = 10 + 12 = 22
        //   sums[2] = 3*5 = 15
        const w = await calculators.mul.calculate({ a: [2, 3], b: [4, 5] });
        const out = w.array("main.out");
        assert.equal(out[0], 8n);
        assert.equal(out[1], 22n);
        assert.equal(out[2], 15n);
    });

    it("zero times nonzero equals zero", async () => {
        const w = await calculators.mul.calculate({ a: [0, 0], b: [7, 3] });
        const out = w.array("main.out");
        assert.equal(out[0], 0n);
        assert.equal(out[1], 0n);
        assert.equal(out[2], 0n);
    });
});
