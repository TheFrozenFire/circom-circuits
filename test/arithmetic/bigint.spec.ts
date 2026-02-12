import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// Use small limb sizes (n=4, k=2) for fast test compilation.
// This gives 8-bit numbers split into two 4-bit limbs.
// Value = limb[0] + limb[1] * 16.

function toLimbs(val: number | bigint, n: number, k: number): bigint[] {
    const v = BigInt(val);
    const mask = (1n << BigInt(n)) - 1n;
    const limbs: bigint[] = [];
    let remaining = v;
    for (let i = 0; i < k; i++) {
        limbs.push(remaining & mask);
        remaining >>= BigInt(n);
    }
    return limbs;
}

function fromLimbs(limbs: bigint[], n: number): bigint {
    let val = 0n;
    for (let i = limbs.length - 1; i >= 0; i--) {
        val = (val << BigInt(n)) + limbs[i];
    }
    return val;
}

describe_circuit("BigAdd", {
    add: { path: "arithmetic/bigint.circom", template: "BigAdd", params: [4, 2] },
}, (calculators) => {
    it("adds without carry", async () => {
        // 3 + 4 = 7; a=[3,0], b=[4,0]
        const w = await calculators.add.calculate({ a: [3, 0], b: [4, 0] });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 7n);
    });

    it("adds with carry between limbs", async () => {
        // 10 + 10 = 20; a=[10,0], b=[10,0] → 20 = [4, 1, 0]
        const w = await calculators.add.calculate({ a: [10, 0], b: [10, 0] });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 20n);
    });

    it("adds max values", async () => {
        // 255 + 255 = 510; a=[15,15], b=[15,15] → 510
        const w = await calculators.add.calculate({ a: [15, 15], b: [15, 15] });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 510n);
    });

    it("adds with zero", async () => {
        const w = await calculators.add.calculate({ a: [5, 3], b: [0, 0] });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), fromLimbs([5n, 3n], 4));
    });
});

describe_circuit("BigSub", {
    sub: { path: "arithmetic/bigint.circom", template: "BigSub", params: [4, 2] },
}, (calculators) => {
    it("subtracts without borrow", async () => {
        // 200 - 50 = 150
        const a = toLimbs(200, 4, 2);
        const b = toLimbs(50, 4, 2);
        const w = await calculators.sub.calculate({ a, b });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 150n);
    });

    it("subtracts with borrow", async () => {
        // 16 - 1 = 15; a=[0,1], b=[1,0] → [15,0]
        const w = await calculators.sub.calculate({ a: [0, 1], b: [1, 0] });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 15n);
    });

    it("subtracts to zero", async () => {
        const w = await calculators.sub.calculate({ a: [5, 3], b: [5, 3] });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 0n);
    });
});

describe_circuit("BigMult", {
    mult: { path: "arithmetic/bigint.circom", template: "BigMult", params: [4, 2] },
}, (calculators) => {
    it("multiplies small values", async () => {
        // 3 * 5 = 15
        const a = toLimbs(3, 4, 2);
        const b = toLimbs(5, 4, 2);
        const w = await calculators.mult.calculate({ a, b });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 15n);
    });

    it("multiplies with carry propagation", async () => {
        // 15 * 15 = 225
        const a = toLimbs(15, 4, 2);
        const b = toLimbs(15, 4, 2);
        const w = await calculators.mult.calculate({ a, b });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 225n);
    });

    it("multiplies max values", async () => {
        // 255 * 255 = 65025
        const a = toLimbs(255, 4, 2);
        const b = toLimbs(255, 4, 2);
        const w = await calculators.mult.calculate({ a, b });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 65025n);
    });

    it("multiply by zero", async () => {
        const a = toLimbs(123, 4, 2);
        const b = toLimbs(0, 4, 2);
        const w = await calculators.mult.calculate({ a, b });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 0n);
    });

    it("multiply by one", async () => {
        const a = toLimbs(200, 4, 2);
        const b = toLimbs(1, 4, 2);
        const w = await calculators.mult.calculate({ a, b });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 200n);
    });
});

describe_circuit("BigLessThan", {
    lt: { path: "arithmetic/bigint.circom", template: "BigLessThan", params: [4, 2] },
}, (calculators) => {
    it("returns 1 when a < b", async () => {
        const a = toLimbs(10, 4, 2);
        const b = toLimbs(200, 4, 2);
        const w = await calculators.lt.calculate({ a, b });
        assert.equal(w.value("main.out"), 1n);
    });

    it("returns 0 when a > b", async () => {
        const a = toLimbs(200, 4, 2);
        const b = toLimbs(10, 4, 2);
        const w = await calculators.lt.calculate({ a, b });
        assert.equal(w.value("main.out"), 0n);
    });

    it("returns 0 when a == b", async () => {
        const a = toLimbs(42, 4, 2);
        const w = await calculators.lt.calculate({ a, b: a });
        assert.equal(w.value("main.out"), 0n);
    });

    it("compares correctly when low limbs differ", async () => {
        // a=33=[1,2], b=34=[2,2], differ only in low limb
        const a = toLimbs(33, 4, 2);
        const b = toLimbs(34, 4, 2);
        const w = await calculators.lt.calculate({ a, b });
        assert.equal(w.value("main.out"), 1n);
    });
});

describe_circuit("BigMod", {
    mod: { path: "arithmetic/bigint.circom", template: "BigMod", params: [4, 2] },
}, (calculators) => {
    // BigMod(4,2): a has 3 limbs (12-bit), b has 2 limbs (8-bit), output is 2 limbs.
    it("computes remainder", async () => {
        // 300 mod 200 = 100
        const a = toLimbs(300, 4, 3);
        const b = toLimbs(200, 4, 2);
        const w = await calculators.mod.calculate({ a, b });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 100n);
    });

    it("remainder is zero when divisible", async () => {
        // 510 mod 255 = 0
        const a = toLimbs(510, 4, 3);
        const b = toLimbs(255, 4, 2);
        const w = await calculators.mod.calculate({ a, b });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 0n);
    });

    it("value smaller than modulus", async () => {
        // 100 mod 200 = 100
        const a = toLimbs(100, 4, 3);
        const b = toLimbs(200, 4, 2);
        const w = await calculators.mod.calculate({ a, b });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 100n);
    });
});

describe_circuit("BigSubModP", {
    sub: { path: "arithmetic/bigint.circom", template: "BigSubModP", params: [4, 2] },
}, (calculators) => {
    // p = 251 (prime, fits in 8 bits)
    const p = toLimbs(251, 4, 2);

    it("subtracts without wrap", async () => {
        // (200 - 50) mod 251 = 150
        const a = toLimbs(200, 4, 2);
        const b = toLimbs(50, 4, 2);
        const w = await calculators.sub.calculate({ a, b, p });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 150n);
    });

    it("wraps on underflow", async () => {
        // (50 - 200) mod 251 = -150 mod 251 = 101
        const a = toLimbs(50, 4, 2);
        const b = toLimbs(200, 4, 2);
        const w = await calculators.sub.calculate({ a, b, p });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 101n);
    });

    it("a - a = 0 mod p", async () => {
        const a = toLimbs(123, 4, 2);
        const w = await calculators.sub.calculate({ a, b: a, p });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 0n);
    });
});

describe_circuit("BigMultModP", {
    mul: { path: "arithmetic/bigint.circom", template: "BigMultModP", params: [4, 2] },
}, (calculators) => {
    const p = toLimbs(251, 4, 2);

    it("multiplies with reduction", async () => {
        // (20 * 13) mod 251 = 260 mod 251 = 9
        const a = toLimbs(20, 4, 2);
        const b = toLimbs(13, 4, 2);
        const w = await calculators.mul.calculate({ a, b, p });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 9n);
    });

    it("multiplies without reduction", async () => {
        // (10 * 5) mod 251 = 50
        const a = toLimbs(10, 4, 2);
        const b = toLimbs(5, 4, 2);
        const w = await calculators.mul.calculate({ a, b, p });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 50n);
    });

    it("multiply by one", async () => {
        const a = toLimbs(200, 4, 2);
        const b = toLimbs(1, 4, 2);
        const w = await calculators.mul.calculate({ a, b, p });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 200n);
    });
});

describe_circuit("BigModInv", {
    inv: { path: "arithmetic/bigint.circom", template: "BigModInv", params: [4, 2] },
}, (calculators) => {
    const p = toLimbs(251, 4, 2);

    it("computes modular inverse", async () => {
        // 3^(-1) mod 251 = 84 (since 3*84 = 252 = 1 mod 251)
        const a = toLimbs(3, 4, 2);
        const w = await calculators.inv.calculate({ a, p });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 84n);
    });

    it("computes another inverse", async () => {
        // 10^(-1) mod 251 = 226 (since 10*226 = 2260 = 9*251 + 1)
        const a = toLimbs(10, 4, 2);
        const w = await calculators.inv.calculate({ a, p });
        const out = w.array("main.out");
        assert.equal(fromLimbs(out, 4), 226n);
    });
});

describe_circuit("BigIsEqual", {
    eq: { path: "arithmetic/bigint.circom", template: "BigIsEqual", params: [2] },
}, (calculators) => {
    it("returns 1 for equal values", async () => {
        const w = await calculators.eq.calculate({ a: [5, 10], b: [5, 10] });
        assert.equal(w.value("main.out"), 1n);
    });

    it("returns 0 for unequal values", async () => {
        const w = await calculators.eq.calculate({ a: [5, 10], b: [5, 11] });
        assert.equal(w.value("main.out"), 0n);
    });

    it("returns 0 when only low limb differs", async () => {
        const w = await calculators.eq.calculate({ a: [4, 10], b: [5, 10] });
        assert.equal(w.value("main.out"), 0n);
    });
});
