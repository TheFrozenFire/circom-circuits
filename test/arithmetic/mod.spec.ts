import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

describe_circuit("ModSum", {
    mod8: { path: "arithmetic/mod.circom", template: "ModSum", params: [8] },
}, (calculators) => {
    it("sums without overflow", async () => {
        const w = await calculators.mod8.calculate({ a: 100, b: 50 });
        assert.equal(w.value("main.out"), 150n);
    });

    it("wraps on overflow", async () => {
        // 200 + 100 = 300, 300 % 256 = 44
        const w = await calculators.mod8.calculate({ a: 200, b: 100 });
        assert.equal(w.value("main.out"), 44n);
    });

    it("handles zero", async () => {
        const w = await calculators.mod8.calculate({ a: 0, b: 0 });
        assert.equal(w.value("main.out"), 0n);
    });

    it("max values wrap", async () => {
        // 255 + 255 = 510, 510 % 256 = 254
        const w = await calculators.mod8.calculate({ a: 255, b: 255 });
        assert.equal(w.value("main.out"), 254n);
    });
});

describe_circuit("ModSub", {
    mod8: { path: "arithmetic/mod.circom", template: "ModSub", params: [8] },
}, (calculators) => {
    it("subtracts without underflow", async () => {
        const w = await calculators.mod8.calculate({ a: 200, b: 50 });
        assert.equal(w.value("main.out"), 150n);
    });

    it("wraps on underflow", async () => {
        // 50 - 200 = -150, (-150) mod 256 = 106
        const w = await calculators.mod8.calculate({ a: 50, b: 200 });
        assert.equal(w.value("main.out"), 106n);
    });

    it("a - 0 = a", async () => {
        const w = await calculators.mod8.calculate({ a: 42, b: 0 });
        assert.equal(w.value("main.out"), 42n);
    });

    it("a - a = 0", async () => {
        const w = await calculators.mod8.calculate({ a: 123, b: 123 });
        assert.equal(w.value("main.out"), 0n);
    });
});

describe_circuit("ModSumThree", {
    mod8: { path: "arithmetic/mod.circom", template: "ModSumThree", params: [8] },
}, (calculators) => {
    it("sums three values with wrap", async () => {
        // 100 + 100 + 100 = 300, 300 % 256 = 44
        const w = await calculators.mod8.calculate({ a: 100, b: 100, c: 100 });
        assert.equal(w.value("main.out"), 44n);
    });

    it("sums without wrap", async () => {
        const w = await calculators.mod8.calculate({ a: 10, b: 20, c: 30 });
        assert.equal(w.value("main.out"), 60n);
    });
});

describe_circuit("ModSubThree", {
    mod8: { path: "arithmetic/mod.circom", template: "ModSubThree", params: [8] },
}, (calculators) => {
    it("subtracts two values from first", async () => {
        const w = await calculators.mod8.calculate({ a: 200, b: 50, c: 30 });
        assert.equal(w.value("main.out"), 120n);
    });

    it("wraps on underflow", async () => {
        // 10 - 100 - 100 = -190, (-190) mod 256 = 66
        const w = await calculators.mod8.calculate({ a: 10, b: 100, c: 100 });
        assert.equal(w.value("main.out"), 66n);
    });
});

describe_circuit("ModSumFour", {
    mod8: { path: "arithmetic/mod.circom", template: "ModSumFour", params: [8] },
}, (calculators) => {
    it("sums four values with wrap", async () => {
        // 100 + 100 + 100 + 100 = 400, 400 % 256 = 144
        const w = await calculators.mod8.calculate({ a: 100, b: 100, c: 100, d: 100 });
        assert.equal(w.value("main.out"), 144n);
    });

    it("sums without wrap", async () => {
        const w = await calculators.mod8.calculate({ a: 10, b: 20, c: 30, d: 40 });
        assert.equal(w.value("main.out"), 100n);
    });
});

describe_circuit("ModProd", {
    mod8: { path: "arithmetic/mod.circom", template: "ModProd", params: [8] },
}, (calculators) => {
    it("multiplies without overflow", async () => {
        const w = await calculators.mod8.calculate({ a: 5, b: 10 });
        assert.equal(w.value("main.out"), 50n);
    });

    it("wraps on overflow", async () => {
        // 20 * 20 = 400, 400 % 256 = 144
        const w = await calculators.mod8.calculate({ a: 20, b: 20 });
        assert.equal(w.value("main.out"), 144n);
    });

    it("multiply by zero", async () => {
        const w = await calculators.mod8.calculate({ a: 255, b: 0 });
        assert.equal(w.value("main.out"), 0n);
    });

    it("multiply by one", async () => {
        const w = await calculators.mod8.calculate({ a: 200, b: 1 });
        assert.equal(w.value("main.out"), 200n);
    });
});

describe_circuit("Split", {
    split: { path: "arithmetic/mod.circom", template: "Split", params: [4, 4] },
}, (calculators) => {
    it("splits into low and high nibbles", async () => {
        // 0xAB = 171 → small = 0xB = 11, big = 0xA = 10
        const w = await calculators.split.calculate({ in: 0xAB });
        assert.equal(w.value("main.small"), 11n);
        assert.equal(w.value("main.big"), 10n);
    });

    it("zero splits into zeros", async () => {
        const w = await calculators.split.calculate({ in: 0 });
        assert.equal(w.value("main.small"), 0n);
        assert.equal(w.value("main.big"), 0n);
    });

    it("value fits in low part", async () => {
        const w = await calculators.split.calculate({ in: 7 });
        assert.equal(w.value("main.small"), 7n);
        assert.equal(w.value("main.big"), 0n);
    });

    it("reconstructs correctly: in = small + big * 2^n", async () => {
        for (const val of [0, 1, 15, 16, 100, 200, 255]) {
            const w = await calculators.split.calculate({ in: val });
            const small = w.value("main.small");
            const big = w.value("main.big");
            assert.equal(small + big * 16n, BigInt(val));
        }
    });
});

describe_circuit("SplitThree", {
    split: { path: "arithmetic/mod.circom", template: "SplitThree", params: [4, 4, 4] },
}, (calculators) => {
    it("splits into three nibbles", async () => {
        // 0xABC = 2748 → small=0xC=12, medium=0xB=11, big=0xA=10
        const w = await calculators.split.calculate({ in: 0xABC });
        assert.equal(w.value("main.small"), 12n);
        assert.equal(w.value("main.medium"), 11n);
        assert.equal(w.value("main.big"), 10n);
    });

    it("reconstructs correctly: in = small + medium * 2^n + big * 2^(n+m)", async () => {
        for (const val of [0, 1, 255, 256, 1000, 4095]) {
            const w = await calculators.split.calculate({ in: val });
            const small = w.value("main.small");
            const medium = w.value("main.medium");
            const big = w.value("main.big");
            assert.equal(small + medium * 16n + big * 256n, BigInt(val));
        }
    });
});
