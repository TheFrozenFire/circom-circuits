import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

describe_circuit("Num2BitsLE", {
    num2bits8: { path: "packing/bitify.circom", template: "Num2BitsLE", params: [8] },
    num2bits1: { path: "packing/bitify.circom", template: "Num2BitsLE", params: [1] },
}, (calculators) => {
    it("decomposes zero", async () => {
        const w = await calculators.num2bits8.calculate({ in: 0 });
        assert.deepEqual(w.array("main.out"), [0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n]);
    });

    it("decomposes known values in little-endian order", async () => {
        // 5 = 0b00000101 → [1, 0, 1, 0, 0, 0, 0, 0] LE
        const w = await calculators.num2bits8.calculate({ in: 5 });
        assert.deepEqual(w.array("main.out"), [1n, 0n, 1n, 0n, 0n, 0n, 0n, 0n]);

        // 255 = 0b11111111
        const w2 = await calculators.num2bits8.calculate({ in: 255 });
        assert.deepEqual(w2.array("main.out"), [1n, 1n, 1n, 1n, 1n, 1n, 1n, 1n]);

        // 128 = 0b10000000 → [0, 0, 0, 0, 0, 0, 0, 1] LE
        const w3 = await calculators.num2bits8.calculate({ in: 128 });
        assert.deepEqual(w3.array("main.out"), [0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n]);
    });

    it("single-bit decomposition", async () => {
        const w0 = await calculators.num2bits1.calculate({ in: 0 });
        assert.deepEqual(w0.array("main.out"), [0n]);

        const w1 = await calculators.num2bits1.calculate({ in: 1 });
        assert.deepEqual(w1.array("main.out"), [1n]);
    });

    it("rejects values that overflow n bits", async () => {
        try {
            await calculators.num2bits8.calculate({ in: 256 });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});

describe_circuit("Bits2NumLE", {
    bits2num8: { path: "packing/bitify.circom", template: "Bits2NumLE", params: [8] },
}, (calculators) => {
    it("reconstructs zero from zero bits", async () => {
        const w = await calculators.bits2num8.calculate({ in: [0, 0, 0, 0, 0, 0, 0, 0] });
        assert.equal(w.value("main.out"), 0n);
    });

    it("reconstructs known values from LE bits", async () => {
        // [1, 0, 1, 0, 0, 0, 0, 0] LE → 5
        const w = await calculators.bits2num8.calculate({ in: [1, 0, 1, 0, 0, 0, 0, 0] });
        assert.equal(w.value("main.out"), 5n);

        // all ones → 255
        const w2 = await calculators.bits2num8.calculate({ in: [1, 1, 1, 1, 1, 1, 1, 1] });
        assert.equal(w2.value("main.out"), 255n);
    });
});

// Circomlib-compatible aliases (functionally identical to LE variants)
describe_circuit("Num2Bits (alias)", {
    n2b: { path: "packing/bitify.circom", template: "Num2Bits", params: [8] },
}, (calculators) => {
    it("decomposes like Num2BitsLE", async () => {
        const w = await calculators.n2b.calculate({ in: 42 });
        // 42 = 0b00101010 → [0,1,0,1,0,1,0,0] LE
        assert.deepEqual(w.array("main.out"), [0n, 1n, 0n, 1n, 0n, 1n, 0n, 0n]);
    });

    it("rejects overflow", async () => {
        try {
            await calculators.n2b.calculate({ in: 256 });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});

describe_circuit("Bits2Num (alias)", {
    b2n: { path: "packing/bitify.circom", template: "Bits2Num", params: [8] },
}, (calculators) => {
    it("reconstructs like Bits2NumLE", async () => {
        // [0,1,0,1,0,1,0,0] LE → 42
        const w = await calculators.b2n.calculate({ in: [0, 1, 0, 1, 0, 1, 0, 0] });
        assert.equal(w.value("main.out"), 42n);
    });
});

describe_circuit("TruncNumLE", {
    trunc: { path: "packing/bitify.circom", template: "TruncNumLE", params: [8, 4] },
}, (calculators) => {
    it("truncates to lower bits (effectively mod 2^nOut)", async () => {
        // 200 = 0b11001000, lower 4 bits = 0b1000 = 8
        const w = await calculators.trunc.calculate({ in: 200 });
        assert.equal(w.value("main.out"), 8n);
    });

    it("passes through values that fit in nOut bits", async () => {
        // 7 < 16, so truncation is identity
        const w = await calculators.trunc.calculate({ in: 7 });
        assert.equal(w.value("main.out"), 7n);
    });

    it("truncates max value", async () => {
        // 255 = 0b11111111, lower 4 bits = 0b1111 = 15
        const w = await calculators.trunc.calculate({ in: 255 });
        assert.equal(w.value("main.out"), 15n);
    });

    it("rejects values exceeding nIn bits", async () => {
        try {
            await calculators.trunc.calculate({ in: 256 });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});
