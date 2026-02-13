import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

describe_circuit("InRange", {
    rc: { path: "linalg/fixedpoint.circom", template: "InRange", params: [8] },
}, (calculators) => {
    it("accepts 0", async () => {
        await calculators.rc.calculate({ in: 0 });
    });

    it("accepts 255 (max for 8 bits)", async () => {
        await calculators.rc.calculate({ in: 255 });
    });

    it("rejects 256 (overflow)", async () => {
        try {
            await calculators.rc.calculate({ in: 256 });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});

describe_circuit("ApproxEqual", {
    ae: { path: "linalg/fixedpoint.circom", template: "ApproxEqual", params: [4] },
}, (calculators) => {
    // tolerance_bits=4 → |a - b| must be < 2^4 = 16

    it("accepts equal values", async () => {
        await calculators.ae.calculate({ a: 100, b: 100 });
    });

    it("accepts values within tolerance", async () => {
        // |110 - 100| = 10 < 16
        await calculators.ae.calculate({ a: 110, b: 100 });
    });

    it("accepts values at tolerance boundary (diff=15)", async () => {
        await calculators.ae.calculate({ a: 115, b: 100 });
    });

    it("rejects values outside tolerance (diff=16)", async () => {
        try {
            await calculators.ae.calculate({ a: 116, b: 100 });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});

describe_circuit("FixedPointMul", {
    fpm: { path: "linalg/fixedpoint.circom", template: "FixedPointMul", params: [8] },
}, (calculators) => {
    // scale_bits=8, S=256. Values represent real/S.
    // 2.0 → 512, 3.0 → 768
    // out = floor(512 * 768 / 256) = floor(393216 / 256) = 1536 (= 6.0 × 256)

    it("multiplies 2.0 × 3.0 = 6.0 in fixed-point", async () => {
        const w = await calculators.fpm.calculate({ a: 512, b: 768 });
        assert.equal(w.value("main.out"), 1536n);
    });

    it("multiplies 1.0 × 1.0 = 1.0", async () => {
        // 256 * 256 / 256 = 256
        const w = await calculators.fpm.calculate({ a: 256, b: 256 });
        assert.equal(w.value("main.out"), 256n);
    });

    it("multiplies 0.5 × 4.0 = 2.0", async () => {
        // 0.5→128, 4.0→1024. floor(128*1024/256) = floor(131072/256) = 512
        const w = await calculators.fpm.calculate({ a: 128, b: 1024 });
        assert.equal(w.value("main.out"), 512n);
    });

    it("multiply by zero gives zero", async () => {
        const w = await calculators.fpm.calculate({ a: 0, b: 512 });
        assert.equal(w.value("main.out"), 0n);
    });
});

describe_circuit("FixedPointDotProduct", {
    fpdp: { path: "linalg/fixedpoint.circom", template: "FixedPointDotProduct", params: [3, 8] },
}, (calculators) => {
    // scale_bits=8, S=256
    // [1.0, 2.0, 3.0] → [256, 512, 768]
    // [4.0, 5.0, 6.0] → [1024, 1280, 1536]
    // raw dot = 256*1024 + 512*1280 + 768*1536
    //         = 262144 + 655360 + 1179648 = 2097152
    // rescaled = floor(2097152 / 256) = 8192 (= 32.0 × 256)

    it("computes fixed-point dot product", async () => {
        const w = await calculators.fpdp.calculate({
            a: [256, 512, 768],
            b: [1024, 1280, 1536],
        });
        assert.equal(w.value("main.out"), 8192n);
    });
});

describe_circuit("FixedPointMatrixVectorMul", {
    fpmv: { path: "linalg/fixedpoint.circom", template: "FixedPointMatrixVectorMul", params: [2, 2, 8] },
}, (calculators) => {
    // scale_bits=8, S=256
    // Identity matrix in fixed-point: [[256,0],[0,256]]
    // Vector [100, 200]
    // row 0: 256*100 + 0*200 = 25600. rescaled = 100
    // row 1: 0*100 + 256*200 = 51200. rescaled = 200

    it("identity matrix preserves vector", async () => {
        const w = await calculators.fpmv.calculate({
            M: [[256, 0], [0, 256]],
            v: [100, 200],
        });
        assert.equal(w.value("main.out[0]"), 100n);
        assert.equal(w.value("main.out[1]"), 200n);
    });

    it("2× scaling matrix doubles vector", async () => {
        // [[512,0],[0,512]] × [100, 200] → rescaled [200, 400]
        const w = await calculators.fpmv.calculate({
            M: [[512, 0], [0, 512]],
            v: [100, 200],
        });
        assert.equal(w.value("main.out[0]"), 200n);
        assert.equal(w.value("main.out[1]"), 400n);
    });
});

describe_circuit("FixedPointDiv", {
    fpd: { path: "linalg/fixedpoint.circom", template: "FixedPointDiv", params: [8, 16] },
}, (calculators) => {
    // scale_bits=8, S=256, max_bits=16

    it("divides 6.0 / 2.0 = 3.0", async () => {
        // 6.0→1536, 2.0→512. floor(1536 * 256 / 512) = floor(393216/512) = 768 (3.0)
        const w = await calculators.fpd.calculate({ a: 1536, b: 512 });
        assert.equal(w.value("main.out"), 768n);
    });

    it("divides 1.0 / 1.0 = 1.0", async () => {
        // 256 * 256 / 256 = 256
        const w = await calculators.fpd.calculate({ a: 256, b: 256 });
        assert.equal(w.value("main.out"), 256n);
    });

    it("divides 1.0 / 4.0 = 0.25", async () => {
        // 256 * 256 / 1024 = 65536 / 1024 = 64 (0.25)
        const w = await calculators.fpd.calculate({ a: 256, b: 1024 });
        assert.equal(w.value("main.out"), 64n);
    });
});
