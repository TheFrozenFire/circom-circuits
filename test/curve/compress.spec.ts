import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

const BASE8_X = 5299619240641551281634865583518297030282874472190772894086521144482721001553n;
const BASE8_Y = 16950150798460657717958625567821834550301663161624707787222815936182638968203n;

describe_circuit("BabyCompress", {
    compress: { path: "curve/compress.circom", template: "BabyCompress" },
}, (calculators) => {
    it("compresses BASE8 with correct y bits and sign", async () => {
        const w = await calculators.compress.calculate({ in: [BASE8_X, BASE8_Y] });
        const bits = w.array("main.out");

        // Reconstruct y from bits 0-253
        let y = 0n;
        for (let i = 0; i < 254; i++) {
            y += bits[i] * (1n << BigInt(i));
        }
        assert.equal(y, BASE8_Y);

        // Padding bit
        assert.equal(bits[254], 0n);

        // Sign bit = LSB of x
        assert.equal(bits[255], BASE8_X % 2n);
    });

    it("compresses the identity point", async () => {
        const w = await calculators.compress.calculate({ in: [0, 1] });
        const bits = w.array("main.out");

        // y = 1 → first bit is 1, rest are 0
        assert.equal(bits[0], 1n);
        for (let i = 1; i < 254; i++) {
            assert.equal(bits[i], 0n);
        }

        // Padding and sign (x = 0, sign = 0)
        assert.equal(bits[254], 0n);
        assert.equal(bits[255], 0n);
    });
});

describe_circuit("BabyMultiCompress", {
    multi: { path: "curve/compress.circom", template: "BabyMultiCompress", params: [2] },
}, (calculators) => {
    it("compresses two points into concatenated output", async () => {
        const w = await calculators.multi.calculate({
            in: [[BASE8_X, BASE8_Y], [0, 1]],
        });
        const bits = w.array("main.out");
        assert.equal(bits.length, 512);

        // First 256 bits: BASE8 compressed
        let y1 = 0n;
        for (let i = 0; i < 254; i++) {
            y1 += bits[i] * (1n << BigInt(i));
        }
        assert.equal(y1, BASE8_Y);
        assert.equal(bits[254], 0n);
        assert.equal(bits[255], BASE8_X % 2n);

        // Second 256 bits: identity compressed
        let y2 = 0n;
        for (let i = 0; i < 254; i++) {
            y2 += bits[256 + i] * (1n << BigInt(i));
        }
        assert.equal(y2, 1n);
        assert.equal(bits[256 + 254], 0n);
        assert.equal(bits[256 + 255], 0n);
    });
});
