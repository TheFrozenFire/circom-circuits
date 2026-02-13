import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// BN128 field modulus
const p = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

// scale_bits=8 → S=256, tolerance_bits=4 → tolerance < 16

describe_circuit("OrthogonalCheck", {
    check: { path: "linalg/orthogonal.circom", template: "OrthogonalCheck", params: [2, 8, 4] },
}, (calculators) => {
    it("accepts identity matrix (scaled by S=256)", async () => {
        await calculators.check.calculate({
            Q: [[256, 0], [0, 256]],
        });
    });

    it("accepts 90-degree rotation matrix", async () => {
        // R = [[0, -1], [1, 0]] scaled by 256 → [[0, p-256], [256, 0]]
        await calculators.check.calculate({
            Q: [[0, p - 256n], [256, 0]],
        });
    });

    it("rejects non-orthogonal matrix", async () => {
        // [[256, 256], [0, 256]] is upper triangular, not orthogonal
        try {
            await calculators.check.calculate({
                Q: [[256, 256], [0, 256]],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});

describe_circuit("OrthogonalTransform", {
    transform: { path: "linalg/orthogonal.circom", template: "OrthogonalTransform", params: [2, 8, 4] },
}, (calculators) => {
    it("identity transform preserves vector", async () => {
        const w = await calculators.transform.calculate({
            Q: [[256, 0], [0, 256]],
            x: [100, 200],
        });
        assert.equal(w.value("main.y[0]"), 100n);
        assert.equal(w.value("main.y[1]"), 200n);
    });

    it("90-degree rotation of [256, 0] gives [0, 256]", async () => {
        // R = [[0, p-256], [256, 0]]
        // y = R * x (fixed-point rescale)
        // row 0: 0*256 + (p-256)*0 = 0 → rescaled 0
        // row 1: 256*256 + 0*0 = 65536 → rescaled 65536/256 = 256
        const w = await calculators.transform.calculate({
            Q: [[0, p - 256n], [256, 0]],
            x: [256, 0],
        });
        assert.equal(w.value("main.y[0]"), 0n);
        assert.equal(w.value("main.y[1]"), 256n);
    });
});
