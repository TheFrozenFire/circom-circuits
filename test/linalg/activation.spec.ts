import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

const p = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

describe_circuit("ReLU", {
    relu: { path: "linalg/activation.circom", template: "ReLU", params: [16] },
}, (calculators) => {
    it("passes through positive values", async () => {
        const w = await calculators.relu.calculate({ in: 500 });
        assert.equal(w.value("main.out"), 500n);
    });

    it("returns zero for zero input", async () => {
        const w = await calculators.relu.calculate({ in: 0 });
        assert.equal(w.value("main.out"), 0n);
    });

    it("returns zero for negative values", async () => {
        // -100 in the field is p - 100
        const w = await calculators.relu.calculate({ in: p - 100n });
        assert.equal(w.value("main.out"), 0n);
    });
});

describe_circuit("ReLUVector", {
    rv: { path: "linalg/activation.circom", template: "ReLUVector", params: [4, 16] },
}, (calculators) => {
    it("applies ReLU element-wise", async () => {
        const w = await calculators.rv.calculate({ in: [100, p - 50n, 200, 0] });
        const out = w.array("main.out");
        assert.deepEqual(out, [100n, 0n, 200n, 0n]);
    });
});
