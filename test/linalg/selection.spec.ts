import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

describe_circuit("Max", {
    max4: { path: "linalg/selection.circom", template: "Max", params: [4, 16] },
    max1: { path: "linalg/selection.circom", template: "Max", params: [1, 16] },
    max3: { path: "linalg/selection.circom", template: "Max", params: [3, 16] },
}, (calculators) => {
    it("finds max and its index", async () => {
        const w = await calculators.max4.calculate({ in: [3, 7, 2, 5] });
        assert.equal(w.value("main.out"), 7n);
        assert.equal(w.value("main.index"), 1n);
    });

    it("works with single element", async () => {
        const w = await calculators.max1.calculate({ in: [42] });
        assert.equal(w.value("main.out"), 42n);
        assert.equal(w.value("main.index"), 0n);
    });

    it("handles all-equal values", async () => {
        const w = await calculators.max3.calculate({ in: [10, 10, 10] });
        assert.equal(w.value("main.out"), 10n);
    });
});

describe_circuit("ArgMax", {
    am3: { path: "linalg/selection.circom", template: "ArgMax", params: [3, 16] },
}, (calculators) => {
    it("returns index of max", async () => {
        const w = await calculators.am3.calculate({ in: [3, 7, 2] });
        assert.equal(w.value("main.index"), 1n);
    });

    it("returns first index when max is at position 0", async () => {
        const w = await calculators.am3.calculate({ in: [100, 1, 50] });
        assert.equal(w.value("main.index"), 0n);
    });
});
