import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

describe_circuit("IndexSelector", {
    sel3x2x1: { path: "collections/selector.circom", template: "IndexSelector", params: [3, 2, 1] },
    sel3x2x2: { path: "collections/selector.circom", template: "IndexSelector", params: [3, 2, 2] },
}, (calculators) => {
    const table = [
        [5, 100],
        [10, 200],
        [15, 300],
    ];

    it("selects a single row by index", async () => {
        const w = await calculators.sel3x2x1.calculate({ in: table, index: [10] });
        assert.deepEqual(w.array("main.out[0]"), [10n, 200n]);
    });

    it("selects multiple rows", async () => {
        const w = await calculators.sel3x2x2.calculate({ in: table, index: [5, 15] });
        assert.deepEqual(w.array("main.out[0]"), [5n, 100n]);
        assert.deepEqual(w.array("main.out[1]"), [15n, 300n]);
    });

    it("returns zeros for missing index", async () => {
        const w = await calculators.sel3x2x1.calculate({ in: table, index: [99] });
        assert.deepEqual(w.array("main.out[0]"), [0n, 0n]);
    });

    it("selects first row", async () => {
        const w = await calculators.sel3x2x1.calculate({ in: table, index: [5] });
        assert.deepEqual(w.array("main.out[0]"), [5n, 100n]);
    });

    it("selects last row", async () => {
        const w = await calculators.sel3x2x1.calculate({ in: table, index: [15] });
        assert.deepEqual(w.array("main.out[0]"), [15n, 300n]);
    });
});
