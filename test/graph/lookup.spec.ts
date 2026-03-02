import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

describe_circuit("Lookup", {
    lookup: { path: "graph/lookup.circom", template: "Lookup", params: [4] },
    lookupRow: { path: "graph/lookup.circom", template: "LookupRow", params: [4, 3] },
}, (calculators) => {
    describe("Lookup(4)", () => {
        it("selects index 0", async () => {
            const w = await calculators.lookup.calculate({ in: [10, 20, 30, 40], sel: 0 });
            assert.equal(w.value("main.out"), 10n);
        });

        it("selects index 2", async () => {
            const w = await calculators.lookup.calculate({ in: [10, 20, 30, 40], sel: 2 });
            assert.equal(w.value("main.out"), 30n);
        });

        it("selects last index", async () => {
            const w = await calculators.lookup.calculate({ in: [10, 20, 30, 40], sel: 3 });
            assert.equal(w.value("main.out"), 40n);
        });
    });

    describe("LookupRow(4, 3)", () => {
        const props = [
            [100, 101, 102],
            [200, 201, 202],
            [300, 301, 302],
            [400, 401, 402],
        ];

        it("selects row 0", async () => {
            const w = await calculators.lookupRow.calculate({ props, sel: 0 });
            assert.equal(w.value("main.out[0]"), 100n);
            assert.equal(w.value("main.out[1]"), 101n);
            assert.equal(w.value("main.out[2]"), 102n);
        });

        it("selects row 2", async () => {
            const w = await calculators.lookupRow.calculate({ props, sel: 2 });
            assert.equal(w.value("main.out[0]"), 300n);
            assert.equal(w.value("main.out[1]"), 301n);
            assert.equal(w.value("main.out[2]"), 302n);
        });

        it("selects last row", async () => {
            const w = await calculators.lookupRow.calculate({ props, sel: 3 });
            assert.equal(w.value("main.out[0]"), 400n);
            assert.equal(w.value("main.out[1]"), 401n);
            assert.equal(w.value("main.out[2]"), 402n);
        });
    });
});
