import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

describe_circuit("Ordered", {
    asc4: { path: "collections/ordered.circom", template: "Ordered", params: [4, 8, 1] },
    desc4: { path: "collections/ordered.circom", template: "Ordered", params: [4, 8, 0] },
    asc2: { path: "collections/ordered.circom", template: "Ordered", params: [2, 8, 1] },
}, (calculators) => {
    it("accepts ascending order", async () => {
        await calculators.asc4.calculate({ in: [1, 3, 5, 7] });
    });

    it("accepts descending order", async () => {
        await calculators.desc4.calculate({ in: [7, 5, 3, 1] });
    });

    it("accepts two elements ascending", async () => {
        await calculators.asc2.calculate({ in: [3, 5] });
    });

    it("rejects equal consecutive values (ascending)", async () => {
        try {
            await calculators.asc4.calculate({ in: [1, 3, 3, 7] });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects wrong direction (descending as ascending)", async () => {
        try {
            await calculators.asc4.calculate({ in: [7, 5, 3, 1] });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects equal consecutive values (descending)", async () => {
        try {
            await calculators.desc4.calculate({ in: [7, 5, 5, 1] });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("accepts consecutive integers ascending", async () => {
        await calculators.asc4.calculate({ in: [0, 1, 2, 3] });
    });
});
