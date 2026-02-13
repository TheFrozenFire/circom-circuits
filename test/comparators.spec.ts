import { assert } from "chai";
import { describe_circuit } from "./helpers.js";

describe_circuit("IsZero", {
    iz: { path: "comparators.circom", template: "IsZero" },
}, (calculators) => {
    it("returns 1 for zero input", async () => {
        const w = await calculators.iz.calculate({ in: 0 });
        assert.equal(w.value("main.out"), 1n);
    });

    it("returns 0 for nonzero input", async () => {
        const w = await calculators.iz.calculate({ in: 42 });
        assert.equal(w.value("main.out"), 0n);
    });

    it("returns 0 for large value", async () => {
        const w = await calculators.iz.calculate({ in: 2n ** 200n });
        assert.equal(w.value("main.out"), 0n);
    });
});

describe_circuit("IsEqual", {
    eq: { path: "comparators.circom", template: "IsEqual" },
}, (calculators) => {
    it("returns 1 for equal values", async () => {
        const w = await calculators.eq.calculate({ in: [99, 99] });
        assert.equal(w.value("main.out"), 1n);
    });

    it("returns 0 for unequal values", async () => {
        const w = await calculators.eq.calculate({ in: [1, 2] });
        assert.equal(w.value("main.out"), 0n);
    });

    it("returns 1 for both zero", async () => {
        const w = await calculators.eq.calculate({ in: [0, 0] });
        assert.equal(w.value("main.out"), 1n);
    });
});

describe_circuit("LessThan", {
    lt: { path: "comparators.circom", template: "LessThan", params: [8] },
}, (calculators) => {
    it("returns 1 when a < b", async () => {
        const w = await calculators.lt.calculate({ in: [10, 200] });
        assert.equal(w.value("main.out"), 1n);
    });

    it("returns 0 when a > b", async () => {
        const w = await calculators.lt.calculate({ in: [200, 10] });
        assert.equal(w.value("main.out"), 0n);
    });

    it("returns 0 when a == b", async () => {
        const w = await calculators.lt.calculate({ in: [42, 42] });
        assert.equal(w.value("main.out"), 0n);
    });

    it("handles edge case 0 < 1", async () => {
        const w = await calculators.lt.calculate({ in: [0, 1] });
        assert.equal(w.value("main.out"), 1n);
    });

    it("handles edge case 254 < 255", async () => {
        const w = await calculators.lt.calculate({ in: [254, 255] });
        assert.equal(w.value("main.out"), 1n);
    });
});

describe_circuit("ForceEqualIfEnabled", {
    fe: { path: "comparators.circom", template: "ForceEqualIfEnabled" },
}, (calculators) => {
    it("passes when disabled and values unequal", async () => {
        await calculators.fe.calculate({ enabled: 0, in: [1, 2] });
    });

    it("passes when enabled and values equal", async () => {
        await calculators.fe.calculate({ enabled: 1, in: [42, 42] });
    });

    it("fails when enabled and values unequal", async () => {
        try {
            await calculators.fe.calculate({ enabled: 1, in: [1, 2] });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});
