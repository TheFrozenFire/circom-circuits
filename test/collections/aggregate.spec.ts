import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

describe_circuit("CalculateTotal", {
    total4: { path: "collections/aggregate.circom", template: "CalculateTotal", params: [4] },
    total1: { path: "collections/aggregate.circom", template: "CalculateTotal", params: [1] },
}, (calculators) => {
    it("sums known values", async () => {
        const w = await calculators.total4.calculate({ in: [10, 20, 30, 40] });
        assert.equal(w.value("main.out"), 100n);
    });

    it("sums zeros", async () => {
        const w = await calculators.total4.calculate({ in: [0, 0, 0, 0] });
        assert.equal(w.value("main.out"), 0n);
    });

    it("single element passthrough", async () => {
        const w = await calculators.total1.calculate({ in: [42] });
        assert.equal(w.value("main.out"), 42n);
    });

    it("handles large field values", async () => {
        const a = 2n ** 200n;
        const b = 2n ** 200n;
        const w = await calculators.total4.calculate({ in: [a, b, 0, 0] });
        assert.equal(w.value("main.out"), a + b);
    });
});

describe_circuit("CalculateProduct", {
    product4: { path: "collections/aggregate.circom", template: "CalculateProduct", params: [4] },
    product1: { path: "collections/aggregate.circom", template: "CalculateProduct", params: [1] },
}, (calculators) => {
    it("multiplies known values", async () => {
        const w = await calculators.product4.calculate({ in: [2, 3, 4, 5] });
        assert.equal(w.value("main.out"), 120n);
    });

    it("product with zero yields zero", async () => {
        const w = await calculators.product4.calculate({ in: [100, 200, 0, 300] });
        assert.equal(w.value("main.out"), 0n);
    });

    it("product of ones is one", async () => {
        const w = await calculators.product4.calculate({ in: [1, 1, 1, 1] });
        assert.equal(w.value("main.out"), 1n);
    });

    it("single element passthrough", async () => {
        const w = await calculators.product1.calculate({ in: [42] });
        assert.equal(w.value("main.out"), 42n);
    });
});
