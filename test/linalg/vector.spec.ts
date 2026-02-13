import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

describe_circuit("VectorAdd", {
    add: { path: "linalg/vector.circom", template: "VectorAdd", params: [3] },
}, (calculators) => {
    it("adds two vectors element-wise", async () => {
        const w = await calculators.add.calculate({ a: [1, 2, 3], b: [4, 5, 6] });
        const out = w.array("main.out");
        assert.deepEqual(out, [5n, 7n, 9n]);
    });

    it("adds with zero vector", async () => {
        const w = await calculators.add.calculate({ a: [10, 20, 30], b: [0, 0, 0] });
        const out = w.array("main.out");
        assert.deepEqual(out, [10n, 20n, 30n]);
    });
});

describe_circuit("VectorSub", {
    sub: { path: "linalg/vector.circom", template: "VectorSub", params: [3] },
}, (calculators) => {
    it("subtracts two vectors element-wise", async () => {
        const w = await calculators.sub.calculate({ a: [10, 20, 30], b: [1, 2, 3] });
        const out = w.array("main.out");
        assert.deepEqual(out, [9n, 18n, 27n]);
    });
});

describe_circuit("ScalarVectorMul", {
    mul: { path: "linalg/vector.circom", template: "ScalarVectorMul", params: [3] },
}, (calculators) => {
    it("multiplies vector by scalar", async () => {
        const w = await calculators.mul.calculate({ scalar: 3, v: [1, 2, 3] });
        const out = w.array("main.out");
        assert.deepEqual(out, [3n, 6n, 9n]);
    });

    it("multiplies by zero", async () => {
        const w = await calculators.mul.calculate({ scalar: 0, v: [5, 10, 15] });
        const out = w.array("main.out");
        assert.deepEqual(out, [0n, 0n, 0n]);
    });
});

describe_circuit("DotProduct", {
    dot: { path: "linalg/vector.circom", template: "DotProduct", params: [3] },
}, (calculators) => {
    it("computes dot product", async () => {
        // [1,2,3]·[4,5,6] = 4+10+18 = 32
        const w = await calculators.dot.calculate({ a: [1, 2, 3], b: [4, 5, 6] });
        assert.equal(w.value("main.out"), 32n);
    });

    it("dot product with zero vector is zero", async () => {
        const w = await calculators.dot.calculate({ a: [1, 2, 3], b: [0, 0, 0] });
        assert.equal(w.value("main.out"), 0n);
    });
});

describe_circuit("VectorNormSquared", {
    norm: { path: "linalg/vector.circom", template: "VectorNormSquared", params: [3] },
}, (calculators) => {
    it("computes squared norm", async () => {
        // ||[3,4,0]||² = 9+16+0 = 25
        const w = await calculators.norm.calculate({ v: [3, 4, 0] });
        assert.equal(w.value("main.out"), 25n);
    });

    it("zero vector has zero norm", async () => {
        const w = await calculators.norm.calculate({ v: [0, 0, 0] });
        assert.equal(w.value("main.out"), 0n);
    });
});

describe_circuit("VectorIsEqual", {
    eq: { path: "linalg/vector.circom", template: "VectorIsEqual", params: [3] },
}, (calculators) => {
    it("returns 1 for equal vectors", async () => {
        const w = await calculators.eq.calculate({ a: [1, 2, 3], b: [1, 2, 3] });
        assert.equal(w.value("main.out"), 1n);
    });

    it("returns 0 for different vectors", async () => {
        const w = await calculators.eq.calculate({ a: [1, 2, 3], b: [1, 2, 4] });
        assert.equal(w.value("main.out"), 0n);
    });
});
