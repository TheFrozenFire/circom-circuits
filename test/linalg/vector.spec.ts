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

describe_circuit("HadamardProduct", {
    hp: { path: "linalg/vector.circom", template: "HadamardProduct", params: [3] },
}, (calculators) => {
    it("computes element-wise product", async () => {
        const w = await calculators.hp.calculate({ a: [1, 2, 3], b: [4, 5, 6] });
        const out = w.array("main.out");
        assert.deepEqual(out, [4n, 10n, 18n]);
    });

    it("product with zero vector is zero", async () => {
        const w = await calculators.hp.calculate({ a: [5, 10, 15], b: [0, 0, 0] });
        const out = w.array("main.out");
        assert.deepEqual(out, [0n, 0n, 0n]);
    });

    it("product with ones vector is identity", async () => {
        const w = await calculators.hp.calculate({ a: [7, 8, 9], b: [1, 1, 1] });
        const out = w.array("main.out");
        assert.deepEqual(out, [7n, 8n, 9n]);
    });
});

describe_circuit("EuclideanDistanceSquared", {
    ed: { path: "linalg/vector.circom", template: "EuclideanDistanceSquared", params: [3] },
}, (calculators) => {
    it("identical vectors have zero distance", async () => {
        const w = await calculators.ed.calculate({ a: [5, 10, 15], b: [5, 10, 15] });
        assert.equal(w.value("main.out"), 0n);
    });

    it("computes distance from origin", async () => {
        // |[3,4,0] - [0,0,0]|^2 = 9+16+0 = 25
        const w = await calculators.ed.calculate({ a: [3, 4, 0], b: [0, 0, 0] });
        assert.equal(w.value("main.out"), 25n);
    });

    it("computes distance between two vectors", async () => {
        // |[1,2,3] - [4,5,6]|^2 = 9+9+9 = 27
        const w = await calculators.ed.calculate({ a: [1, 2, 3], b: [4, 5, 6] });
        assert.equal(w.value("main.out"), 27n);
    });
});

describe_circuit("WeightedSum", {
    ws2: { path: "linalg/vector.circom", template: "WeightedSum", params: [3, 2] },
    ws1: { path: "linalg/vector.circom", template: "WeightedSum", params: [3, 1] },
}, (calculators) => {
    it("computes equal-weight sum", async () => {
        // w=[1,1], v=[[1,2,3],[4,5,6]] → [5,7,9]
        const w = await calculators.ws2.calculate({ w: [1, 1], v: [[1, 2, 3], [4, 5, 6]] });
        const out = w.array("main.out");
        assert.deepEqual(out, [5n, 7n, 9n]);
    });

    it("computes weighted combination", async () => {
        // w=[2,3], v=[[1,0,0],[0,1,0]] → [2,3,0]
        const w = await calculators.ws2.calculate({ w: [2, 3], v: [[1, 0, 0], [0, 1, 0]] });
        const out = w.array("main.out");
        assert.deepEqual(out, [2n, 3n, 0n]);
    });

    it("single vector passthrough", async () => {
        const w = await calculators.ws1.calculate({ w: [5], v: [[2, 3, 4]] });
        const out = w.array("main.out");
        assert.deepEqual(out, [10n, 15n, 20n]);
    });
});

describe_circuit("VectorMean", {
    vm: { path: "linalg/vector.circom", template: "VectorMean", params: [2, 2] },
    vm1: { path: "linalg/vector.circom", template: "VectorMean", params: [2, 1] },
}, (calculators) => {
    it("computes mean of two vectors", async () => {
        // [[6,12],[4,8]] → [(6+4)/2, (12+8)/2] = [5, 10]
        const w = await calculators.vm.calculate({ v: [[6, 12], [4, 8]] });
        const out = w.array("main.out");
        assert.deepEqual(out, [5n, 10n]);
    });

    it("single vector returns itself", async () => {
        const w = await calculators.vm1.calculate({ v: [[7, 13]] });
        const out = w.array("main.out");
        assert.deepEqual(out, [7n, 13n]);
    });

    it("truncates (integer division)", async () => {
        // [[5, 3],[4, 2]] → [(5+4)/2, (3+2)/2] = [4, 2] (floor)
        const w = await calculators.vm.calculate({ v: [[5, 3], [4, 2]] });
        const out = w.array("main.out");
        assert.deepEqual(out, [4n, 2n]);
    });
});
