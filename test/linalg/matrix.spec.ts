import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

describe_circuit("MatrixAdd", {
    add: { path: "linalg/matrix.circom", template: "MatrixAdd", params: [2, 2] },
}, (calculators) => {
    it("adds two matrices element-wise", async () => {
        const w = await calculators.add.calculate({
            A: [[1, 2], [3, 4]],
            B: [[5, 6], [7, 8]],
        });
        assert.equal(w.value("main.out[0][0]"), 6n);
        assert.equal(w.value("main.out[0][1]"), 8n);
        assert.equal(w.value("main.out[1][0]"), 10n);
        assert.equal(w.value("main.out[1][1]"), 12n);
    });
});

describe_circuit("MatrixSub", {
    sub: { path: "linalg/matrix.circom", template: "MatrixSub", params: [2, 2] },
}, (calculators) => {
    it("subtracts two matrices element-wise", async () => {
        const w = await calculators.sub.calculate({
            A: [[10, 20], [30, 40]],
            B: [[1, 2], [3, 4]],
        });
        assert.equal(w.value("main.out[0][0]"), 9n);
        assert.equal(w.value("main.out[0][1]"), 18n);
        assert.equal(w.value("main.out[1][0]"), 27n);
        assert.equal(w.value("main.out[1][1]"), 36n);
    });
});

describe_circuit("ScalarMatrixMul", {
    mul: { path: "linalg/matrix.circom", template: "ScalarMatrixMul", params: [2, 2] },
}, (calculators) => {
    it("multiplies matrix by scalar", async () => {
        const w = await calculators.mul.calculate({
            scalar: 2,
            M: [[1, 2], [3, 4]],
        });
        assert.equal(w.value("main.out[0][0]"), 2n);
        assert.equal(w.value("main.out[0][1]"), 4n);
        assert.equal(w.value("main.out[1][0]"), 6n);
        assert.equal(w.value("main.out[1][1]"), 8n);
    });
});

describe_circuit("MatrixVectorMul", {
    mul: { path: "linalg/matrix.circom", template: "MatrixVectorMul", params: [2, 2] },
}, (calculators) => {
    it("identity matrix times vector equals vector", async () => {
        const w = await calculators.mul.calculate({
            M: [[1, 0], [0, 1]],
            v: [5, 6],
        });
        assert.equal(w.value("main.out[0]"), 5n);
        assert.equal(w.value("main.out[1]"), 6n);
    });

    it("multiplies non-trivial matrix by vector", async () => {
        // [[1,2],[3,4]] * [1,1] = [3, 7]
        const w = await calculators.mul.calculate({
            M: [[1, 2], [3, 4]],
            v: [1, 1],
        });
        assert.equal(w.value("main.out[0]"), 3n);
        assert.equal(w.value("main.out[1]"), 7n);
    });
});

describe_circuit("MatrixMul", {
    mul: { path: "linalg/matrix.circom", template: "MatrixMul", params: [2, 2, 2] },
}, (calculators) => {
    it("multiplies two 2x2 matrices", async () => {
        // [[1,2],[3,4]] × [[5,6],[7,8]] = [[19,22],[43,50]]
        const w = await calculators.mul.calculate({
            A: [[1, 2], [3, 4]],
            B: [[5, 6], [7, 8]],
        });
        assert.equal(w.value("main.out[0][0]"), 19n);
        assert.equal(w.value("main.out[0][1]"), 22n);
        assert.equal(w.value("main.out[1][0]"), 43n);
        assert.equal(w.value("main.out[1][1]"), 50n);
    });

    it("identity × matrix = matrix", async () => {
        const w = await calculators.mul.calculate({
            A: [[1, 0], [0, 1]],
            B: [[7, 8], [9, 10]],
        });
        assert.equal(w.value("main.out[0][0]"), 7n);
        assert.equal(w.value("main.out[0][1]"), 8n);
        assert.equal(w.value("main.out[1][0]"), 9n);
        assert.equal(w.value("main.out[1][1]"), 10n);
    });
});

describe_circuit("MatrixTranspose", {
    t: { path: "linalg/matrix.circom", template: "MatrixTranspose", params: [2, 3] },
}, (calculators) => {
    it("transposes a 2x3 matrix to 3x2", async () => {
        // [[1,2,3],[4,5,6]] → [[1,4],[2,5],[3,6]]
        const w = await calculators.t.calculate({
            M: [[1, 2, 3], [4, 5, 6]],
        });
        assert.equal(w.value("main.out[0][0]"), 1n);
        assert.equal(w.value("main.out[0][1]"), 4n);
        assert.equal(w.value("main.out[1][0]"), 2n);
        assert.equal(w.value("main.out[1][1]"), 5n);
        assert.equal(w.value("main.out[2][0]"), 3n);
        assert.equal(w.value("main.out[2][1]"), 6n);
    });
});

describe_circuit("MatrixIsEqual", {
    eq: { path: "linalg/matrix.circom", template: "MatrixIsEqual", params: [2, 2] },
}, (calculators) => {
    it("returns 1 for equal matrices", async () => {
        const w = await calculators.eq.calculate({
            A: [[1, 2], [3, 4]],
            B: [[1, 2], [3, 4]],
        });
        assert.equal(w.value("main.out"), 1n);
    });

    it("returns 0 for different matrices", async () => {
        const w = await calculators.eq.calculate({
            A: [[1, 2], [3, 4]],
            B: [[1, 2], [3, 5]],
        });
        assert.equal(w.value("main.out"), 0n);
    });
});
