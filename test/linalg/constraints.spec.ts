import { assert } from "chai";
import { compile_and_count, CircuitDef } from "../helpers.js";

function circuit(template: string, file: string, params: number[]): CircuitDef {
    return { path: `linalg/${file}`, template, params };
}

describe("@slow Linalg constraint scaling", function () {
    this.timeout(0);

    // --- Vector operations (n = 128, 384, 768) ---

    describe("VectorAdd O(n)", () => {
        it("has constant per-element cost", async () => {
            const c128 = await compile_and_count(circuit("VectorAdd", "vector.circom", [128]));
            const c384 = await compile_and_count(circuit("VectorAdd", "vector.circom", [384]));
            const c768 = await compile_and_count(circuit("VectorAdd", "vector.circom", [768]));
            const perUnit1 = (c384 - c128) / (384 - 128);
            const perUnit2 = (c768 - c384) / (768 - 384);
            assert.equal(perUnit1, perUnit2, "VectorAdd per-element cost should be constant");
        });
    });

    describe("VectorSub O(n)", () => {
        it("has constant per-element cost", async () => {
            const c128 = await compile_and_count(circuit("VectorSub", "vector.circom", [128]));
            const c384 = await compile_and_count(circuit("VectorSub", "vector.circom", [384]));
            const c768 = await compile_and_count(circuit("VectorSub", "vector.circom", [768]));
            const perUnit1 = (c384 - c128) / (384 - 128);
            const perUnit2 = (c768 - c384) / (768 - 384);
            assert.equal(perUnit1, perUnit2, "VectorSub per-element cost should be constant");
        });
    });

    describe("ScalarVectorMul O(n)", () => {
        it("has constant per-element cost", async () => {
            const c128 = await compile_and_count(circuit("ScalarVectorMul", "vector.circom", [128]));
            const c384 = await compile_and_count(circuit("ScalarVectorMul", "vector.circom", [384]));
            const c768 = await compile_and_count(circuit("ScalarVectorMul", "vector.circom", [768]));
            const perUnit1 = (c384 - c128) / (384 - 128);
            const perUnit2 = (c768 - c384) / (768 - 384);
            assert.equal(perUnit1, perUnit2, "ScalarVectorMul per-element cost should be constant");
        });
    });

    describe("DotProduct O(n)", () => {
        it("has constant per-element cost", async () => {
            const c128 = await compile_and_count(circuit("DotProduct", "vector.circom", [128]));
            const c384 = await compile_and_count(circuit("DotProduct", "vector.circom", [384]));
            const c768 = await compile_and_count(circuit("DotProduct", "vector.circom", [768]));
            const perUnit1 = (c384 - c128) / (384 - 128);
            const perUnit2 = (c768 - c384) / (768 - 384);
            assert.equal(perUnit1, perUnit2, "DotProduct per-element cost should be constant");
        });
    });

    describe("VectorNormSquared O(n)", () => {
        it("has constant per-element cost", async () => {
            const c128 = await compile_and_count(circuit("VectorNormSquared", "vector.circom", [128]));
            const c384 = await compile_and_count(circuit("VectorNormSquared", "vector.circom", [384]));
            const c768 = await compile_and_count(circuit("VectorNormSquared", "vector.circom", [768]));
            const perUnit1 = (c384 - c128) / (384 - 128);
            const perUnit2 = (c768 - c384) / (768 - 384);
            assert.equal(perUnit1, perUnit2, "VectorNormSquared per-element cost should be constant");
        });
    });

    describe("VectorIsEqual O(n)", () => {
        it("has constant per-element cost", async () => {
            const c128 = await compile_and_count(circuit("VectorIsEqual", "vector.circom", [128]));
            const c384 = await compile_and_count(circuit("VectorIsEqual", "vector.circom", [384]));
            const c768 = await compile_and_count(circuit("VectorIsEqual", "vector.circom", [768]));
            const perUnit1 = (c384 - c128) / (384 - 128);
            const perUnit2 = (c768 - c384) / (768 - 384);
            assert.equal(perUnit1, perUnit2, "VectorIsEqual per-element cost should be constant");
        });
    });

    describe("HadamardProduct O(n)", () => {
        it("has constant per-element cost", async () => {
            const c128 = await compile_and_count(circuit("HadamardProduct", "vector.circom", [128]));
            const c384 = await compile_and_count(circuit("HadamardProduct", "vector.circom", [384]));
            const c768 = await compile_and_count(circuit("HadamardProduct", "vector.circom", [768]));
            const perUnit1 = (c384 - c128) / (384 - 128);
            const perUnit2 = (c768 - c384) / (768 - 384);
            assert.equal(perUnit1, perUnit2, "HadamardProduct per-element cost should be constant");
        });
    });

    describe("EuclideanDistanceSquared O(n)", () => {
        it("has constant per-element cost", async () => {
            const c128 = await compile_and_count(circuit("EuclideanDistanceSquared", "vector.circom", [128]));
            const c384 = await compile_and_count(circuit("EuclideanDistanceSquared", "vector.circom", [384]));
            const c768 = await compile_and_count(circuit("EuclideanDistanceSquared", "vector.circom", [768]));
            const perUnit1 = (c384 - c128) / (384 - 128);
            const perUnit2 = (c768 - c384) / (768 - 384);
            assert.equal(perUnit1, perUnit2, "EuclideanDistanceSquared per-element cost should be constant");
        });
    });

    // --- Multi-vector operations ---

    describe("WeightedSum O(k*n)", () => {
        it("has constant per-vector cost (varying k, fixed n=128)", async () => {
            const c4 = await compile_and_count(circuit("WeightedSum", "vector.circom", [128, 4]));
            const c8 = await compile_and_count(circuit("WeightedSum", "vector.circom", [128, 8]));
            const c16 = await compile_and_count(circuit("WeightedSum", "vector.circom", [128, 16]));
            const perUnit1 = (c8 - c4) / (8 - 4);
            const perUnit2 = (c16 - c8) / (16 - 8);
            assert.equal(perUnit1, perUnit2, "WeightedSum per-vector cost should be constant");
        });
    });

    describe("VectorMean O(n)", () => {
        it("has constant per-element cost (fixed k=4, varying n)", async () => {
            const c128 = await compile_and_count(circuit("VectorMean", "vector.circom", [128, 4]));
            const c384 = await compile_and_count(circuit("VectorMean", "vector.circom", [384, 4]));
            const c768 = await compile_and_count(circuit("VectorMean", "vector.circom", [768, 4]));
            const perUnit1 = (c384 - c128) / (384 - 128);
            const perUnit2 = (c768 - c384) / (768 - 384);
            assert.equal(perUnit1, perUnit2, "VectorMean per-element cost should be constant");
        });
    });

    // --- Matrix operations ---

    describe("MatrixAdd O(m*n)", () => {
        it("has constant per-element cost (fixed m=64, varying n)", async () => {
            const c32 = await compile_and_count(circuit("MatrixAdd", "matrix.circom", [64, 32]));
            const c64 = await compile_and_count(circuit("MatrixAdd", "matrix.circom", [64, 64]));
            const c128 = await compile_and_count(circuit("MatrixAdd", "matrix.circom", [64, 128]));
            const perUnit1 = (c64 - c32) / (64 - 32);
            const perUnit2 = (c128 - c64) / (128 - 64);
            assert.equal(perUnit1, perUnit2, "MatrixAdd per-column cost should be constant");
        });
    });

    describe("MatrixSub O(m*n)", () => {
        it("has constant per-element cost (fixed m=64, varying n)", async () => {
            const c32 = await compile_and_count(circuit("MatrixSub", "matrix.circom", [64, 32]));
            const c64 = await compile_and_count(circuit("MatrixSub", "matrix.circom", [64, 64]));
            const c128 = await compile_and_count(circuit("MatrixSub", "matrix.circom", [64, 128]));
            const perUnit1 = (c64 - c32) / (64 - 32);
            const perUnit2 = (c128 - c64) / (128 - 64);
            assert.equal(perUnit1, perUnit2, "MatrixSub per-column cost should be constant");
        });
    });

    describe("MatrixTranspose O(m*n)", () => {
        it("has constant per-element cost (fixed m=64, varying n)", async () => {
            const c32 = await compile_and_count(circuit("MatrixTranspose", "matrix.circom", [64, 32]));
            const c64 = await compile_and_count(circuit("MatrixTranspose", "matrix.circom", [64, 64]));
            const c128 = await compile_and_count(circuit("MatrixTranspose", "matrix.circom", [64, 128]));
            const perUnit1 = (c64 - c32) / (64 - 32);
            const perUnit2 = (c128 - c64) / (128 - 64);
            assert.equal(perUnit1, perUnit2, "MatrixTranspose per-column cost should be constant");
        });
    });

    describe("ScalarMatrixMul O(m*n)", () => {
        it("has constant per-element cost", async () => {
            const c32 = await compile_and_count(circuit("ScalarMatrixMul", "matrix.circom", [32, 32]));
            const c64 = await compile_and_count(circuit("ScalarMatrixMul", "matrix.circom", [64, 64]));
            const c128 = await compile_and_count(circuit("ScalarMatrixMul", "matrix.circom", [128, 128]));
            const perUnit1 = (c64 - c32) / (64 * 64 - 32 * 32);
            const perUnit2 = (c128 - c64) / (128 * 128 - 64 * 64);
            assert.equal(perUnit1, perUnit2, "ScalarMatrixMul per-element cost should be constant");
        });
    });

    describe("MatrixVectorMul O(m*n)", () => {
        it("has constant per-column cost (fixed m=64, varying n)", async () => {
            const c32 = await compile_and_count(circuit("MatrixVectorMul", "matrix.circom", [64, 32]));
            const c64 = await compile_and_count(circuit("MatrixVectorMul", "matrix.circom", [64, 64]));
            const c128 = await compile_and_count(circuit("MatrixVectorMul", "matrix.circom", [64, 128]));
            const perUnit1 = (c64 - c32) / (64 - 32);
            const perUnit2 = (c128 - c64) / (128 - 64);
            assert.equal(perUnit1, perUnit2, "MatrixVectorMul per-column cost should be constant");
        });
    });

    describe("MatrixMul O(m*n*p)", () => {
        it("has constant per-inner-dim cost (fixed m=p=32, varying n)", async () => {
            const c16 = await compile_and_count(circuit("MatrixMul", "matrix.circom", [32, 16, 32]));
            const c32 = await compile_and_count(circuit("MatrixMul", "matrix.circom", [32, 32, 32]));
            const c64 = await compile_and_count(circuit("MatrixMul", "matrix.circom", [32, 64, 32]));
            const perUnit1 = (c32 - c16) / (32 - 16);
            const perUnit2 = (c64 - c32) / (64 - 32);
            assert.equal(perUnit1, perUnit2, "MatrixMul per-inner-dim cost should be constant");
        });
    });

    describe("MatrixIsEqual O(m*n)", () => {
        it("has constant per-element cost", async () => {
            const c32 = await compile_and_count(circuit("MatrixIsEqual", "matrix.circom", [32, 32]));
            const c64 = await compile_and_count(circuit("MatrixIsEqual", "matrix.circom", [64, 64]));
            const c128 = await compile_and_count(circuit("MatrixIsEqual", "matrix.circom", [128, 128]));
            const perUnit1 = (c64 - c32) / (64 * 64 - 32 * 32);
            const perUnit2 = (c128 - c64) / (128 * 128 - 64 * 64);
            assert.equal(perUnit1, perUnit2, "MatrixIsEqual per-element cost should be constant");
        });
    });

    // --- Fixed-point operations ---

    describe("FixedPointMul O(s)", () => {
        it("has constant per-bit cost", async () => {
            const c8 = await compile_and_count(circuit("FixedPointMul", "fixedpoint.circom", [8]));
            const c16 = await compile_and_count(circuit("FixedPointMul", "fixedpoint.circom", [16]));
            const c32 = await compile_and_count(circuit("FixedPointMul", "fixedpoint.circom", [32]));
            const perUnit1 = (c16 - c8) / (16 - 8);
            const perUnit2 = (c32 - c16) / (32 - 16);
            assert.equal(perUnit1, perUnit2, "FixedPointMul per-bit cost should be constant");
        });
    });

    describe("FixedPointDotProduct O(n)", () => {
        it("has constant per-element cost (s=8 fixed)", async () => {
            const c128 = await compile_and_count(circuit("FixedPointDotProduct", "fixedpoint.circom", [128, 8]));
            const c384 = await compile_and_count(circuit("FixedPointDotProduct", "fixedpoint.circom", [384, 8]));
            const c768 = await compile_and_count(circuit("FixedPointDotProduct", "fixedpoint.circom", [768, 8]));
            const perUnit1 = (c384 - c128) / (384 - 128);
            const perUnit2 = (c768 - c384) / (768 - 384);
            assert.equal(perUnit1, perUnit2, "FixedPointDotProduct per-element cost should be constant");
        });
    });

    describe("FixedPointMatrixVectorMul O(m*n)", () => {
        it("has constant per-row cost (fixed n=64, s=8, varying m)", async () => {
            const c32 = await compile_and_count(circuit("FixedPointMatrixVectorMul", "fixedpoint.circom", [32, 64, 8]));
            const c64 = await compile_and_count(circuit("FixedPointMatrixVectorMul", "fixedpoint.circom", [64, 64, 8]));
            const c128 = await compile_and_count(circuit("FixedPointMatrixVectorMul", "fixedpoint.circom", [128, 64, 8]));
            const perUnit1 = (c64 - c32) / (64 - 32);
            const perUnit2 = (c128 - c64) / (128 - 64);
            assert.equal(perUnit1, perUnit2, "FixedPointMatrixVectorMul per-row cost should be constant");
        });
    });

    describe("FixedPointDiv O(s+m)", () => {
        it("has constant per-bit cost (max_bits=16 fixed)", async () => {
            const c8 = await compile_and_count(circuit("FixedPointDiv", "fixedpoint.circom", [8, 16]));
            const c16 = await compile_and_count(circuit("FixedPointDiv", "fixedpoint.circom", [16, 16]));
            const c32 = await compile_and_count(circuit("FixedPointDiv", "fixedpoint.circom", [32, 16]));
            const perUnit1 = (c16 - c8) / (16 - 8);
            const perUnit2 = (c32 - c16) / (32 - 16);
            assert.equal(perUnit1, perUnit2, "FixedPointDiv per-bit cost should be constant");
        });
    });

    // --- Selection operations ---

    describe("Max O(n)", () => {
        it("has constant per-element cost (bits=16 fixed)", async () => {
            const c64 = await compile_and_count(circuit("Max", "selection.circom", [64, 16]));
            const c128 = await compile_and_count(circuit("Max", "selection.circom", [128, 16]));
            const c256 = await compile_and_count(circuit("Max", "selection.circom", [256, 16]));
            const perUnit1 = (c128 - c64) / (128 - 64);
            const perUnit2 = (c256 - c128) / (256 - 128);
            assert.equal(perUnit1, perUnit2, "Max per-element cost should be constant");
        });
    });

    // --- Activation operations ---

    describe("ReLU O(max_bits)", () => {
        it("has constant per-bit cost", async () => {
            const c8 = await compile_and_count(circuit("ReLU", "activation.circom", [8]));
            const c16 = await compile_and_count(circuit("ReLU", "activation.circom", [16]));
            const c32 = await compile_and_count(circuit("ReLU", "activation.circom", [32]));
            const perUnit1 = (c16 - c8) / (16 - 8);
            const perUnit2 = (c32 - c16) / (32 - 16);
            assert.equal(perUnit1, perUnit2, "ReLU per-bit cost should be constant");
        });
    });

    describe("ReLUVector O(n)", () => {
        it("has constant per-element cost (max_bits=16 fixed)", async () => {
            const c128 = await compile_and_count(circuit("ReLUVector", "activation.circom", [128, 16]));
            const c384 = await compile_and_count(circuit("ReLUVector", "activation.circom", [384, 16]));
            const c768 = await compile_and_count(circuit("ReLUVector", "activation.circom", [768, 16]));
            const perUnit1 = (c384 - c128) / (384 - 128);
            const perUnit2 = (c768 - c384) / (768 - 384);
            assert.equal(perUnit1, perUnit2, "ReLUVector per-element cost should be constant");
        });
    });

    // --- Similarity operations ---

    describe("CosineSimilarityCheck O(n)", () => {
        it("has constant per-element cost (bits=64 fixed)", async () => {
            const c128 = await compile_and_count(circuit("CosineSimilarityCheck", "similarity.circom", [128, 64]));
            const c384 = await compile_and_count(circuit("CosineSimilarityCheck", "similarity.circom", [384, 64]));
            const c768 = await compile_and_count(circuit("CosineSimilarityCheck", "similarity.circom", [768, 64]));
            const perUnit1 = (c384 - c128) / (384 - 128);
            const perUnit2 = (c768 - c384) / (768 - 384);
            assert.equal(perUnit1, perUnit2, "CosineSimilarityCheck per-element cost should be constant");
        });
    });

    describe("NearestNeighborCheck O(k)", () => {
        it("has constant per-candidate cost (n=64, bits=64 fixed)", async () => {
            const c8 = await compile_and_count(circuit("NearestNeighborCheck", "similarity.circom", [64, 8, 64]));
            const c16 = await compile_and_count(circuit("NearestNeighborCheck", "similarity.circom", [64, 16, 64]));
            const c32 = await compile_and_count(circuit("NearestNeighborCheck", "similarity.circom", [64, 32, 64]));
            const perUnit1 = (c16 - c8) / (16 - 8);
            const perUnit2 = (c32 - c16) / (32 - 16);
            assert.equal(perUnit1, perUnit2, "NearestNeighborCheck per-candidate cost should be constant");
        });
    });
});
