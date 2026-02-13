import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

describe_circuit("CosineSimilarityCheck", {
    cos: { path: "linalg/similarity.circom", template: "CosineSimilarityCheck", params: [3, 32] },
}, (calculators) => {
    it("passes for identical vectors (cos=1.0, threshold_sq=0.5)", async () => {
        // Identical vectors: cos = 1.0. 1.0^2 >= 0.5 → pass
        // threshold_sq is a raw value representing t^2 as a fraction
        // We use the cross-multiply form: dotAB^2 >= threshold_sq * normA * normB
        // For [3,4,0]·[3,4,0]: dot=25, normA=25, normB=25
        // lhs = 625, rhs = threshold_sq * 625
        // Need 625 >= threshold_sq * 625 → threshold_sq <= 1
        // Use threshold_sq = 1 (maximum, exact equality passes since 625 >= 625)
        await calculators.cos.calculate({
            a: [3, 4, 0],
            b: [3, 4, 0],
            threshold_sq: 1,
        });
    });

    it("passes for similar vectors above threshold", async () => {
        // a=[10,0,0], b=[10,1,0]: dot=100, normA=100, normB=101
        // lhs=10000, rhs=threshold_sq*10100
        // For threshold_sq=0 (any non-negative angle passes): 10000 >= 0 → pass
        await calculators.cos.calculate({
            a: [10, 0, 0],
            b: [10, 1, 0],
            threshold_sq: 0,
        });
    });

    it("fails for orthogonal vectors with positive threshold", async () => {
        // a=[1,0,0], b=[0,1,0]: dot=0, normA=1, normB=1
        // lhs=0, rhs=threshold_sq*1. Need 0 >= threshold_sq → only works if threshold_sq=0
        try {
            await calculators.cos.calculate({
                a: [1, 0, 0],
                b: [0, 1, 0],
                threshold_sq: 1,
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});

describe_circuit("NearestNeighborCheck", {
    nn: { path: "linalg/similarity.circom", template: "NearestNeighborCheck", params: [2, 3, 32] },
}, (calculators) => {
    it("passes for correct nearest neighbor index", async () => {
        // query=[0,0], candidates=[[1,1],[10,10],[5,5]]
        // dist: [2, 200, 50] → nearest is index 0
        await calculators.nn.calculate({
            query: [0, 0],
            candidates: [[1, 1], [10, 10], [5, 5]],
            claimedIdx: 0,
        });
    });

    it("fails for wrong nearest neighbor index", async () => {
        // query=[0,0], candidates=[[1,1],[10,10],[5,5]]
        // dist: [2, 200, 50] → nearest is 0, claiming 1 should fail
        try {
            await calculators.nn.calculate({
                query: [0, 0],
                candidates: [[1, 1], [10, 10], [5, 5]],
                claimedIdx: 1,
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});
