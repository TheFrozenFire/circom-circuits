import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// Bipartite graph: 3 left nodes, 3 right nodes, 5 edges
// L0-R0, L0-R1, L1-R1, L1-R2, L2-R2

describe_circuit("Graph BipartiteMatching", {
    matching: {
        path: "graph/matching.circom",
        template: "Graph_BipartiteMatching",
        params: [3, 3, 5, 3],
    },
}, (calculators) => {
    const leftNode =  [0, 0, 1, 1, 2];
    const rightNode = [0, 1, 1, 2, 2];

    it("accepts perfect matching with size 3", async () => {
        // Matching: L0-R0, L1-R1, L2-R2 (edges 0, 2, 4)
        // Cover: all right nodes
        const w = await calculators.matching.calculate({
            leftNode,
            rightNode,
            matchMask: [1, 0, 1, 0, 1],
            coverLeft: [0, 0, 0],
            coverRight: [1, 1, 1],
        });
        assert.equal(w.value("main.matchingSize"), 3n);
    });

    it("accepts alternative matching with left cover", async () => {
        // Matching: L0-R0, L1-R1, L2-R2 (edges 0, 2, 4)
        // Cover: all left nodes
        const w = await calculators.matching.calculate({
            leftNode,
            rightNode,
            matchMask: [1, 0, 1, 0, 1],
            coverLeft: [1, 1, 1],
            coverRight: [0, 0, 0],
        });
        assert.equal(w.value("main.matchingSize"), 3n);
    });

    it("rejects invalid matching (shared left endpoint)", async () => {
        try {
            // matchMask=[1,1,0,0,1]: L0 incident to edges 0 AND 1 → count=2
            await calculators.matching.calculate({
                leftNode,
                rightNode,
                matchMask: [1, 1, 0, 0, 1],
                coverLeft: [1, 1, 1],
                coverRight: [0, 0, 0],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects incomplete cover (edge L0-R1 uncovered)", async () => {
        try {
            // coverRight=[1,0,1]: edge L0-R1 has coverLeft[0]=0, coverRight[1]=0
            await calculators.matching.calculate({
                leftNode,
                rightNode,
                matchMask: [1, 0, 1, 0, 1],
                coverLeft: [0, 0, 0],
                coverRight: [1, 0, 1],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects König mismatch (matching=2, cover=3)", async () => {
        try {
            // Only 2 matching edges but 3 cover nodes → mismatch
            await calculators.matching.calculate({
                leftNode,
                rightNode,
                matchMask: [1, 0, 1, 0, 0],
                coverLeft: [1, 1, 1],
                coverRight: [0, 0, 0],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});
