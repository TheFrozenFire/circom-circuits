import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// Test graph (4 nodes, 5 edges):
//   0 →(w=10) 1 →(w=20) 3
//   0 →(w=5)  2 →(w=8)  3
//   1 →(w=3)  2
// Edges: [0,1], [0,2], [1,3], [2,3], [1,2]
// Edge costs: [10, 5, 20, 8, 3]

describe_circuit("Graph Path", {
    verifyPath: { path: "graph/path.circom", template: "Graph_VerifyPath", params: [4, 5, 2] },
    pathCost: { path: "graph/path.circom", template: "Graph_PathCost", params: [4, 5, 1, 2, 0] },
}, (calculators) => {
    const edges = [[0, 1], [0, 2], [1, 3], [2, 3], [1, 2]];
    const edgeProps = [[10], [5], [20], [8], [3]];

    describe("Graph_VerifyPath", () => {
        it("accepts valid path 0→1→3", async () => {
            await calculators.verifyPath.calculate({ edges, path: [0, 1, 3] });
        });

        it("accepts valid path 0→2→3", async () => {
            await calculators.verifyPath.calculate({ edges, path: [0, 2, 3] });
        });

        it("rejects invalid path 0→3→1 (no edge 0→3)", async () => {
            try {
                await calculators.verifyPath.calculate({ edges, path: [0, 3, 1] });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });

        it("rejects path with non-existent edge", async () => {
            try {
                await calculators.verifyPath.calculate({ edges, path: [2, 1, 3] });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });

    describe("Graph_PathCost", () => {
        it("computes cost of path 0→1→3 (edges 0,2 = 10+20=30)", async () => {
            const w = await calculators.pathCost.calculate({
                edges,
                edgeProps,
                path: [0, 1, 3],
                edgeIndices: [0, 2],
            });
            assert.equal(w.value("main.totalCost"), 30n);
        });

        it("computes cost of path 0→2→3 (edges 1,3 = 5+8=13)", async () => {
            const w = await calculators.pathCost.calculate({
                edges,
                edgeProps,
                path: [0, 2, 3],
                edgeIndices: [1, 3],
            });
            assert.equal(w.value("main.totalCost"), 13n);
        });

        it("rejects wrong edge index for path step", async () => {
            try {
                // Edge 1 is (0,2) but path step is 0→1
                await calculators.pathCost.calculate({
                    edges,
                    edgeProps,
                    path: [0, 1, 3],
                    edgeIndices: [1, 2],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });
});
