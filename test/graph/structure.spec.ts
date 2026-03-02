import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// Test graph (4 nodes, 4 edges):
//   0 → 1 → 3
//   0 → 2 → 3
// Sinks: [3]
// Valid topological levels: [0, 1, 1, 2]

describe_circuit("Graph Structure", {
    validEdges: { path: "graph/structure.circom", template: "Graph_ValidEdges", params: [4, 4, 3] },
    dag: { path: "graph/structure.circom", template: "Graph_DAG", params: [4, 4, 3] },
    sinkCheck: { path: "graph/structure.circom", template: "Graph_SinkCheck", params: [4, 4, 1] },
    wellFormed: { path: "graph/structure.circom", template: "Graph_WellFormedDAG", params: [4, 4, 1, 3] },
}, (calculators) => {
    const edges = [[0, 1], [0, 2], [1, 3], [2, 3]];
    const levels = [0, 1, 1, 2];

    describe("Graph_ValidEdges", () => {
        it("accepts valid edges", async () => {
            await calculators.validEdges.calculate({ edges });
        });

        it("rejects out-of-range node", async () => {
            try {
                await calculators.validEdges.calculate({ edges: [[0, 1], [0, 5], [1, 3], [2, 3]] });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });

        it("rejects self-loop", async () => {
            try {
                await calculators.validEdges.calculate({ edges: [[0, 1], [2, 2], [1, 3], [2, 3]] });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });

    describe("Graph_DAG", () => {
        it("accepts valid topological ordering", async () => {
            await calculators.dag.calculate({ edges, levels });
        });

        it("accepts alternative valid ordering", async () => {
            // levels [0, 2, 1, 3] also valid: 0<2, 0<1, 2<3, 1<3
            await calculators.dag.calculate({ edges, levels: [0, 2, 1, 3] });
        });

        it("rejects invalid ordering (equal levels on edge)", async () => {
            try {
                // levels [0, 1, 1, 1] fails: edge (1,3) has 1 < 1 = false
                await calculators.dag.calculate({ edges, levels: [0, 1, 1, 1] });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });

        it("rejects backward edge (cycle certificate)", async () => {
            try {
                // levels [1, 0, 2, 3] fails: edge (0,1) has 1 < 0 = false
                await calculators.dag.calculate({ edges, levels: [1, 0, 2, 3] });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });

    describe("Graph_SinkCheck", () => {
        it("accepts valid sink", async () => {
            await calculators.sinkCheck.calculate({ edges, sinks: [3] });
        });

        it("rejects non-sink node", async () => {
            try {
                // Node 0 has outgoing edges
                await calculators.sinkCheck.calculate({ edges, sinks: [0] });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });

    describe("Graph_WellFormedDAG", () => {
        it("accepts well-formed DAG", async () => {
            await calculators.wellFormed.calculate({ edges, levels, sinks: [3] });
        });

        it("rejects when any sub-check fails", async () => {
            try {
                // Self-loop edge
                await calculators.wellFormed.calculate({
                    edges: [[0, 0], [0, 2], [1, 3], [2, 3]],
                    levels,
                    sinks: [3],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });
});
