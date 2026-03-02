import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// Test graph (4 nodes, 5 edges) — K4 minus edge (0,3):
//   0 -- 1
//   |  / |
//   2 -- 3
// Chromatic number = 3

describe_circuit("Graph Coloring", {
    coloring: {
        path: "graph/coloring.circom",
        template: "Graph_Coloring",
        params: [4, 5, 3, 3],
    },
}, (calculators) => {
    const edges = [[0, 1], [0, 2], [1, 2], [1, 3], [2, 3]];

    it("accepts valid 3-coloring [0,1,2,0]", async () => {
        await calculators.coloring.calculate({
            edges,
            colors: [0, 1, 2, 0],
        });
    });

    it("accepts alternative valid coloring [2,0,1,2]", async () => {
        await calculators.coloring.calculate({
            edges,
            colors: [2, 0, 1, 2],
        });
    });

    it("rejects adjacent same color (edge 0-2)", async () => {
        try {
            // colors[0]=0, colors[2]=0 but edge (0,2) exists
            await calculators.coloring.calculate({
                edges,
                colors: [0, 1, 0, 2],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects color out of range", async () => {
        try {
            // color 3 is not in [0, nColors=3)
            await calculators.coloring.calculate({
                edges,
                colors: [0, 1, 3, 2],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});
