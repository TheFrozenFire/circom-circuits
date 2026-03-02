import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// Test graph (4 nodes, 5 edges):
//   0 →(w=10) 1 →(w=20) 3
//   0 →(w=5)  2 →(w=8)  3
//   1 →(w=3)  2
//
// Shortest path 0→3: 0→2→3 with cost 13
// dist = [0, 10, 5, 13]

function bellmanFord(
    nNodes: number,
    edges: number[][],
    costs: number[],
    source: number,
): number[] {
    const dist = new Array(nNodes).fill(Infinity);
    dist[source] = 0;
    for (let round = 0; round < nNodes - 1; round++) {
        for (let e = 0; e < edges.length; e++) {
            const [u, v] = edges[e];
            if (dist[u] + costs[e] < dist[v]) {
                dist[v] = dist[u] + costs[e];
            }
        }
    }
    return dist;
}

describe_circuit("Graph ShortestPath", {
    sp: {
        path: "graph/shortest_path.circom",
        template: "Graph_ShortestPath",
        params: [4, 5, 2, 8, 0],
    },
}, (calculators) => {
    const edges = [[0, 1], [0, 2], [1, 3], [2, 3], [1, 2]];
    const edgeProps = [10, 5, 20, 8, 3];

    it("verifies shortest path 0→2→3 (cost 13)", async () => {
        const dist = bellmanFord(4, edges, edgeProps, 0);
        assert.deepEqual(dist, [0, 10, 5, 13]);

        const w = await calculators.sp.calculate({
            edges,
            edgeProps,
            source: 0,
            target: 3,
            dist,
            path: [0, 2, 3],
            edgeIndices: [1, 3],  // edge 1 = (0,2), edge 3 = (2,3)
        });
        assert.equal(w.value("main.shortestDist"), 13n);
    });

    it("verifies shortest path 1→2→3 from source 1 (cost 11)", async () => {
        // From source 1: dist = [200, 0, 3, 11] (200 = unreachable sentinel)
        const dist = [200, 0, 3, 11];

        const w = await calculators.sp.calculate({
            edges,
            edgeProps,
            source: 1,
            target: 3,
            dist,
            path: [1, 2, 3],
            edgeIndices: [4, 3],  // edge 4 = (1,2), edge 3 = (2,3)
        });
        assert.equal(w.value("main.shortestDist"), 11n);
    });

    it("rejects wrong distance labels (violates dual feasibility)", async () => {
        try {
            await calculators.sp.calculate({
                edges,
                edgeProps,
                source: 0,
                target: 3,
                dist: [0, 10, 5, 20],  // dist[3]=20, but actual shortest is 13
                path: [0, 2, 3],
                edgeIndices: [1, 3],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects wrong path (cost doesn't match dist[target])", async () => {
        try {
            await calculators.sp.calculate({
                edges,
                edgeProps,
                source: 0,
                target: 3,
                dist: [0, 10, 5, 13],
                path: [0, 1, 3],  // cost 10+20=30, but dist[3]=13
                edgeIndices: [0, 2],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});
