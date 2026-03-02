import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// Test graph (4 nodes, 5 edges, undirected):
//   0 -- 1  (edge 0)
//   0 -- 2  (edge 1)
//   1 -- 3  (edge 2)
//   2 -- 3  (edge 3)
//   0 -- 3  (edge 4)

describe_circuit("Graph SpanningTree & MST", {
    st: {
        path: "graph/spanning_tree.circom",
        template: "Graph_SpanningTree",
        params: [4, 5, 3],
    },
    mst: {
        path: "graph/spanning_tree.circom",
        template: "Graph_MST",
        params: [4, 5, 8],
    },
}, (calculators) => {
    const edges = [[0, 1], [0, 2], [1, 3], [2, 3], [0, 3]];

    describe("Graph_SpanningTree", () => {
        it("accepts valid spanning tree rooted at 0", async () => {
            // Tree: 0-1, 0-2, 1-3 (edges 0, 1, 2)
            await calculators.st.calculate({
                edges,
                root: 0,
                parent: [0, 0, 0, 1],
                depth: [0, 1, 1, 2],
            });
        });

        it("accepts alternative tree rooted at 0", async () => {
            // Tree: 0-1, 0-2, 0-3 (star, edges 0, 1, 4)
            await calculators.st.calculate({
                edges,
                root: 0,
                parent: [0, 0, 0, 0],
                depth: [0, 1, 1, 1],
            });
        });

        it("accepts tree rooted at node 2", async () => {
            // Tree: 2-0, 0-1, 2-3 (edges 1, 0, 3)
            await calculators.st.calculate({
                edges,
                root: 2,
                parent: [2, 0, 2, 2],
                depth: [1, 2, 0, 1],
            });
        });

        it("rejects depth inconsistency", async () => {
            try {
                // parent[3]=1, so depth[3] should be depth[1]+1=2, not 1
                await calculators.st.calculate({
                    edges,
                    root: 0,
                    parent: [0, 0, 0, 1],
                    depth: [0, 1, 1, 1],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });

        it("rejects non-existent parent edge", async () => {
            try {
                // parent[3]=2 means edge (3,2) or (2,3) must exist — edge 3 = (2,3) exists.
                // parent[1]=3 means edge (1,3) or (3,1) must exist — edge 2 = (1,3) exists.
                // parent[2]=3 means edge (2,3) or (3,2) — edge 3 = (2,3) exists.
                // So let's use parent[1]=2: edge (1,2) or (2,1) — neither exists!
                await calculators.st.calculate({
                    edges,
                    root: 0,
                    parent: [0, 2, 0, 1],
                    depth: [0, 2, 1, 3],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });

    describe("Graph_MST", () => {
        // Weights: [1, 4, 2, 5, 3]
        // MST by Kruskal: (0,1)=1, (1,3)=2, (0,3)=3? No, 0-3 already connected.
        //   Add (0,1)=1, add (1,3)=2, skip (0,3)=3 (cycle), add (0,2)=4. Total=7.
        // MST tree: {edge 0, edge 2, edge 1} = {(0,1), (1,3), (0,2)}
        // Tree structure: root=0, parent=[0,0,0,1], depth=[0,1,1,2]
        const weights = [1, 4, 2, 5, 3];

        it("verifies MST with total weight 7", async () => {
            const w = await calculators.mst.calculate({
                edges,
                weights,
                root: 0,
                parent: [0, 0, 0, 1],
                depth: [0, 1, 1, 2],
                treeEdgeMask: [1, 1, 1, 0, 0],  // edges 0,1,2 in tree
                // Non-tree edges: edge 3 (2,3)=5, edge 4 (0,3)=3
                // Tree path for edge 3 (2-0-1-3): max weight = max(4,1,2) = 4
                // Tree path for edge 4 (0-1-3): max weight = max(1,2) = 2
                maxPathWeight: [0, 0, 0, 4, 2],
            });
            assert.equal(w.value("main.totalWeight"), 7n);
        });

        it("rejects suboptimal tree (cut property violated)", async () => {
            try {
                // Non-MST tree: {(0,1)=1, (0,2)=4, (2,3)=5}, total=10
                // Non-tree edge (1,3)=2, tree path 1-0-2-3, max=max(1,4,5)=5
                // Cut property: 2 >= 5? NO → rejected
                await calculators.mst.calculate({
                    edges,
                    weights,
                    root: 0,
                    parent: [0, 0, 0, 2],
                    depth: [0, 1, 1, 2],
                    treeEdgeMask: [1, 1, 0, 1, 0],  // edges 0,1,3
                    maxPathWeight: [0, 0, 5, 0, 2],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });

        it("rejects wrong tree edge count", async () => {
            try {
                // Only 2 tree edges instead of nNodes-1=3
                await calculators.mst.calculate({
                    edges,
                    weights,
                    root: 0,
                    parent: [0, 0, 0, 1],
                    depth: [0, 1, 1, 2],
                    treeEdgeMask: [1, 0, 1, 0, 0],  // only 2 edges
                    maxPathWeight: [0, 4, 0, 4, 2],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });
});
