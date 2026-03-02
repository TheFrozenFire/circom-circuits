import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// Test graph (4 nodes, 5 edges):
//   s=0 →(cap=10) 1 →(cap=5) t=3
//   s=0 →(cap=8)  2 →(cap=7) t=3
//   1 →(cap=3) 2
//
// Max flow = 13:
//   flow: 0→1=8, 0→2=5, 1→3=5, 2→3=8, 1→2=3
//   (Verify: source out = 8+5=13, sink in = 5+8=13)
//
// Min cut: S={0,1}, T={2,3}, capacity = cap(1→2) + cap(1→3) = 3+5 = 8... no.
// Let me recalculate:
// Actually max flow is limited by bottleneck. Let me compute properly.
//
// Edges: [0,1]=10, [0,2]=8, [1,3]=5, [2,3]=7, [1,2]=3
// Path 0→1→3: bottleneck=min(10,5)=5, send 5
//   residual: 0→1=5, 0→2=8, 1→3=0, 2→3=7, 1→2=3
// Path 0→2→3: bottleneck=min(8,7)=7, send 7
//   residual: 0→1=5, 0→2=1, 1→3=0, 2→3=0, 1→2=3
// Path 0→1→2→3: can't, 2→3=0
// Path 0→2... can't get anywhere useful
// So max flow = 5+7=12
//
// But wait, 0→1→2→3: residual 0→1=5, 1→2=3, 2→3=0. No.
// Try: send along 0→1=5 (5), then 0→1→2→3: 0→1 has 5 left, 1→2 has 3, 2→3 has 7
//   bottleneck = min(5,3,7) = 3, send 3
//   Now: 0→1 used 8, 0→2 used 0, 1→3 used 5, 2→3 used 3, 1→2 used 3
//   Then 0→2→3: 0→2=8, 2→3=7-3=4. send 4
//   Total: 5+3+4=12
//
// flows: 0→1=8, 0→2=4, 1→3=5, 2→3=7, 1→2=3
// source out: 8+4=12
// Check node 1: in=8, out=5+3=8 ✓
// Check node 2: in=4+3=7, out=7 ✓
// sink in: 5+7=12 ✓
//
// Min cut: S={0}, T={1,2,3}
//   cut edges: 0→1 (cap=10), 0→2 (cap=8), total = 18
// That's not tight. Try S={0,1}, T={2,3}:
//   cut edges: 0→2 (cap=8), 1→3 (cap=5), 1→2 (cap=3), total=16
// Try S={0,1,2}, T={3}:
//   cut edges: 1→3 (cap=5), 2→3 (cap=7), total=12 = max flow ✓

describe_circuit("Graph MaxFlowMinCut", {
    mf: {
        path: "graph/max_flow.circom",
        template: "Graph_MaxFlowMinCut",
        params: [4, 5, 8],
    },
}, (calculators) => {
    const edges = [[0, 1], [0, 2], [1, 3], [2, 3], [1, 2]];
    const capacity = [10, 8, 5, 7, 3];

    it("verifies max flow = 12 with matching min cut", async () => {
        const w = await calculators.mf.calculate({
            edges,
            capacity,
            source: 0,
            target: 3,
            flow: [8, 4, 5, 7, 3],
            cutLabel: [0, 0, 0, 1],  // S={0,1,2}, T={3}
        });
        assert.equal(w.value("main.maxFlow"), 12n);
    });

    it("rejects flow exceeding capacity", async () => {
        try {
            await calculators.mf.calculate({
                edges,
                capacity,
                source: 0,
                target: 3,
                flow: [11, 4, 5, 7, 3],  // flow[0]=11 > cap[0]=10
                cutLabel: [0, 0, 0, 1],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects when flow and cut don't match (not optimal)", async () => {
        try {
            // Suboptimal flow (value=5) with min cut (capacity=12)
            await calculators.mf.calculate({
                edges,
                capacity,
                source: 0,
                target: 3,
                flow: [5, 0, 5, 0, 0],
                cutLabel: [0, 0, 0, 1],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects invalid cut (source not in S)", async () => {
        try {
            await calculators.mf.calculate({
                edges,
                capacity,
                source: 0,
                target: 3,
                flow: [8, 4, 5, 7, 3],
                cutLabel: [1, 0, 0, 1],  // source labeled T-side
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});
