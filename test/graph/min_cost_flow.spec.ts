import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

const p = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

// Test graph (4 nodes, 5 edges):
//   0→1 cap=10 cost=2
//   0→2 cap=8  cost=1
//   1→3 cap=5  cost=4
//   2→3 cap=7  cost=3
//   1→2 cap=3  cost=1
//
// demand = [-10, 0, 0, 10] → ship 10 units from node 0 to node 3
//
// Optimal flow: 0→1:3, 0→2:7, 1→3:3, 2→3:7, 1→2:0, totalCost = 3*2 + 7*1 + 3*4 + 7*3 + 0 = 6+7+12+21 = 46
//
// Potentials: p=[0, 2, 1, 6]
// Reduced costs: rc[e] = cost[e] + p[src] - p[dst]
//   0→1: 2 + 0 - 2 = 0   (flow=3, 0<flow<cap → rc must be 0 ✓)
//   0→2: 1 + 0 - 1 = 0   (flow=7, 0<flow<cap → rc must be 0 ✓)
//   1→3: 4 + 2 - 6 = 0   (flow=3, 0<flow<cap → rc must be 0 ✓)
//   2→3: 3 + 1 - 6 = -2  (flow=7=cap → rc ≤ 0 ✓)
//   1→2: 1 + 2 - 1 = 2   (flow=0 → rc ≥ 0 ✓)

describe_circuit("Graph MinCostFlow", {
    mcf: {
        path: "graph/min_cost_flow.circom",
        template: "Graph_MinCostFlow",
        params: [4, 5, 8],
    },
}, (calculators) => {
    const edges = [[0, 1], [0, 2], [1, 3], [2, 3], [1, 2]];
    const capacity = [10, 8, 5, 7, 3];
    const cost = [2, 1, 4, 3, 1];
    const demand = [p - 10n, 0, 0, 10];

    it("verifies optimal flow with totalCost=46", async () => {
        const w = await calculators.mcf.calculate({
            edges,
            capacity,
            cost,
            demand,
            flow: [3, 7, 3, 7, 0],
            potential: [0, 2, 1, 6],
            // rc = [0, 0, 0, -2, 2]
            // rcPlus = max(rc, 0), rcMinus = max(-rc, 0)
            rcPlus:  [0, 0, 0, 0, 2],
            rcMinus: [0, 0, 0, 2, 0],
        });
        assert.equal(w.value("main.totalCost"), 46n);
    });

    it("rejects flow exceeding capacity", async () => {
        try {
            // flow[0]=11 but capacity[0]=10
            await calculators.mcf.calculate({
                edges,
                capacity,
                cost,
                demand: [p - 11n, 0, 0, 11],
                flow: [11, 0, 3, 7, 0],
                potential: [0, 2, 1, 6],
                rcPlus:  [0, 0, 0, 0, 2],
                rcMinus: [0, 0, 0, 2, 0],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects conservation violation", async () => {
        try {
            // flow doesn't conserve at node 1: in=3, out=3+1=4
            await calculators.mcf.calculate({
                edges,
                capacity,
                cost,
                demand,
                flow: [3, 7, 3, 7, 1],
                potential: [0, 2, 1, 6],
                rcPlus:  [0, 0, 0, 0, 2],
                rcMinus: [0, 0, 0, 2, 0],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects suboptimal flow (complementary slackness fails)", async () => {
        try {
            // Suboptimal: 0→1:5, 0→2:5, 1→3:5, 2→3:5, 1→2:0
            // totalCost = 5*2+5*1+5*4+5*3+0 = 10+5+20+15 = 50
            // With potentials [0,2,1,6]:
            //   rc(0→1)=0, flow=5 (0<f<cap) → csFlow: 5*0=0 ✓
            //   rc(0→2)=0, flow=5 (0<f<cap) → csFlow: 5*0=0 ✓
            //   rc(1→3)=0, flow=5=cap → csFlow: 5*0=0 ✓
            //   rc(2→3)=-2, flow=5<7 → capSlack=2, rcMinus=2 → csSlack: 2*2=4 ≠ 0!
            await calculators.mcf.calculate({
                edges,
                capacity,
                cost,
                demand,
                flow: [5, 5, 5, 5, 0],
                potential: [0, 2, 1, 6],
                rcPlus:  [0, 0, 0, 0, 2],
                rcMinus: [0, 0, 0, 2, 0],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("rejects wrong reduced cost decomposition", async () => {
        try {
            // Use correct flow but wrong rcPlus/rcMinus that don't match reduced costs
            await calculators.mcf.calculate({
                edges,
                capacity,
                cost,
                demand,
                flow: [3, 7, 3, 7, 0],
                potential: [0, 2, 1, 6],
                // rc(1→2)=2 but we claim rcPlus=1, rcMinus=0 → 1≠2
                rcPlus:  [0, 0, 0, 0, 1],
                rcMinus: [0, 0, 0, 2, 0],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});
