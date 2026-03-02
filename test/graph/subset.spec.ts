import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// 4 nodes, 2 properties each:
//   Node 0: [10, 100]
//   Node 1: [20, 200]
//   Node 2: [30, 300]
//   Node 3: [40, 400]

describe_circuit("Graph Subset", {
    aggregate: { path: "graph/subset.circom", template: "Graph_SubsetAggregate", params: [4, 2, 2, 0] },
    propCheck: { path: "graph/subset.circom", template: "Graph_SubsetPropertyCheck", params: [4, 2, 2, 0, 8] },
}, (calculators) => {
    const nodeProps = [[10, 100], [20, 200], [30, 300], [40, 400]];

    describe("Graph_SubsetAggregate", () => {
        it("extracts property 0 for subset [1, 3]", async () => {
            const w = await calculators.aggregate.calculate({
                nodeProps,
                subset: [1, 3],
            });
            assert.equal(w.value("main.out[0]"), 20n);
            assert.equal(w.value("main.out[1]"), 40n);
        });

        it("extracts property 0 for subset [0, 2]", async () => {
            const w = await calculators.aggregate.calculate({
                nodeProps,
                subset: [0, 2],
            });
            assert.equal(w.value("main.out[0]"), 10n);
            assert.equal(w.value("main.out[1]"), 30n);
        });
    });

    describe("Graph_SubsetPropertyCheck", () => {
        it("accepts when properties in range [10, 50)", async () => {
            await calculators.propCheck.calculate({
                nodeProps,
                subset: [0, 1],
                lo: 10,
                hi: 50,
            });
        });

        it("rejects when property below lo", async () => {
            try {
                // Node 0 has prop=10, lo=15 → 10 < 15 fails
                await calculators.propCheck.calculate({
                    nodeProps,
                    subset: [0, 1],
                    lo: 15,
                    hi: 50,
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });

        it("rejects when property at or above hi", async () => {
            try {
                // Node 1 has prop=20, hi=20 → 20 < 20 fails
                await calculators.propCheck.calculate({
                    nodeProps,
                    subset: [0, 1],
                    lo: 5,
                    hi: 20,
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });
});
