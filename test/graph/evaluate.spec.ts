import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// Test graph: 4 nodes, 3 edges
// Node properties (2 props each): [1,2], [3,4], [5,6], [7,8]
// Edges: (0,1), (1,2), (2,3)

describe_circuit("Graph Evaluate", {
    evalLinear: { path: "graph/evaluate.circom", template: "Graph_EvalLinear", params: [4, 3, 2] },
    evalQuadratic: { path: "graph/evaluate.circom", template: "Graph_EvalQuadratic", params: [4, 3, 2] },
    evalEdgeEq: { path: "graph/evaluate.circom", template: "Graph_EvalEdgeExpr", params: [3, 2, 8, 0] },
    evalEdgeLt: { path: "graph/evaluate.circom", template: "Graph_EvalEdgeExpr", params: [3, 2, 8, 1] },
}, (calculators) => {
    const edges = [[0, 1], [1, 2], [2, 3]];
    const nodeProps = [[1, 2], [3, 4], [5, 6], [7, 8]];

    describe("Graph_EvalLinear", () => {
        it("computes linear expression with unit coefficients", async () => {
            // coeff = [1,1,1,1], constant = 0
            // Edge (0,1): 1*1 + 1*2 + 1*3 + 1*4 = 10
            // Edge (1,2): 1*3 + 1*4 + 1*5 + 1*6 = 18
            // Edge (2,3): 1*5 + 1*6 + 1*7 + 1*8 = 26
            const w = await calculators.evalLinear.calculate({
                edges,
                nodeProps,
                coeff: [1, 1, 1, 1],
                constant: 0,
            });
            assert.equal(w.value("main.out[0]"), 10n);
            assert.equal(w.value("main.out[1]"), 18n);
            assert.equal(w.value("main.out[2]"), 26n);
        });

        it("computes with constant offset", async () => {
            // coeff = [1, 0, 0, 0], constant = 100
            // Edge (0,1): 1*1 + 100 = 101
            const w = await calculators.evalLinear.calculate({
                edges,
                nodeProps,
                coeff: [1, 0, 0, 0],
                constant: 100,
            });
            assert.equal(w.value("main.out[0]"), 101n);
        });

        it("computes difference (dst[0] - src[0])", async () => {
            // coeff = [-1, 0, 1, 0], constant = 0
            // But we need to work in field arithmetic — use large prime minus 1
            const p = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
            const negOne = p - 1n;
            const w = await calculators.evalLinear.calculate({
                edges,
                nodeProps,
                coeff: [negOne, 0, 1, 0],
                constant: 0,
            });
            // Edge (0,1): -1*1 + 1*3 = 2
            assert.equal(w.value("main.out[0]"), 2n);
            // Edge (1,2): -1*3 + 1*5 = 2
            assert.equal(w.value("main.out[1]"), 2n);
        });
    });

    describe("Graph_EvalQuadratic", () => {
        it("computes cross-product with identity Q", async () => {
            // Q = [[1,0],[0,1]], linCoeff = [0,0,0,0], constant = 0
            // Edge (0,1): 1*1*3 + 0*1*4 + 0*2*3 + 1*2*4 = 3 + 8 = 11
            // Edge (1,2): 1*3*5 + 0*3*6 + 0*4*5 + 1*4*6 = 15 + 24 = 39
            const w = await calculators.evalQuadratic.calculate({
                edges,
                nodeProps,
                Q: [[1, 0], [0, 1]],
                linCoeff: [0, 0, 0, 0],
                constant: 0,
            });
            assert.equal(w.value("main.out[0]"), 11n);
            assert.equal(w.value("main.out[1]"), 39n);
        });

        it("computes with linear terms and constant", async () => {
            // Q = [[0,0],[0,0]], linCoeff = [2,0,3,0], constant = 10
            // Edge (0,1): 2*1 + 3*3 + 10 = 2 + 9 + 10 = 21
            const w = await calculators.evalQuadratic.calculate({
                edges,
                nodeProps,
                Q: [[0, 0], [0, 0]],
                linCoeff: [2, 0, 3, 0],
                constant: 10,
            });
            assert.equal(w.value("main.out[0]"), 21n);
        });
    });

    describe("Graph_EvalEdgeExpr", () => {
        // Edge props: [[10, 10], [5, 8], [3, 3]]
        const edgeProps = [[10, 10], [5, 8], [3, 3]];

        it("evaluates equality (prop0 == prop1)", async () => {
            const w = await calculators.evalEdgeEq.calculate({
                edgeProps,
                propIdx1: 0,
                propIdx2: 1,
            });
            assert.equal(w.value("main.results[0]"), 1n);  // 10 == 10
            assert.equal(w.value("main.results[1]"), 0n);  // 5 != 8
            assert.equal(w.value("main.results[2]"), 1n);  // 3 == 3
        });

        it("evaluates less-than (prop0 < prop1)", async () => {
            const w = await calculators.evalEdgeLt.calculate({
                edgeProps,
                propIdx1: 0,
                propIdx2: 1,
            });
            assert.equal(w.value("main.results[0]"), 0n);  // 10 < 10 = false
            assert.equal(w.value("main.results[1]"), 1n);  // 5 < 8 = true
            assert.equal(w.value("main.results[2]"), 0n);  // 3 < 3 = false
        });
    });
});
