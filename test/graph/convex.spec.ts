import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

// Test 1: Simple LP (Q=0)
//   min c^T x = 2*x0 + 3*x1
//   s.t. x0 + x1 <= 10   (A=[1,1], b=10)
//        x0 >= 0, x1 >= 0 (as -x0 <= 0, -x1 <= 0)
//
// KKT solution: x = [10, 0], lambda = [0, 0, 3]
// Wait, let me solve properly.
// With 3 inequality constraints: x0+x1<=10, -x0<=0, -x1<=0
// A = [[1,1],[-1,0],[0,-1]], b = [10, 0, 0]
//
// Optimal: min 2*x0 + 3*x1 s.t. constraints
// At x=[10,0]: obj = 20
// KKT: c + A^T λ = 0 → [2,3] + [λ0-λ1, λ0-λ2] = 0
//   2 + λ0 - λ1 = 0  →  λ1 = λ0 + 2
//   3 + λ0 - λ2 = 0  →  λ2 = λ0 + 3
// Complementarity: λ0*(10-10)=0 ✓, λ1*(0-(-10))=λ1*10=0 → λ1=0 → λ0=-2 (negative!)
// That's not feasible. Let me reconsider.
//
// Actually for LP min c^T x, the dual vars are non-negative for <= constraints.
// The standard LP: x0=10, x1=0
// At this point, constraint 1 (x0+x1<=10) is active, constraint 2 (-x0<=0) is inactive (slack=10),
// constraint 3 (-x1<=0) is active.
// Complementarity: λ0 free, λ1=0, λ2 free
// Stationarity: [2,3] + λ0[1,1] + λ1[-1,0] + λ2[0,-1] = 0
//   2 + λ0 = 0 → λ0 = -2... negative again.
// The issue is this LP has the optimal at a vertex but the dual is negative.
// Let me flip to a maximization or use a different LP.
//
// Simpler approach: min -x0 - x1, s.t. x0 <= 5, x1 <= 3, x0 >= 0, x1 >= 0
// A = [[1,0],[0,1],[-1,0],[0,-1]], b = [5, 3, 0, 0]
// Optimal: x = [5, 3], obj = -8
// Stationarity: [-1,-1] + λ0[1,0] + λ1[0,1] + λ2[-1,0] + λ3[0,-1] = 0
//   -1 + λ0 - λ2 = 0
//   -1 + λ1 - λ3 = 0
// Active: x0<=5 (active), x1<=3 (active), x0>=0 (inactive, slack=5), x1>=0 (inactive, slack=3)
// Complementarity: λ2*5=0 → λ2=0, λ3*3=0 → λ3=0
// So: λ0=1, λ1=1, λ2=0, λ3=0 ✓ (all non-negative!)

// Test 2: Simple QP
//   min (1/2)(x0² + x1²) - 2*x0 - 3*x1
//   s.t. x0 + x1 <= 4, x0 >= 0, x1 >= 0
//
// Q = [[1,0],[0,1]], c = [-2, -3]
// A = [[1,1],[-1,0],[0,-1]], b = [4, 0, 0]
//
// Unconstrained optimum: Qx + c = 0 → x = [2, 3], but x0+x1=5 > 4 (infeasible)
// At boundary x0+x1=4: use Lagrange multiplier for the active constraint
// L = (1/2)(x0²+x1²) - 2x0 - 3x1 + λ(x0+x1-4)
// ∂L/∂x0 = x0 - 2 + λ = 0 → x0 = 2 - λ
// ∂L/∂x1 = x1 - 3 + λ = 0 → x1 = 3 - λ
// x0 + x1 = 5 - 2λ = 4 → λ = 0.5
// x0 = 1.5, x1 = 2.5... but these are not integers!
// For circom we need integer values. Let me adjust.
//
// Simpler QP with integer solution:
//   min (1/2)(x0² + x1²) subject to x0 + x1 <= 6, -x0 <= 0, -x1 <= 0
//   c = [0, 0]
// Unconstrained: x = [0, 0], which satisfies all constraints → optimal!
// KKT: Qx + c + A^T λ = [0,0] + [0,0] + [λ0-λ1, λ0-λ2] = 0
// All slacks: 6, 0, 0 → λ0*6=0→λ0=0, λ1=0, λ2=0 ✓
// Trivial. Let me make it non-trivial:
//
//   min (1/2)(x0² + x1²) - 4*x0 - 6*x1
//   s.t. x0 + x1 <= 8, -x0 <= 0, -x1 <= 0
// Unconstrained: x = [4, 6], x0+x1=10 > 8, infeasible
// Active constraint x0+x1=8: x0 = 4-λ, x1 = 6-λ, sum = 10-2λ = 8 → λ=1
// x0 = 3, x1 = 5. Both >= 0 ✓
// KKT: [3-4+1, 5-6+1] = [0, 0] ✓
// λ = [1, 0, 0], slacks = [0, 3, 5]
// Complementarity: 1*0=0, 0*3=0, 0*5=0 ✓
// Objective: (1/2)(9+25) - 12 - 30 = 17 - 42 = -25
// 2*objective = 9+25 + 2*(-12-30) = 34 - 84 = -50
// In field: p - 50

describe_circuit("Graph KKTVerifier", {
    lp: {
        path: "graph/convex.circom",
        template: "Graph_KKTVerifier",
        params: [2, 4, 0, 8],  // 2 vars, 4 inequalities, 0 equalities
    },
    qp: {
        path: "graph/convex.circom",
        template: "Graph_KKTVerifier",
        params: [2, 3, 0, 8],  // 2 vars, 3 inequalities, 0 equalities
    },
}, (calculators) => {
    const p = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

    describe("LP (Q=0): min -x0 - x1 s.t. x0<=5, x1<=3, x0>=0, x1>=0", () => {
        it("verifies optimal x=[5,3] with λ=[1,1,0,0]", async () => {
            const w = await calculators.lp.calculate({
                Q: [[0, 0], [0, 0]],
                c: [p - 1n, p - 1n],  // c = [-1, -1] in field
                A: [[1, 0], [0, 1], [p - 1n, 0], [0, p - 1n]],  // [-1,0], [0,-1] in field
                b: [5, 3, 0, 0],
                C: [],
                d: [],
                x: [5, 3],
                lambda: [1, 1, 0, 0],
                mu: [],
            });
            // 2*obj = 0 + 2*(-5-3) = -16 = p-16 in field
            assert.equal(w.value("main.objective"), p - 16n);
        });

        it("rejects non-optimal solution", async () => {
            try {
                // x=[4,3] is feasible but not optimal. Stationarity fails:
                // c + A^T λ = [-1,-1] + [λ0-λ2, λ1-λ3] ≠ 0 for any valid λ
                // with complementarity (x0<5 so λ0=0, x1=3 so λ1 free, etc.)
                await calculators.lp.calculate({
                    Q: [[0, 0], [0, 0]],
                    c: [p - 1n, p - 1n],
                    A: [[1, 0], [0, 1], [p - 1n, 0], [0, p - 1n]],
                    b: [5, 3, 0, 0],
                    C: [],
                    d: [],
                    x: [4, 3],
                    lambda: [1, 1, 0, 0],  // stationarity fails
                    mu: [],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });

        it("rejects infeasible solution", async () => {
            try {
                // x=[6,3] violates x0<=5
                await calculators.lp.calculate({
                    Q: [[0, 0], [0, 0]],
                    c: [p - 1n, p - 1n],
                    A: [[1, 0], [0, 1], [p - 1n, 0], [0, p - 1n]],
                    b: [5, 3, 0, 0],
                    C: [],
                    d: [],
                    x: [6, 3],
                    lambda: [1, 1, 0, 0],
                    mu: [],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });

    describe("QP: min (1/2)(x0²+x1²) - 4x0 - 6x1 s.t. x0+x1<=8, x>=0", () => {
        it("verifies optimal x=[3,5] with λ=[1,0,0]", async () => {
            const w = await calculators.qp.calculate({
                Q: [[1, 0], [0, 1]],
                c: [p - 4n, p - 6n],  // c = [-4, -6] in field
                A: [[1, 1], [p - 1n, 0], [0, p - 1n]],  // [1,1], [-1,0], [0,-1]
                b: [8, 0, 0],
                C: [],
                d: [],
                x: [3, 5],
                lambda: [1, 0, 0],
                mu: [],
            });
            // 2*obj = x^T Q x + 2 c^T x = (9+25) + 2(-12-30) = 34 - 84 = -50
            assert.equal(w.value("main.objective"), p - 50n);
        });

        it("rejects when complementary slackness violated", async () => {
            try {
                // λ[1]=1 but slack for -x0<=0 is 3 (since x0=3): 1*3≠0
                await calculators.qp.calculate({
                    Q: [[1, 0], [0, 1]],
                    c: [p - 4n, p - 6n],
                    A: [[1, 1], [p - 1n, 0], [0, p - 1n]],
                    b: [8, 0, 0],
                    C: [],
                    d: [],
                    x: [3, 5],
                    lambda: [1, 1, 0],  // λ[1]=1 but constraint 2 inactive
                    mu: [],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });
});
