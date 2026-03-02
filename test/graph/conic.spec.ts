import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

const p = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

describe_circuit("Conic Verifier", {
    lp: {
        path: "graph/conic.circom",
        template: "Conic_Verifier",
        params: [2, 4, 0, 0, 8],  // nVars=2, nNonneg=4, nSOC=0, socDim=0
    },
    socp: {
        path: "graph/conic.circom",
        template: "Conic_Verifier",
        params: [2, 0, 1, 3, 8],  // nVars=2, nNonneg=0, nSOC=1, socDim=3
    },
    mixed: {
        path: "graph/conic.circom",
        template: "Conic_Verifier",
        params: [1, 1, 1, 3, 8],  // nVars=1, nNonneg=1, nSOC=1, socDim=3
    },
}, (calculators) => {
    // ---------------------------------------------------------------
    // LP: min -x0 - x1  s.t. x0 <= 5, x1 <= 3, x0 >= 0, x1 >= 0
    // Standard form: A x + s = b, s >= 0
    //   Row 0: x0 + s0 = 5       →  A=[1,0], s0=5-x0
    //   Row 1: x1 + s1 = 3       →  A=[0,1], s1=3-x1
    //   Row 2: -x0 + s2 = 0      →  A=[-1,0], s2=x0
    //   Row 3: -x1 + s3 = 0      →  A=[0,-1], s3=x1
    //
    // Optimal: x=[5,3], s=[0,0,5,3], y=[1,1,0,0]
    // Stationarity: A^Ty + c = [1-0, 1-0] + [-1,-1] = [0, 0]
    // Complementarity: 0*1=0, 0*1=0, 5*0=0, 3*0=0
    // ---------------------------------------------------------------
    describe("LP (pure nonneg)", () => {
        const lpInputs = {
            c: [p - 1n, p - 1n],
            A: [[1, 0], [0, 1], [p - 1n, 0], [0, p - 1n]],
            b: [5, 3, 0, 0],
        };

        it("verifies optimal x=[5,3]", async () => {
            const w = await calculators.lp.calculate({
                ...lpInputs,
                x: [5, 3],
                s: [0, 0, 5, 3],
                y: [1, 1, 0, 0],
            });
            assert.equal(w.value("main.objective"), p - 8n);
        });

        it("rejects non-optimal (complementary slackness fails)", async () => {
            try {
                // x=[4,2]: s=[1,1,4,2], y=[1,1,0,0]
                // Complementarity: s[0]*y[0] = 1*1 = 1 ≠ 0
                await calculators.lp.calculate({
                    ...lpInputs,
                    x: [4, 2],
                    s: [1, 1, 4, 2],
                    y: [1, 1, 0, 0],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });

        it("rejects infeasible (primal residual nonzero)", async () => {
            try {
                // Wrong slack: s=[0,0,5,3] but x=[6,3] so row 0: 6+0≠5
                await calculators.lp.calculate({
                    ...lpInputs,
                    x: [6, 3],
                    s: [0, 0, 5, 3],
                    y: [1, 1, 0, 0],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });

    // ---------------------------------------------------------------
    // SOCP: min -x0  s.t. ||(x0, x1)|| <= 3
    // Standard form: A x + s = b, s ∈ SOC(3)
    //   Row 0 (t):  0*x0 + 0*x1 + s0 = 3    →  s0 = 3
    //   Row 1 (z1): -x0 + s1 = 0             →  s1 = x0
    //   Row 2 (z2): -x1 + s2 = 0             →  s2 = x1
    //
    // Optimal: x=[3,0], s=[3,3,0]
    // Stationarity: A^Ty + c = [0-(p-1), 0-0] + [p-1, 0]
    //   A^T = [[0, -1, 0], [0, 0, -1]]
    //   A^Ty = [-y1, -y2]
    //   -y1 + (p-1) = 0  →  y1 = p-1
    //   -y2 + 0 = 0      →  y2 = 0
    //   y0 free (row 0 of A is [0,0]) but SOC + CS determine it
    //
    // SOC membership y: (y0, p-1, 0) → y0² ≥ 1 and y0 ≥ 0 → y0 ≥ 1
    // Complementarity: 3*y0 + 3*(p-1) + 0*0 = 3*y0 - 3 = 0  →  y0 = 1
    // Dual: y=[1, p-1, 0], SOC check: 1 ≥ 1+0 ✓
    // ---------------------------------------------------------------
    describe("SOCP (single SOC)", () => {
        const socpInputs = {
            c: [p - 1n, 0],
            A: [[0, 0], [p - 1n, 0], [0, p - 1n]],
            b: [3, 0, 0],
        };

        it("verifies optimal x=[3,0] with objective=-3", async () => {
            const w = await calculators.socp.calculate({
                ...socpInputs,
                x: [3, 0],
                s: [3, 3, 0],
                y: [1, p - 1n, 0],
            });
            assert.equal(w.value("main.objective"), p - 3n);
        });

        it("rejects SOC membership violation", async () => {
            try {
                // x=[4,0]: s=[3,4,0], SOC check: 9 ≥ 16? No → slack = -7
                await calculators.socp.calculate({
                    ...socpInputs,
                    x: [4, 0],
                    s: [3, 4, 0],
                    y: [1, p - 1n, 0],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });

        it("rejects stationarity violation", async () => {
            try {
                // Correct primal but wrong dual: y=[2, p-1, 0]
                // Stationarity: -(p-1) + (p-1) = 0 for x0, ok
                // But CS: 3*2 + 3*(p-1) + 0 = 6-3 = 3 ≠ 0
                await calculators.socp.calculate({
                    ...socpInputs,
                    x: [3, 0],
                    s: [3, 3, 0],
                    y: [2, p - 1n, 0],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });

    // ---------------------------------------------------------------
    // Mixed: min -x0  s.t. x0 <= 5 (nonneg), ||(x0, 0)|| <= 3 (SOC)
    // nRows = 1 + 3 = 4
    //   Row 0 (nonneg): x0 + s0 = 5       →  s0 = 5-x0
    //   Row 1 (SOC t):  0*x0 + s1 = 3     →  s1 = 3
    //   Row 2 (SOC z1): -x0 + s2 = 0      →  s2 = x0
    //   Row 3 (SOC z2): 0*x0 + s3 = 0     →  s3 = 0
    //
    // Optimal: x=[3], s=[2, 3, 3, 0] (SOC binding, nonneg slack)
    // Stationarity: A^Ty + c = [y0 + 0 - y2 + 0] + [p-1] = y0 - y2 - 1 = 0
    // Nonneg CS: s0*y0 = 2*y0 = 0  →  y0 = 0
    // SOC CS: 3*y1 + 3*y2 + 0*y3 = 0  →  y1 = -y2 (field: y1 = p - y2)
    // Stationarity: 0 - y2 - 1 = 0  →  y2 = p-1
    // → y1 = 1
    // Dual SOC: (1, p-1, 0), 1² ≥ 1²+0² ✓
    // Dual nonneg: y0=0 ≥ 0 ✓
    // ---------------------------------------------------------------
    describe("Mixed LP + SOCP", () => {
        const mixedInputs = {
            c: [p - 1n],
            A: [[1], [0], [p - 1n], [0]],
            b: [5, 3, 0, 0],
        };

        it("verifies optimal x=[3] with SOC binding", async () => {
            const w = await calculators.mixed.calculate({
                ...mixedInputs,
                x: [3],
                s: [2, 3, 3, 0],
                y: [0, 1, p - 1n, 0],
            });
            assert.equal(w.value("main.objective"), p - 3n);
        });

        it("rejects wrong dual (nonneg complementarity fails)", async () => {
            try {
                // y0=1 but s0=2 → s0*y0 = 2 ≠ 0
                await calculators.mixed.calculate({
                    ...mixedInputs,
                    x: [3],
                    s: [2, 3, 3, 0],
                    y: [1, 1, p - 1n, 0],
                });
                assert.fail("should have thrown");
            } catch (e: any) {
                assert.notEqual(e.message, "should have thrown");
            }
        });
    });
});
