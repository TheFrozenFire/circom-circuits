pragma circom 2.2.2;

include "core/comparators.circom";
include "packing/bitify.circom";

/// KKT optimality verifier for quadratic programs.
///
/// Verifies optimality of: min (1/2) x^T Q x + c^T x
///   subject to: A x <= b, C x = d
///
/// Witness: x[nVars] (primal), lambda[nIneq] (dual >= 0), mu[nEq] (dual)
///
/// Checks:
///   1. Stationarity: Q x + c + A^T λ + C^T μ = 0
///   2. Primal feasibility: A x <= b (via range-checked slack), C x = d
///   3. Dual feasibility: λ >= 0 (via range check)
///   4. Complementary slackness: λ_i × slack_i = 0
///
/// Restriction: Q must be PSD for conditions to be sufficient.
/// All arithmetic is mod p; prover must ensure intermediate values stay bounded.
///
/// O(nVars² + (nIneq+nEq)×nVars) constraints.
template Graph_KKTVerifier(nVars, nIneq, nEq, nBits) {
    // Problem data
    signal input Q[nVars][nVars];
    signal input c[nVars];
    signal input A[nIneq][nVars];
    signal input b[nIneq];
    signal input C[nEq][nVars];
    signal input d[nEq];

    // Witness
    signal input x[nVars];
    signal input lambda[nIneq];
    signal input mu[nEq];

    signal output objective;

    // --- 1. Stationarity: Q x + c + A^T λ + C^T μ = 0 ---
    // Compute Qx
    signal Qx_terms[nVars][nVars];
    signal stationarity[nVars];

    for (var i = 0; i < nVars; i++) {
        var sum = c[i];

        // Q x term: sum_j Q[i][j] * x[j]
        for (var j = 0; j < nVars; j++) {
            Qx_terms[i][j] <== Q[i][j] * x[j];
            sum += Qx_terms[i][j];
        }

        // A^T λ term: sum_k A[k][i] * lambda[k]
        for (var k = 0; k < nIneq; k++) {
            // A[k][i] is an input signal, lambda[k] is an input signal
            // Need intermediate signal for quadratic constraint
        }

        // C^T μ term: sum_k C[k][i] * mu[k]
        // Same as above
    }

    // Rewrite with proper intermediate signals for quadratic terms
    signal AT_lambda_terms[nVars][nIneq];
    signal CT_mu_terms[nVars][nEq];

    for (var i = 0; i < nVars; i++) {
        var sum = c[i];

        for (var j = 0; j < nVars; j++) {
            sum += Qx_terms[i][j];
        }

        for (var k = 0; k < nIneq; k++) {
            AT_lambda_terms[i][k] <== A[k][i] * lambda[k];
            sum += AT_lambda_terms[i][k];
        }

        for (var k = 0; k < nEq; k++) {
            CT_mu_terms[i][k] <== C[k][i] * mu[k];
            sum += CT_mu_terms[i][k];
        }

        stationarity[i] <== sum;
        stationarity[i] === 0;
    }

    // --- 2. Primal feasibility ---
    // Inequality: A x <= b, i.e., b - Ax >= 0
    signal Ax_terms[nIneq][nVars];
    signal ineqSlack[nIneq];
    component ineqSlackRange[nIneq];
    signal ineqSlackBits[nIneq][nBits];

    for (var k = 0; k < nIneq; k++) {
        var Ax_sum = 0;
        for (var j = 0; j < nVars; j++) {
            Ax_terms[k][j] <== A[k][j] * x[j];
            Ax_sum += Ax_terms[k][j];
        }
        ineqSlack[k] <== b[k] - Ax_sum;

        // Range-check: slack >= 0
        ineqSlackRange[k] = Num2Bits(nBits);
        ineqSlackRange[k].in <== ineqSlack[k];
        for (var bit = 0; bit < nBits; bit++) {
            ineqSlackBits[k][bit] <== ineqSlackRange[k].out[bit];
        }
    }

    // Equality: C x = d
    signal Cx_terms[nEq][nVars];
    signal eqResidual[nEq];

    for (var k = 0; k < nEq; k++) {
        var Cx_sum = 0;
        for (var j = 0; j < nVars; j++) {
            Cx_terms[k][j] <== C[k][j] * x[j];
            Cx_sum += Cx_terms[k][j];
        }
        eqResidual[k] <== Cx_sum - d[k];
        eqResidual[k] === 0;
    }

    // --- 3. Dual feasibility: λ >= 0 ---
    component lambdaRange[nIneq];
    signal lambdaBits[nIneq][nBits];

    for (var k = 0; k < nIneq; k++) {
        lambdaRange[k] = Num2Bits(nBits);
        lambdaRange[k].in <== lambda[k];
        for (var bit = 0; bit < nBits; bit++) {
            lambdaBits[k][bit] <== lambdaRange[k].out[bit];
        }
    }

    // --- 4. Complementary slackness: λ_k × slack_k = 0 ---
    signal complementarity[nIneq];

    for (var k = 0; k < nIneq; k++) {
        complementarity[k] <== lambda[k] * ineqSlack[k];
        complementarity[k] === 0;
    }

    // --- Compute objective: output = x^T Q x + 2 c^T x = 2 × true objective ---
    // (1/2 division avoided; caller divides output by 2 for the real objective)
    signal Qx_row[nVars];
    signal xQx_terms[nVars];
    signal cx_terms[nVars];
    var dblObjSum = 0;

    for (var i = 0; i < nVars; i++) {
        var rowSum = 0;
        for (var j = 0; j < nVars; j++) {
            rowSum += Qx_terms[i][j];
        }
        Qx_row[i] <== rowSum;
        xQx_terms[i] <== x[i] * Qx_row[i];
        cx_terms[i] <== c[i] * x[i];
        dblObjSum += xQx_terms[i] + 2 * cx_terms[i];
    }

    objective <== dblObjSum;  // = 2 × true objective
}
