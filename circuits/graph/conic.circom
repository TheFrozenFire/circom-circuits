pragma circom 2.2.2;

include "packing/bitify.circom";

/// Nonneg cone membership: constrains x[i] ∈ [0, 2^nBits) for all i.
/// K = R+^dim (nonneg orthant). Self-dual: K* = K.
///
/// Constraints: dim × (nBits + 1).
template Cone_Nonneg(dim, nBits) {
    signal input x[dim];

    component rc[dim];
    signal bits[dim][nBits];

    for (var i = 0; i < dim; i++) {
        rc[i] = Num2Bits(nBits);
        rc[i].in <== x[i];
        for (var b = 0; b < nBits; b++) {
            bits[i][b] <== rc[i].out[b];
        }
    }
}

/// Second-order cone membership: x[0] = t (scalar), x[1..dim-1] = body.
/// K = {(t, z) : t ≥ 0, t² ≥ ‖z‖²}. Self-dual: K* = K.
///
/// Body components can be signed (field-negative small values). We range-check
/// their squares to 2*nBits bits instead of the values themselves. Since
/// v² mod p = (p-v)² mod p, this proves |v| < 2^nBits regardless of sign.
///
/// Constraints: (nBits+1) + dim + (dim-1)*(2*nBits+1) + (2*nBits+1) + 2.
template Cone_SOC(dim, nBits) {
    signal input x[dim];

    // t ≥ 0
    component tRC = Num2Bits(nBits);
    tRC.in <== x[0];

    // t²
    signal tSq;
    tSq <== x[0] * x[0];

    // Body squares with range checks (handles signed values)
    signal bodySq[dim - 1];
    component bodySqRC[dim - 1];
    var normSq = 0;

    for (var i = 1; i < dim; i++) {
        bodySq[i - 1] <== x[i] * x[i];
        // Range-check the square: proves |x[i]| < 2^nBits
        bodySqRC[i - 1] = Num2Bits(2 * nBits);
        bodySqRC[i - 1].in <== bodySq[i - 1];
        normSq += bodySq[i - 1];
    }
    signal normSqSig <== normSq;

    // slack = t² - ‖body‖² ≥ 0
    signal slack <== tSq - normSqSig;
    component slackRC = Num2Bits(2 * nBits);
    slackRC.in <== slack;
}

/// Rotated second-order cone membership: x[0]=u, x[1]=v, x[2..dim-1]=body.
/// K = {(u, v, z) : u ≥ 0, v ≥ 0, 2uv ≥ ‖z‖²}. Self-dual: K* = K.
///
/// Same signed-body pattern as Cone_SOC.
///
/// Constraints: 2*(nBits+1) + 1 + (dim-2) + (dim-2)*(2*nBits+1) + (2*nBits+2) + 2.
template Cone_RotatedSOC(dim, nBits) {
    signal input x[dim];

    // u ≥ 0, v ≥ 0
    component uRC = Num2Bits(nBits);
    uRC.in <== x[0];
    component vRC = Num2Bits(nBits);
    vRC.in <== x[1];

    // u × v
    signal uv <== x[0] * x[1];
    // 2uv is linear (no extra constraint)

    // Body squares with range checks
    signal bodySq[dim - 2];
    component bodySqRC[dim - 2];
    var normSq = 0;

    for (var i = 2; i < dim; i++) {
        bodySq[i - 2] <== x[i] * x[i];
        bodySqRC[i - 2] = Num2Bits(2 * nBits);
        bodySqRC[i - 2].in <== bodySq[i - 2];
        normSq += bodySq[i - 2];
    }
    signal normSqSig <== normSq;

    // slack = 2uv - ‖body‖² ≥ 0
    signal slack <== 2 * uv - normSqSig;
    // 2uv can be up to 2 × (2^nBits)² = 2^(2*nBits+1)
    component slackRC = Num2Bits(2 * nBits + 1);
    slackRC.in <== slack;
}

/// Conic optimization verifier for LP + SOCP.
///
/// Standard form: min c^T x  s.t. Ax + s = b, s ∈ K
/// where K = R+^nNonneg × SOC(socDim)^nSOC
///
/// Witness: x (primal), s (primal slack in K), y (dual in K*)
///
/// Checks:
///   1. Primal feasibility: A*x + s = b
///   2. Stationarity: A^T*y + c = 0
///   3. Primal cone membership: s ∈ K
///   4. Dual cone membership: y ∈ K* (= K for self-dual cones)
///   5. Complementary slackness:
///      - Nonneg: s[i] × y[i] = 0 per element
///      - SOC: ⟨s_block, y_block⟩ = 0 per cone
///
/// O(nRows×nVars + nNonneg×nBits + nSOC×socDim×nBits) constraints.
template Conic_Verifier(nVars, nNonneg, nSOC, socDim, nBits) {
    var nRows = nNonneg + nSOC * socDim;

    // Problem data
    signal input c[nVars];
    signal input A[nRows][nVars];
    signal input b[nRows];

    // Witness
    signal input x[nVars];
    signal input s[nRows];
    signal input y[nRows];

    signal output objective;

    // --- 1. Primal feasibility: A*x + s = b ---
    signal Ax_terms[nRows][nVars];
    signal primalResidual[nRows];

    for (var i = 0; i < nRows; i++) {
        var Ax_sum = 0;
        for (var j = 0; j < nVars; j++) {
            Ax_terms[i][j] <== A[i][j] * x[j];
            Ax_sum += Ax_terms[i][j];
        }
        primalResidual[i] <== Ax_sum + s[i] - b[i];
        primalResidual[i] === 0;
    }

    // --- 2. Stationarity: A^T*y + c = 0 ---
    signal ATy_terms[nVars][nRows];
    signal stationarity[nVars];

    for (var j = 0; j < nVars; j++) {
        var sum = c[j];
        for (var i = 0; i < nRows; i++) {
            ATy_terms[j][i] <== A[i][j] * y[i];
            sum += ATy_terms[j][i];
        }
        stationarity[j] <== sum;
        stationarity[j] === 0;
    }

    // --- 3 & 4. Cone membership (primal s and dual y) ---

    // Nonneg block: first nNonneg components
    if (nNonneg > 0) {
        component sNonneg = Cone_Nonneg(nNonneg, nBits);
        component yNonneg = Cone_Nonneg(nNonneg, nBits);
        for (var i = 0; i < nNonneg; i++) {
            sNonneg.x[i] <== s[i];
            yNonneg.x[i] <== y[i];
        }
    }

    // SOC blocks: nSOC cones each of dimension socDim
    if (nSOC > 0) {
        component sSOC[nSOC];
        component ySOC[nSOC];
        for (var k = 0; k < nSOC; k++) {
            sSOC[k] = Cone_SOC(socDim, nBits);
            ySOC[k] = Cone_SOC(socDim, nBits);
            for (var j = 0; j < socDim; j++) {
                var idx = nNonneg + k * socDim + j;
                sSOC[k].x[j] <== s[idx];
                ySOC[k].x[j] <== y[idx];
            }
        }
    }

    // --- 5. Complementary slackness ---

    // Nonneg: per-element s[i] × y[i] = 0
    signal csNonneg[nNonneg];
    for (var i = 0; i < nNonneg; i++) {
        csNonneg[i] <== s[i] * y[i];
        csNonneg[i] === 0;
    }

    // SOC: block inner product ⟨s_block, y_block⟩ = 0
    signal csSOC_terms[nSOC][socDim];
    signal csSOC[nSOC];
    for (var k = 0; k < nSOC; k++) {
        var dotSum = 0;
        for (var j = 0; j < socDim; j++) {
            var idx = nNonneg + k * socDim + j;
            csSOC_terms[k][j] <== s[idx] * y[idx];
            dotSum += csSOC_terms[k][j];
        }
        csSOC[k] <== dotSum;
        csSOC[k] === 0;
    }

    // --- Objective: c^T x ---
    signal cx_terms[nVars];
    var objSum = 0;
    for (var j = 0; j < nVars; j++) {
        cx_terms[j] <== c[j] * x[j];
        objSum += cx_terms[j];
    }
    objective <== objSum;
}
