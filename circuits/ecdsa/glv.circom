pragma circom 2.2.2;

include "arithmetic/bigint.circom";
include "arithmetic/bigint_func.circom";
include "collections/multiplexer.circom";
include "core/bitwise.circom";
include "core/comparators.circom";
include "packing/bitify.circom";
include "ecdsa/constants.circom";
include "ecdsa/functions.circom";
include "ecdsa/point.circom";

// ═══════════════════════════════════════════════════
// GLV-accelerated variable-base scalar multiplication on secp256k1.
// Exploits the secp256k1 endomorphism φ(x,y) = (β·x, y) where
// φ(P) = λ·P to halve the scalar multiplication loop from 256 to 129.
// ═══════════════════════════════════════════════════

/// GLV-accelerated scalar multiplication: out = scalar * point on secp256k1.
/// Same interface as Secp256k1ScalarMult — drop-in replacement.
///
/// NOTE: Does not handle scalar = 0 or point = identity.
/// The caller must ensure scalar ∈ [1, order-1] and point is a valid curve point.
template Secp256k1GLVScalarMult(n, k) {
    assert(n == 32 && k == 8);

    signal input scalar[k];
    signal input point[2][k];
    signal output out[2][k];

    var NUM_BITS = 129;

    // ───────────────────────────────────────────────
    // Phase 1: GLV decomposition (witness + constrain)
    // ───────────────────────────────────────────────

    var decomp[4][200] = glv_decompose(n, k, scalar);

    signal k1_abs[k];
    signal k2_abs[k];
    signal s1, s2;

    for (var i = 0; i < k; i++) {
        k1_abs[i] <-- decomp[0][i];
        k2_abs[i] <-- decomp[1][i];
    }
    s1 <-- decomp[2][0];
    s2 <-- decomp[3][0];

    // s1, s2 are binary
    s1 * (s1 - 1) === 0;
    s2 * (s2 - 1) === 0;

    // Range-check k1_abs: limbs 0-3 are 32-bit, limb 4 is binary, limbs 5-7 are 0
    component k1_n2b[4];
    for (var i = 0; i < 4; i++) {
        k1_n2b[i] = Num2Bits(n);
        k1_n2b[i].in <== k1_abs[i];
    }
    k1_abs[4] * (k1_abs[4] - 1) === 0;
    k1_abs[5] === 0;
    k1_abs[6] === 0;
    k1_abs[7] === 0;

    // Range-check k2_abs: same structure
    component k2_n2b[4];
    for (var i = 0; i < 4; i++) {
        k2_n2b[i] = Num2Bits(n);
        k2_n2b[i].in <== k2_abs[i];
    }
    k2_abs[4] * (k2_abs[4] - 1) === 0;
    k2_abs[5] === 0;
    k2_abs[6] === 0;
    k2_abs[7] === 0;

    // Compute k2_lambda = |k2| * lambda mod order
    var lambda_const[8];
    lambda_const[0] = 455327090;   lambda_const[1] = 3741488764;
    lambda_const[2] = 545351288;   lambda_const[3] = 305013482;
    lambda_const[4] = 2282906714;  lambda_const[5] = 2770738178;
    lambda_const[6] = 3227267296;  lambda_const[7] = 1399041356;

    var order_const[8] = SECP256K1_ORDER(n, k);

    signal lambda_sig[k];
    signal order_sig[k];
    for (var i = 0; i < k; i++) {
        lambda_sig[i] <== lambda_const[i];
        order_sig[i] <== order_const[i];
    }

    signal k2l[k];
    k2l <== BigMultModP(n, k)(k2_abs, lambda_sig, order_sig);

    // Verify decomposition: scalar + 2*s1*k1 + 2*s2*k2l - k1 - k2l = q * order
    signal s1_k1[k];
    for (var i = 0; i < k; i++) {
        s1_k1[i] <== s1 * k1_abs[i];
    }
    signal s2_k2l[k];
    for (var i = 0; i < k; i++) {
        s2_k2l[i] <== s2 * k2l[i];
    }

    // Witness: compute q via multi-limb arithmetic
    var k2l_var[200] = prod_mod_p(n, k, decomp[1], lambda_const, order_const);
    var pos_limbs[200];
    var neg_limbs[200];
    for (var i = 0; i < 200; i++) { pos_limbs[i] = 0; neg_limbs[i] = 0; }
    for (var i = 0; i < k; i++) {
        pos_limbs[i] = scalar[i] + 2 * decomp[2][0] * decomp[0][i]
                                  + 2 * decomp[3][0] * k2l_var[i];
        neg_limbs[i] = decomp[0][i] + k2l_var[i];
    }
    // Carry-normalize
    for (var i = 0; i < k; i++) {
        pos_limbs[i+1] = pos_limbs[i+1] + (pos_limbs[i] >> n);
        pos_limbs[i] = pos_limbs[i] % (1 << n);
    }
    for (var i = 0; i < k; i++) {
        neg_limbs[i+1] = neg_limbs[i+1] + (neg_limbs[i] >> n);
        neg_limbs[i] = neg_limbs[i] % (1 << n);
    }
    var q_witness = 0;
    if (long_gt(n, k + 1, neg_limbs, pos_limbs) == 1) {
        var d[200] = long_sub(n, k + 1, neg_limbs, pos_limbs);
        var dv[2][200] = long_div2(n, k, 1, d, order_const);
        q_witness = 0 - dv[0][0];
    } else {
        var d[200] = long_sub(n, k + 1, pos_limbs, neg_limbs);
        var dv[2][200] = long_div2(n, k, 1, d, order_const);
        q_witness = dv[0][0];
    }

    // q = q_pos - q_neg
    signal q_pos, q_neg;
    if (q_witness >= 0) {
        q_pos <-- q_witness;
        q_neg <-- 0;
    } else {
        q_pos <-- 0;
        q_neg <-- 0 - q_witness;
    }

    signal _q_pos_bits[2] <== Num2Bits(2)(q_pos);
    q_neg * (q_neg - 1) === 0;
    q_pos * q_neg === 0;

    signal q_order[k];
    for (var i = 0; i < k; i++) {
        q_order[i] <== (q_pos - q_neg) * order_sig[i];
    }

    signal verify_diff[k];
    for (var i = 0; i < k; i++) {
        verify_diff[i] <== scalar[i] + 2 * s1_k1[i] + 2 * s2_k2l[i]
                          - k1_abs[i] - k2l[i] - q_order[i];
    }
    CheckCarryToZero(n, n + 4, k)(verify_diff);

    // ───────────────────────────────────────────────
    // Phase 2: Endomorphism + conditional negation
    // ───────────────────────────────────────────────

    var p_const[8] = SECP256K1_PRIME(n, k);
    var beta_const[8] = SECP256K1_BETA(n, k);

    signal beta_sig[k];
    signal p_sig[k];
    for (var i = 0; i < k; i++) {
        beta_sig[i] <== beta_const[i];
        p_sig[i] <== p_const[i];
    }

    // Q.x = beta * point.x mod p
    signal qx[k];
    qx <== BigMultModP(n, k)(beta_sig, point[0], p_sig);

    // neg_y = p - point.y
    signal neg_y[k];
    var neg_y_wit[200] = long_sub(n, k, p_const, point[1]);
    for (var i = 0; i < k; i++) {
        neg_y[i] <-- neg_y_wit[i];
    }

    component neg_y_rc[k];
    for (var i = 0; i < k; i++) {
        neg_y_rc[i] = Num2Bits(n);
        neg_y_rc[i].in <== neg_y[i];
    }

    signal neg_check[k];
    for (var i = 0; i < k; i++) {
        neg_check[i] <== neg_y[i] + point[1][i] - p_sig[i];
    }
    CheckCarryToZero(n, n + 1, k)(neg_check);

    // P' = (point.x, s1 ? neg_y : point.y)
    // Q' = (qx,      s2 ? neg_y : point.y)
    signal pp[2][k];
    signal qp[2][k];
    for (var i = 0; i < k; i++) {
        pp[0][i] <== point[0][i];
        pp[1][i] <== s1 * (neg_y[i] - point[1][i]) + point[1][i];
        qp[0][i] <== qx[i];
        qp[1][i] <== s2 * (neg_y[i] - point[1][i]) + point[1][i];
    }

    // P' + Q' precomputed
    signal ppqp[2][k];
    ppqp <== Secp256k1AddUnequal(n, k)(pp, qp);

    // ───────────────────────────────────────────────
    // Phase 3: Dummy point
    // ───────────────────────────────────────────────

    var dummyVar[2][8] = SECP256K1_DUMMY(n, k);
    signal dummy[2][k];
    for (var i = 0; i < k; i++) {
        dummy[0][i] <== dummyVar[0][i];
        dummy[1][i] <== dummyVar[1][i];
    }

    // ───────────────────────────────────────────────
    // Phase 4: Main loop (129 iterations, MSB to LSB)
    // ───────────────────────────────────────────────

    // All signals/components declared outside the loop
    signal sel[NUM_BITS];
    signal partial[NUM_BITS][2][k];
    signal intermed[NUM_BITS - 1][2][k];
    component doublers[NUM_BITS - 1];
    component adders[NUM_BITS - 1];
    component mux_x[NUM_BITS];
    component mux_y[NUM_BITS];
    component is_zero_sel[NUM_BITS];
    signal has_prev_nz[NUM_BITS];

    for (var idx = NUM_BITS - 1; idx >= 0; idx--) {
        // Compute sel = k1_bit + 2 * k2_bit
        if (idx < 128) {
            sel[idx] <== k1_n2b[idx \ n].out[idx % n]
                       + 2 * k2_n2b[idx \ n].out[idx % n];
        } else {
            sel[idx] <== k1_abs[4] + 2 * k2_abs[4];
        }

        // is_zero_sel: 1 if sel==0, 0 otherwise
        is_zero_sel[idx] = IsZero();
        is_zero_sel[idx].in <== sel[idx];

        // 4-way mux: [dummy, P', Q', P'+Q']
        mux_x[idx] = Multiplexer(k, 4);
        mux_y[idx] = Multiplexer(k, 4);
        mux_x[idx].sel <== sel[idx];
        mux_y[idx].sel <== sel[idx];
        for (var l = 0; l < k; l++) {
            mux_x[idx].inp[0][l] <== dummy[0][l];
            mux_x[idx].inp[1][l] <== pp[0][l];
            mux_x[idx].inp[2][l] <== qp[0][l];
            mux_x[idx].inp[3][l] <== ppqp[0][l];

            mux_y[idx].inp[0][l] <== dummy[1][l];
            mux_y[idx].inp[1][l] <== pp[1][l];
            mux_y[idx].inp[2][l] <== qp[1][l];
            mux_y[idx].inp[3][l] <== ppqp[1][l];
        }

        if (idx == NUM_BITS - 1) {
            // MSB: partial = mux output, has_prev = (sel != 0)
            for (var l = 0; l < k; l++) {
                partial[idx][0][l] <== mux_x[idx].out[l];
                partial[idx][1][l] <== mux_y[idx].out[l];
            }
            has_prev_nz[idx] <== 1 - is_zero_sel[idx].out;
        } else {
            // Double previous
            doublers[idx] = Secp256k1Double(n, k);
            for (var l = 0; l < k; l++) {
                doublers[idx].in[0][l] <== partial[idx + 1][0][l];
                doublers[idx].in[1][l] <== partial[idx + 1][1][l];
            }

            // Add mux output
            adders[idx] = Secp256k1AddUnequal(n, k);
            for (var l = 0; l < k; l++) {
                adders[idx].a[0][l] <== doublers[idx].out[0][l];
                adders[idx].a[1][l] <== doublers[idx].out[1][l];
                adders[idx].b[0][l] <== mux_x[idx].out[l];
                adders[idx].b[1][l] <== mux_y[idx].out[l];
            }

            // intermed = sel!=0 ? added : doubled
            for (var l = 0; l < k; l++) {
                intermed[idx][0][l] <== (1 - is_zero_sel[idx].out) * (adders[idx].out[0][l] - doublers[idx].out[0][l]) + doublers[idx].out[0][l];
                intermed[idx][1][l] <== (1 - is_zero_sel[idx].out) * (adders[idx].out[1][l] - doublers[idx].out[1][l]) + doublers[idx].out[1][l];
            }

            // has_prev_nz = prev OR (sel != 0)
            has_prev_nz[idx] <== has_prev_nz[idx + 1] + (1 - is_zero_sel[idx].out)
                                - has_prev_nz[idx + 1] * (1 - is_zero_sel[idx].out);

            // partial = has_prev_from_above ? intermed : mux_output
            for (var l = 0; l < k; l++) {
                partial[idx][0][l] <== has_prev_nz[idx + 1] * (intermed[idx][0][l] - mux_x[idx].out[l]) + mux_x[idx].out[l];
                partial[idx][1][l] <== has_prev_nz[idx + 1] * (intermed[idx][1][l] - mux_y[idx].out[l]) + mux_y[idx].out[l];
            }
        }
    }

    for (var l = 0; l < k; l++) {
        out[0][l] <== partial[0][0][l];
        out[1][l] <== partial[0][1][l];
    }
}
