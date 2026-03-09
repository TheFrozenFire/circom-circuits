pragma circom 2.2.2;

include "arithmetic/bigint.circom";
include "arithmetic/bigint_func.circom";
include "collections/multiplexer.circom";
include "core/comparators.circom";
include "packing/bitify.circom";
include "ecdsa/constants.circom";
include "ecdsa/functions.circom";
include "ecdsa/point.circom";

/// Diagnostic: Phase 2 only — algebraic verification without MSM.
template EisensteinPhase2Diag(n, k) {
    assert(n == 32 && k == 8);

    signal input scalar[k];
    signal input point[2][k];
    signal input hint[2][k];
    signal output out[2][k];

    var NUM_BITS = 68;
    var p_const[8] = SECP256K1_PRIME(n, k);
    var order_const[30];
    for (var j = 0; j < 30; j++) order_const[j] = 0;
    var _ord[8] = SECP256K1_ORDER(n, k);
    for (var j = 0; j < k; j++) order_const[j] = _ord[j];
    var lambda_const[30];
    for (var j = 0; j < 30; j++) lambda_const[j] = 0;
    var _lam[8] = SECP256K1_LAMBDA(n, k);
    for (var j = 0; j < k; j++) lambda_const[j] = _lam[j];

    // Phase 1: Verify hint Q is on curve
    Secp256k1PointOnCurve()(hint[0], hint[1]);
    CheckInRangeSecp256k1()(hint[0]);
    CheckInRangeSecp256k1()(hint[1]);

    for (var i = 0; i < k; i++) {
        out[0][i] <== hint[0][i];
        out[1][i] <== hint[1][i];
    }

    // Phase 2: Eisenstein decomposition verification
    var eis[10][30] = eisenstein_half_gcd(n, k, scalar);

    signal x0_abs[k], x1_abs[k], z0_abs[k], z1_abs[k];
    signal s0, s1, s2, s3, sx;

    for (var i = 0; i < k; i++) {
        x0_abs[i] <-- eis[0][i];
        x1_abs[i] <-- eis[1][i];
        z0_abs[i] <-- eis[2][i];
        z1_abs[i] <-- eis[3][i];
    }
    s0 <-- eis[4][0];
    s1 <-- eis[5][0];
    s2 <-- eis[6][0];
    s3 <-- eis[7][0];
    sx <-- eis[8][0];

    // Constrain sign bits binary
    s0 * (s0 - 1) === 0;
    s1 * (s1 - 1) === 0;
    s2 * (s2 - 1) === 0;
    s3 * (s3 - 1) === 0;
    sx * (sx - 1) === 0;

    // Range-check each sub-scalar < 2^68
    var EXTRA_BITS = NUM_BITS - 64;

    component x0_rc[3];
    x0_rc[0] = Num2Bits(n);  x0_rc[0].in <== x0_abs[0];
    x0_rc[1] = Num2Bits(n);  x0_rc[1].in <== x0_abs[1];
    x0_rc[2] = Num2Bits(EXTRA_BITS);  x0_rc[2].in <== x0_abs[2];
    for (var i = 3; i < k; i++) x0_abs[i] === 0;

    component x1_rc[3];
    x1_rc[0] = Num2Bits(n);  x1_rc[0].in <== x1_abs[0];
    x1_rc[1] = Num2Bits(n);  x1_rc[1].in <== x1_abs[1];
    x1_rc[2] = Num2Bits(EXTRA_BITS);  x1_rc[2].in <== x1_abs[2];
    for (var i = 3; i < k; i++) x1_abs[i] === 0;

    component z0_rc[3];
    z0_rc[0] = Num2Bits(n);  z0_rc[0].in <== z0_abs[0];
    z0_rc[1] = Num2Bits(n);  z0_rc[1].in <== z0_abs[1];
    z0_rc[2] = Num2Bits(EXTRA_BITS);  z0_rc[2].in <== z0_abs[2];
    for (var i = 3; i < k; i++) z0_abs[i] === 0;

    component z1_rc[3];
    z1_rc[0] = Num2Bits(n);  z1_rc[0].in <== z1_abs[0];
    z1_rc[1] = Num2Bits(n);  z1_rc[1].in <== z1_abs[1];
    z1_rc[2] = Num2Bits(EXTRA_BITS);  z1_rc[2].in <== z1_abs[2];
    for (var i = 3; i < k; i++) z1_abs[i] === 0;

    // Algebraic verification
    signal order_sig[k];
    signal lambda_sig[k];
    for (var i = 0; i < k; i++) {
        order_sig[i] <== order_const[i];
        lambda_sig[i] <== lambda_const[i];
    }

    signal z1l[k];
    z1l <== BigMultModP(n, k)(z1_abs, lambda_sig, order_sig);

    signal x1l[k];
    x1l <== BigMultModP(n, k)(x1_abs, lambda_sig, order_sig);

    // z_comp witness
    signal z_comp[k];
    var z_comp_wit[30];
    for (var j = 0; j < 30; j++) z_comp_wit[j] = 0;

    var z1l_wit[30] = prod_mod_p_s(n, k, eis[3], lambda_const, order_const);
    var z0_sign_raw = 1 - eis[6][0];
    var z1_sign_raw = 1 - eis[7][0];
    var z0_term[30];
    for (var j = 0; j < 30; j++) z0_term[j] = 0;
    if (z0_sign_raw == 0) {
        for (var j = 0; j < k; j++) z0_term[j] = eis[2][j];
    } else {
        z0_term = long_sub_s(n, k, order_const, eis[2]);
    }
    var z1_term[30];
    for (var j = 0; j < 30; j++) z1_term[j] = 0;
    if (z1_sign_raw == 0) {
        for (var j = 0; j < k; j++) z1_term[j] = z1l_wit[j];
    } else {
        z1_term = long_sub_s(n, k, order_const, z1l_wit);
    }
    z_comp_wit = long_add_s(n, k, z0_term, z1_term);
    if (long_gt(n, k+1, z_comp_wit, order_const) == 1) {
        z_comp_wit = long_sub_s(n, k+1, z_comp_wit, order_const);
    }
    if (long_gt(n, k+1, z_comp_wit, order_const) == 1) {
        z_comp_wit = long_sub_s(n, k+1, z_comp_wit, order_const);
    }
    for (var j = 0; j < k; j++) z_comp[j] <-- z_comp_wit[j];

    component z_comp_rc[k];
    for (var i = 0; i < k; i++) {
        z_comp_rc[i] = Num2Bits(n);
        z_comp_rc[i].in <== z_comp[i];
    }

    // z_verify carry check
    // The constraint equation is:
    //   z_comp = (2s2-1)*z0_abs + (2s3-1)*z1l + z_q_adj*order
    // But z_q_adj = (2-s2-s3) - z_q_unsigned can be negative.
    // Bias by +2: z_q_biased = z_q_adj + 2 = 4 - s2 - s3 - z_q_unsigned ∈ [0,4]
    signal z_q;
    var z_q_unsigned = 0;
    var z_lhs[30] = long_add_s(n, k, z0_term, z1_term);
    if (long_gt(n, k+1, z_lhs, order_const) == 1) {
        z_q_unsigned = z_q_unsigned + 1;
        z_lhs = long_sub_s(n, k+1, z_lhs, order_const);
    }
    if (long_gt(n, k+1, z_lhs, order_const) == 1) {
        z_q_unsigned = z_q_unsigned + 1;
    }
    z_q <-- 4 - eis[6][0] - eis[7][0] - z_q_unsigned;
    signal _z_q_bits[3] <== Num2Bits(3)(z_q);

    signal neg_z0_z0[k];
    signal neg_z1_z1l[k];
    for (var i = 0; i < k; i++) {
        neg_z0_z0[i] <== (1 - s2) * z0_abs[i];
        neg_z1_z1l[i] <== (1 - s3) * z1l[i];
    }

    signal z_verify[k];
    for (var i = 0; i < k; i++) {
        z_verify[i] <== z_comp[i] + 2 * neg_z0_z0[i] + 2 * neg_z1_z1l[i]
                        - z0_abs[i] - z1l[i] - z_q * order_sig[i] + 2 * order_sig[i];
    }
    CheckCarryToZero(n, n + 4, k)(z_verify);

    // x_comp witness
    signal x_comp[k];
    var x_comp_wit[30];
    for (var j = 0; j < 30; j++) x_comp_wit[j] = 0;

    var x1l_wit[30] = prod_mod_p_s(n, k, eis[1], lambda_const, order_const);
    var x0_sign_raw = eis[4][0] ^ eis[8][0];
    var x1_sign_raw = eis[5][0] ^ eis[8][0];
    var x0_term[30];
    for (var j = 0; j < 30; j++) x0_term[j] = 0;
    if (x0_sign_raw == 0) {
        for (var j = 0; j < k; j++) x0_term[j] = eis[0][j];
    } else {
        x0_term = long_sub_s(n, k, order_const, eis[0]);
    }
    var x1_term[30];
    for (var j = 0; j < 30; j++) x1_term[j] = 0;
    if (x1_sign_raw == 0) {
        for (var j = 0; j < k; j++) x1_term[j] = x1l_wit[j];
    } else {
        x1_term = long_sub_s(n, k, order_const, x1l_wit);
    }
    x_comp_wit = long_add_s(n, k, x0_term, x1_term);
    if (long_gt(n, k+1, x_comp_wit, order_const) == 1) {
        x_comp_wit = long_sub_s(n, k+1, x_comp_wit, order_const);
    }
    if (long_gt(n, k+1, x_comp_wit, order_const) == 1) {
        x_comp_wit = long_sub_s(n, k+1, x_comp_wit, order_const);
    }
    for (var j = 0; j < k; j++) x_comp[j] <-- x_comp_wit[j];

    component x_comp_rc[k];
    for (var i = 0; i < k; i++) {
        x_comp_rc[i] = Num2Bits(n);
        x_comp_rc[i].in <== x_comp[i];
    }

    // x_verify carry check
    // Same biasing approach: x_q_biased = x0_sign_raw + x1_sign_raw + 2 - x_q_unsigned
    signal x0_neg;
    x0_neg <== s0 + sx - 2 * s0 * sx;
    signal x1_neg;
    x1_neg <== s1 + sx - 2 * s1 * sx;

    signal x_q;
    var x_lhs[30] = long_add_s(n, k, x0_term, x1_term);
    var x_q_unsigned = 0;
    if (long_gt(n, k+1, x_lhs, order_const) == 1) {
        x_q_unsigned = x_q_unsigned + 1;
        x_lhs = long_sub_s(n, k+1, x_lhs, order_const);
    }
    if (long_gt(n, k+1, x_lhs, order_const) == 1) {
        x_q_unsigned = x_q_unsigned + 1;
    }
    x_q <-- x0_sign_raw + x1_sign_raw + 2 - x_q_unsigned;
    signal _x_q_bits[3] <== Num2Bits(3)(x_q);

    signal x0_neg_x0[k];
    signal x1_neg_x1l[k];
    for (var i = 0; i < k; i++) {
        x0_neg_x0[i] <== x0_neg * x0_abs[i];
        x1_neg_x1l[i] <== x1_neg * x1l[i];
    }

    signal x_verify[k];
    for (var i = 0; i < k; i++) {
        x_verify[i] <== x_comp[i] + 2 * x0_neg_x0[i] + 2 * x1_neg_x1l[i]
                        - x0_abs[i] - x1l[i] - x_q * order_sig[i] + 2 * order_sig[i];
    }
    CheckCarryToZero(n, n + 4, k)(x_verify);

    // Algebraic check
    signal u[k];
    u <== BigMultModP(n, k)(scalar, z_comp, order_sig);

    signal order_minus_x[k];
    order_minus_x <== BigSub(n, k)(order_sig, x_comp);

    signal expected[k];
    for (var i = 0; i < k; i++) {
        expected[i] <== sx * (order_minus_x[i] - x_comp[i]) + x_comp[i];
    }
    signal u_eq_expected <== BigIsEqual(k)(u, expected);
    u_eq_expected === 1;

    // z_comp must be nonzero
    signal z_is_zero <== IsZero()(z_comp[0] + z_comp[1] + z_comp[2] + z_comp[3]
                                 + z_comp[4] + z_comp[5] + z_comp[6] + z_comp[7]);
    z_is_zero === 0;
}
