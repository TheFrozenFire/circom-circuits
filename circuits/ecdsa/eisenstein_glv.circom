pragma circom 2.2.2;

include "arithmetic/bigint.circom";
include "arithmetic/bigint_func.circom";
include "collections/multiplexer.circom";
include "core/comparators.circom";
include "packing/bitify.circom";
include "ecdsa/constants.circom";
include "ecdsa/functions.circom";
include "ecdsa/point.circom";

// ═══════════════════════════════════════════════════
// Eisenstein integer scalar multiplication on secp256k1.
// Based on "Fast elliptic curve scalar multiplications in SNARK circuits"
// (eprint 2025/933 §2.5/§3.3).
//
// Decomposes the scalar via Eisenstein half-GCD in Z[ω] (ω = e^{2πi/3})
// into 4 sub-scalars bounded by ~2^68, enabling MSM(4, 68).
//
// The algebraic identity: k·(z₀+z₁λ) ≡ ±(x₀+x₁λ) (mod order)
// maps to the geometric: [x₀]B0 + [x₁]B1 + [z₀]B2 + [z₁]B3 = O
// where B0..B3 are sign-adjusted versions of P, ψ(P), −Q, −ψ(Q).
// ═══════════════════════════════════════════════════

/// Eisenstein scalar multiplication: out = scalar * point on secp256k1.
///
/// The prover provides hint = [scalar]·point externally. The circuit verifies
/// via Eisenstein half-GCD decomposition + Pippenger MSM(4, 68) with offset.
///
/// Algorithm:
///   1. Verify hint is on curve
///   2. Eisenstein half-GCD: 4 sub-scalars < 2^68
///   3. Algebraic: k·(z₀+z₁λ) ≡ ±(x₀+x₁λ) (mod order)
///   4. Geometric: MSM(4, 68) with 16-entry Pippenger table
///
/// NOTE: Does not handle scalar = 0 or point = identity.
template Secp256k1EisensteinScalarMult(n, k) {
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

    // ───────────────────────────────────────────────
    // Phase 1: Verify hint Q is on curve
    // ───────────────────────────────────────────────

    Secp256k1PointOnCurve()(hint[0], hint[1]);
    CheckInRangeSecp256k1()(hint[0]);
    CheckInRangeSecp256k1()(hint[1]);

    for (var i = 0; i < k; i++) {
        out[0][i] <== hint[0][i];
        out[1][i] <== hint[1][i];
    }

    // ───────────────────────────────────────────────
    // Phase 2: Eisenstein decomposition verification
    //
    // Witness x0_abs, x1_abs, z0_abs, z1_abs (each < 2^68)
    // and sign bits s0..s3, sx.
    // Verify: scalar * z_comp ≡ expected (mod order)
    // ───────────────────────────────────────────────

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

    // Range-check each sub-scalar < 2^68:
    // Limbs 0,1: Num2Bits(32), Limb 2: Num2Bits(4), Limbs 3-7: === 0
    // (68 = 32 + 32 + 4)
    var EXTRA_BITS = NUM_BITS - 64;  // = 4

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

    // Algebraic verification: scalar * (z0 + z1*lambda) ≡ ±(x0 + x1*lambda) (mod order)
    signal order_sig[k];
    signal lambda_sig[k];
    for (var i = 0; i < k; i++) {
        order_sig[i] <== order_const[i];
        lambda_sig[i] <== lambda_const[i];
    }

    // z1_lambda = z1_abs * lambda mod order
    signal z1l[k];
    z1l <== BigMultModP(n, k)(z1_abs, lambda_sig, order_sig);

    // x1_lambda = x1_abs * lambda mod order
    signal x1l[k];
    x1l <== BigMultModP(n, k)(x1_abs, lambda_sig, order_sig);

    // z_comp = signed_add(z0_abs, sz0, z1l, sz1, order)
    // sz0 and sz1 come from s2/s3 but need to undo the Q negation baked into them.
    // The witness function already computes correct sign bits for the algebraic check:
    //   The raw Eisenstein signs are rc0s, rc1s, tc0s, tc1s
    //   s0..s3 include both component signs and Q negation.
    //
    // For algebraic verification, we use the raw component signs.
    // raw_tc0_sign = s2 XOR 1 (undo default Q negation) XOR (sx if overall flip applies to z)
    // Actually, the witness encodes: if relation is k*(z0+z1λ)≡+(x0+x1λ), default s2=1,s3=1
    // Component sign flips and overall sign flips are baked in.
    //
    // Simpler approach: witness z_comp and x_comp directly, verify with CheckCarryToZero.

    // Witness z_comp = z0_abs ± z1l mod order
    // and    x_comp = x0_abs ± x1l mod order
    // Then verify: scalar * z_comp ≡ expected (mod order)

    // For sign-handling: we witness the result and verify with carry check.
    // The Eisenstein decomposition gives us 4 absolute values + sign bits.
    // The algebraic relation uses the ORIGINAL (pre-sign-flip) component signs:
    //   x0_sign_raw = rc0s = s0 XOR sx (when sx=1, s0 was flipped)
    //   x1_sign_raw = rc1s = s1 XOR sx
    //   z0_sign_raw = tc0s = s2 XOR 1 (undo default negation)
    //   z1_sign_raw = tc1s = s3 XOR 1

    // Compute z_comp = (-1)^z0_raw * z0_abs + (-1)^z1_raw * z1l  (mod order)
    // = (-1)^(s2+1) * z0_abs + (-1)^(s3+1) * z1l  (mod order)
    //
    // Instead of complex sign logic, compute directly:
    // neg_z0 = (1-s2): when s2=1 (default), neg_z0=0 → z0 positive
    // neg_z1 = (1-s3): when s3=1 (default), neg_z1=0 → z1 positive

    // Witness z_comp as the result
    signal z_comp[k];
    var z_comp_wit[30];
    for (var j = 0; j < 30; j++) z_comp_wit[j] = 0;

    // Compute in witness: z_comp = ((-1)^(1-s2)*z0_abs + (-1)^(1-s3)*z1l) mod order
    // s2=1 default → 1-s2=0 → z0 positive (not negated)
    // If z0 was originally negative in Eisenstein: s2 gets flipped to 0, 1-s2=1 → z0 negated
    var z1l_wit[30] = prod_mod_p_s(n, k, eis[3], lambda_const, order_const);
    // term0 = z0_abs or order - z0_abs depending on sign
    var z0_sign_raw = 1 - eis[6][0];  // undo default Q negation
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
    // z_comp = (z0_term + z1_term) mod order
    z_comp_wit = long_add_s(n, k, z0_term, z1_term);
    if (long_gt(n, k+1, z_comp_wit, order_const) == 1) {
        z_comp_wit = long_sub_s(n, k+1, z_comp_wit, order_const);
    }
    // If still > order (can happen with double carry)
    if (long_gt(n, k+1, z_comp_wit, order_const) == 1) {
        z_comp_wit = long_sub_s(n, k+1, z_comp_wit, order_const);
    }
    for (var j = 0; j < k; j++) z_comp[j] <-- z_comp_wit[j];

    // Range-check z_comp limbs
    component z_comp_rc[k];
    for (var i = 0; i < k; i++) {
        z_comp_rc[i] = Num2Bits(n);
        z_comp_rc[i].in <== z_comp[i];
    }

    // Constrain z_comp: verify via carry check
    // Let neg_z0 = 1-s2, neg_z1 = 1-s3
    // Then: z_comp + neg_z0*z0_abs + neg_z1*z1l
    //      = (1-neg_z0)*z0_abs + (1-neg_z1)*z1l + q*order
    // Rearranging: z_comp = (1-2*neg_z0)*z0_abs + (1-2*neg_z1)*z1l - q*order (bad for carries)
    //
    // Better: z_comp + neg_z0*2*z0_abs + neg_z1*2*z1l = z0_abs + z1l + q*order
    // where q ∈ {0, 1, 2}

    // Witness z_q (biased quotient for signed carry check)
    // The constraint: z_comp = (2s2-1)*z0_abs + (2s3-1)*z1l + q_adj*order
    // where q_adj = (2-s2-s3) - q_unsigned can be negative.
    // Bias by +2: q_biased = q_adj + 2 = 4 - s2 - s3 - q_unsigned ∈ [0,4]
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

    // Now compute x_comp similarly
    signal x_comp[k];
    var x_comp_wit[30];
    for (var j = 0; j < 30; j++) x_comp_wit[j] = 0;

    var x1l_wit[30] = prod_mod_p_s(n, k, eis[1], lambda_const, order_const);
    var x0_sign_raw = eis[4][0] ^ eis[8][0];  // s0 XOR sx
    var x1_sign_raw = eis[5][0] ^ eis[8][0];  // s1 XOR sx
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

    // Constrain x_comp with same pattern
    // x0_sign_raw = s0 XOR sx. In R1CS: s0 + sx - 2*s0*sx
    signal x0_neg;
    x0_neg <== s0 + sx - 2 * s0 * sx;  // XOR
    signal x1_neg;
    x1_neg <== s1 + sx - 2 * s1 * sx;  // XOR

    // x_q biased quotient: x_q_biased = x0_sign_raw + x1_sign_raw + 2 - x_q_unsigned
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

    // Verify: scalar * z_comp ≡ ±x_comp (mod order)
    signal u[k];
    u <== BigMultModP(n, k)(scalar, z_comp, order_sig);

    // expected = sx ? (order - x_comp) : x_comp
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

    // ───────────────────────────────────────────────
    // Phase 3: Construct 4 signed base points
    //
    // B0 = (P.x, s0 ? neg_Py : P.y)         — x0 scalar on P
    // B1 = (ψ(P).x, s1 ? neg_Py : P.y)      — x1 scalar on ψ(P)
    // B2 = (Q.x, s2 ? neg_Qy : Q.y)         — z0 scalar on ±Q
    // B3 = (ψ(Q).x, s3 ? neg_Qy : Q.y)     — z1 scalar on ±ψ(Q)
    // ───────────────────────────────────────────────

    signal p_sig[k];
    signal beta_sig[k];
    var beta_const[8] = SECP256K1_BETA(n, k);
    for (var i = 0; i < k; i++) {
        p_sig[i] <== p_const[i];
        beta_sig[i] <== beta_const[i];
    }

    // Endomorphism: ψ(P).x = β·P.x mod p, ψ(P).y = P.y
    signal psiPx[k];
    psiPx <== BigMultModP(n, k)(beta_sig, point[0], p_sig);

    // Endomorphism: ψ(Q).x = β·Q.x mod p, ψ(Q).y = Q.y
    signal psiQx[k];
    psiQx <== BigMultModP(n, k)(beta_sig, hint[0], p_sig);

    // Negated y-coordinates
    signal neg_Py[k];
    var neg_Py_wit[30] = long_sub_s(n, k, p_const, point[1]);
    for (var i = 0; i < k; i++) neg_Py[i] <-- neg_Py_wit[i];
    component neg_Py_rc[k];
    for (var i = 0; i < k; i++) {
        neg_Py_rc[i] = Num2Bits(n);
        neg_Py_rc[i].in <== neg_Py[i];
    }
    signal neg_Py_check[k];
    for (var i = 0; i < k; i++) neg_Py_check[i] <== neg_Py[i] + point[1][i] - p_sig[i];
    CheckCarryToZero(n, n + 1, k)(neg_Py_check);

    signal neg_Qy[k];
    var neg_Qy_wit[30] = long_sub_s(n, k, p_const, hint[1]);
    for (var i = 0; i < k; i++) neg_Qy[i] <-- neg_Qy_wit[i];
    component neg_Qy_rc[k];
    for (var i = 0; i < k; i++) {
        neg_Qy_rc[i] = Num2Bits(n);
        neg_Qy_rc[i].in <== neg_Qy[i];
    }
    signal neg_Qy_check[k];
    for (var i = 0; i < k; i++) neg_Qy_check[i] <== neg_Qy[i] + hint[1][i] - p_sig[i];
    CheckCarryToZero(n, n + 1, k)(neg_Qy_check);

    // B0 = (P.x, s0 ? neg_Py : P.y)
    signal base0[2][k];
    for (var i = 0; i < k; i++) {
        base0[0][i] <== point[0][i];
        base0[1][i] <== s0 * (neg_Py[i] - point[1][i]) + point[1][i];
    }

    // B1 = (ψ(P).x, s1 ? neg_Py : P.y)
    signal base1[2][k];
    for (var i = 0; i < k; i++) {
        base1[0][i] <== psiPx[i];
        base1[1][i] <== s1 * (neg_Py[i] - point[1][i]) + point[1][i];
    }

    // B2 = (Q.x, s2 ? neg_Qy : Q.y)
    signal base2[2][k];
    for (var i = 0; i < k; i++) {
        base2[0][i] <== hint[0][i];
        base2[1][i] <== s2 * (neg_Qy[i] - hint[1][i]) + hint[1][i];
    }

    // B3 = (ψ(Q).x, s3 ? neg_Qy : Q.y)
    signal base3[2][k];
    for (var i = 0; i < k; i++) {
        base3[0][i] <== psiQx[i];
        base3[1][i] <== s3 * (neg_Qy[i] - hint[1][i]) + hint[1][i];
    }

    // ───────────────────────────────────────────────
    // Phase 4: Precompute 16-entry Pippenger table
    //
    // Index = x0_bit + 2·x1_bit + 4·z0_bit + 8·z1_bit
    //   0: DUMMY      4: B2        8: B3       12: B2+B3
    //   1: B0         5: B0+B2     9: B0+B3    13: B0+B2+B3
    //   2: B1         6: B1+B2    10: B1+B3    14: B1+B2+B3
    //   3: B0+B1      7: B0+B1+B2 11: B0+B1+B3 15: B0+B1+B2+B3
    // ───────────────────────────────────────────────

    var dummyVar[2][8] = SECP256K1_DUMMY(n, k);
    signal table[16][2][k];

    // Entry 0: DUMMY
    for (var i = 0; i < k; i++) {
        table[0][0][i] <== dummyVar[0][i];
        table[0][1][i] <== dummyVar[1][i];
    }

    // Entry 1: B0
    for (var i = 0; i < k; i++) {
        table[1][0][i] <== base0[0][i];
        table[1][1][i] <== base0[1][i];
    }

    // Entry 2: B1
    for (var i = 0; i < k; i++) {
        table[2][0][i] <== base1[0][i];
        table[2][1][i] <== base1[1][i];
    }

    // Entry 3: B0+B1
    signal t3[2][k];
    t3 <== Secp256k1AddUnequal(n, k)(base0, base1);
    for (var i = 0; i < k; i++) {
        table[3][0][i] <== t3[0][i];
        table[3][1][i] <== t3[1][i];
    }

    // Entry 4: B2
    for (var i = 0; i < k; i++) {
        table[4][0][i] <== base2[0][i];
        table[4][1][i] <== base2[1][i];
    }

    // Entry 5: B0+B2
    signal t5[2][k];
    t5 <== Secp256k1AddUnequal(n, k)(base0, base2);
    for (var i = 0; i < k; i++) {
        table[5][0][i] <== t5[0][i];
        table[5][1][i] <== t5[1][i];
    }

    // Entry 6: B1+B2
    signal t6[2][k];
    t6 <== Secp256k1AddUnequal(n, k)(base1, base2);
    for (var i = 0; i < k; i++) {
        table[6][0][i] <== t6[0][i];
        table[6][1][i] <== t6[1][i];
    }

    // Entry 7: B0+B1+B2
    signal t7[2][k];
    t7 <== Secp256k1AddUnequal(n, k)(t3, base2);
    for (var i = 0; i < k; i++) {
        table[7][0][i] <== t7[0][i];
        table[7][1][i] <== t7[1][i];
    }

    // Entry 8: B3
    for (var i = 0; i < k; i++) {
        table[8][0][i] <== base3[0][i];
        table[8][1][i] <== base3[1][i];
    }

    // Entry 9: B0+B3
    signal t9[2][k];
    t9 <== Secp256k1AddUnequal(n, k)(base0, base3);
    for (var i = 0; i < k; i++) {
        table[9][0][i] <== t9[0][i];
        table[9][1][i] <== t9[1][i];
    }

    // Entry 10: B1+B3
    signal t10[2][k];
    t10 <== Secp256k1AddUnequal(n, k)(base1, base3);
    for (var i = 0; i < k; i++) {
        table[10][0][i] <== t10[0][i];
        table[10][1][i] <== t10[1][i];
    }

    // Entry 11: B0+B1+B3
    signal t11[2][k];
    t11 <== Secp256k1AddUnequal(n, k)(t3, base3);
    for (var i = 0; i < k; i++) {
        table[11][0][i] <== t11[0][i];
        table[11][1][i] <== t11[1][i];
    }

    // Entry 12: B2+B3
    signal t12[2][k];
    t12 <== Secp256k1AddUnequal(n, k)(base2, base3);
    for (var i = 0; i < k; i++) {
        table[12][0][i] <== t12[0][i];
        table[12][1][i] <== t12[1][i];
    }

    // Entry 13: B0+B2+B3
    signal t13[2][k];
    t13 <== Secp256k1AddUnequal(n, k)(base0, t12);
    for (var i = 0; i < k; i++) {
        table[13][0][i] <== t13[0][i];
        table[13][1][i] <== t13[1][i];
    }

    // Entry 14: B1+B2+B3
    signal t14[2][k];
    t14 <== Secp256k1AddUnequal(n, k)(base1, t12);
    for (var i = 0; i < k; i++) {
        table[14][0][i] <== t14[0][i];
        table[14][1][i] <== t14[1][i];
    }

    // Entry 15: B0+B1+B2+B3
    signal t15[2][k];
    t15 <== Secp256k1AddUnequal(n, k)(t3, t12);
    for (var i = 0; i < k; i++) {
        table[15][0][i] <== t15[0][i];
        table[15][1][i] <== t15[1][i];
    }

    // ───────────────────────────────────────────────
    // Phase 5: MSM(4, 68) main loop with offset technique
    //
    // Accumulator starts at DUMMY. At each bit position (MSB to LSB):
    //   1. Build 4-bit selector from current bits of x0,x1,z0,z1
    //   2. Mux 16-entry table
    //   3. Double accumulator
    //   4. Add mux output (if sel != 0, else skip)
    //
    // After 68 iterations: accumulator = [2^68]·DUMMY = DUMMY_SHIFTED_68
    // ───────────────────────────────────────────────

    signal sel[NUM_BITS];
    signal partial[NUM_BITS + 1][2][k];
    component doublers[NUM_BITS];
    component adders[NUM_BITS];
    component muxes[NUM_BITS];
    component is_zero_sel[NUM_BITS];

    // Initialize accumulator with DUMMY
    for (var i = 0; i < k; i++) {
        partial[NUM_BITS][0][i] <== dummyVar[0][i];
        partial[NUM_BITS][1][i] <== dummyVar[1][i];
    }

    for (var idx = NUM_BITS - 1; idx >= 0; idx--) {
        // Build 4-bit selector from bit decompositions
        // Bits 0-31 from limb 0 (rc[0]), bits 32-63 from limb 1 (rc[1]),
        // bits 64-67 from limb 2 (rc[2])
        var limb_idx = idx \ n;
        var bit_pos = idx % n;

        if (limb_idx < 2) {
            sel[idx] <== x0_rc[limb_idx].out[bit_pos]
                       + 2 * x1_rc[limb_idx].out[bit_pos]
                       + 4 * z0_rc[limb_idx].out[bit_pos]
                       + 8 * z1_rc[limb_idx].out[bit_pos];
        } else {
            sel[idx] <== x0_rc[2].out[bit_pos]
                       + 2 * x1_rc[2].out[bit_pos]
                       + 4 * z0_rc[2].out[bit_pos]
                       + 8 * z1_rc[2].out[bit_pos];
        }

        is_zero_sel[idx] = IsZero();
        is_zero_sel[idx].in <== sel[idx];

        // 16-way mux for x and y coordinates
        muxes[idx] = DualMultiplexer(k, 16);
        muxes[idx].sel <== sel[idx];
        for (var j = 0; j < 16; j++) {
            for (var l = 0; l < k; l++) {
                muxes[idx].inp0[j][l] <== table[j][0][l];
                muxes[idx].inp1[j][l] <== table[j][1][l];
            }
        }

        // Double previous accumulator
        doublers[idx] = Secp256k1DoubleLoop(n, k);
        for (var l = 0; l < k; l++) {
            doublers[idx].in[0][l] <== partial[idx + 1][0][l];
            doublers[idx].in[1][l] <== partial[idx + 1][1][l];
        }

        // Add mux output to doubled accumulator
        adders[idx] = Secp256k1AddUnequalLoop(n, k);
        for (var l = 0; l < k; l++) {
            adders[idx].a[0][l] <== doublers[idx].out[0][l];
            adders[idx].a[1][l] <== doublers[idx].out[1][l];
            adders[idx].b[0][l] <== muxes[idx].out0[l];
            adders[idx].b[1][l] <== muxes[idx].out1[l];
        }

        // If sel==0: skip add (use doubled only). Otherwise: use added.
        for (var l = 0; l < k; l++) {
            partial[idx][0][l] <== (1 - is_zero_sel[idx].out) * (adders[idx].out[0][l] - doublers[idx].out[0][l]) + doublers[idx].out[0][l];
            partial[idx][1][l] <== (1 - is_zero_sel[idx].out) * (adders[idx].out[1][l] - doublers[idx].out[1][l]) + doublers[idx].out[1][l];
        }
    }

    // ───────────────────────────────────────────────
    // Phase 6: Final equality check
    // If the MSM relation holds, accumulator == DUMMY_SHIFTED_68
    // ───────────────────────────────────────────────

    var dummyShifted[2][8] = SECP256K1_DUMMY_SHIFTED_68(n, k);
    signal dummyShiftedSig[2][k];
    for (var i = 0; i < k; i++) {
        dummyShiftedSig[0][i] <== dummyShifted[0][i];
        dummyShiftedSig[1][i] <== dummyShifted[1][i];
    }

    signal eq_x <== BigIsEqual(k)(partial[0][0], dummyShiftedSig[0]);
    signal eq_y <== BigIsEqual(k)(partial[0][1], dummyShiftedSig[1]);
    eq_x === 1;
    eq_y === 1;
}
