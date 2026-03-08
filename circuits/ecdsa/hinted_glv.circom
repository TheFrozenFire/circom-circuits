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
// Hinted GLV scalar multiplication on secp256k1.
// Based on "Fast elliptic curve scalar multiplications in SNARK circuits"
// (eprint 2025/933).
//
// Instead of computing [k]P via double-and-add, the prover hints Q=[k]P
// and the circuit verifies the relation using half-GCD decomposition
// and a single MSM(4, 64) via Pippenger with offset technique.
//
// Target: ~175K constraints vs ~270K for the original GLVScalarMult.
// ═══════════════════════════════════════════════════

/// Hinted GLV scalar multiplication: out = scalar * point on secp256k1.
///
/// The prover provides hint = [scalar]·point externally. The circuit verifies
/// the hint via half-GCD decomposition + Pippenger MSM(4, 64) with offset.
///
/// Algorithm:
///   1. Verify hint is on curve
///   2. Half-GCD: scalar·z ≡ x (mod order), |x|,|z| < 2^128
///   3. GLV decompose x → (x1, x2) and z → (z1, z2), each < 2^64
///   4. Verify [x1]P + [x2]φ(P) - [z1]Q - [z2]φ(Q) = O
///      via Pippenger MSM(4, 64) with offset technique
///
/// NOTE: Does not handle scalar = 0 or point = identity.
/// The caller must ensure scalar ∈ [1, order-1] and point is a valid curve point.
template Secp256k1HintedGLVScalarMult(n, k) {
    assert(n == 32 && k == 8);

    signal input scalar[k];
    signal input point[2][k];
    signal input hint[2][k];
    signal output out[2][k];

    var NUM_BITS = 64;
    var p_const[8] = SECP256K1_PRIME(n, k);
    var order_const[8] = SECP256K1_ORDER(n, k);
    var beta_const[8] = SECP256K1_BETA(n, k);

    // ───────────────────────────────────────────────
    // Phase 1: Verify hint Q is on curve
    // ───────────────────────────────────────────────

    Secp256k1PointOnCurve()(hint[0], hint[1]);
    CheckInRangeSecp256k1()(hint[0]);
    CheckInRangeSecp256k1()(hint[1]);

    // Output is the verified hint
    for (var i = 0; i < k; i++) {
        out[0][i] <== hint[0][i];
        out[1][i] <== hint[1][i];
    }

    // ───────────────────────────────────────────────
    // Phase 2: Half-GCD decomposition
    // scalar·z_abs ≡ ±x_abs (mod order), |x_abs|, |z_abs| < 2^128
    // ───────────────────────────────────────────────

    var hgcd[4][200] = half_gcd(n, k, scalar, order_const);

    signal x_abs[k];
    signal z_abs[k];
    signal sx;
    for (var i = 0; i < k; i++) {
        x_abs[i] <-- hgcd[0][i];
        z_abs[i] <-- hgcd[1][i];
    }
    sx <-- hgcd[2][0];
    sx * (sx - 1) === 0;

    // Range-check x_abs < 2^128: limbs 0-3 are 32-bit, limbs 4-7 are 0
    component x_rc[4];
    for (var i = 0; i < 4; i++) {
        x_rc[i] = Num2Bits(n);
        x_rc[i].in <== x_abs[i];
    }
    for (var i = 4; i < k; i++) x_abs[i] === 0;

    // Range-check z_abs < 2^128: same structure
    component z_rc[4];
    for (var i = 0; i < 4; i++) {
        z_rc[i] = Num2Bits(n);
        z_rc[i].in <== z_abs[i];
    }
    for (var i = 4; i < k; i++) z_abs[i] === 0;

    // z_abs must be nonzero (order is prime, so gcd(scalar, order) = 1)
    signal z_is_zero <== IsZero()(z_abs[0] + z_abs[1] + z_abs[2] + z_abs[3]);
    z_is_zero === 0;

    // Verify: scalar * z_abs ≡ ±x_abs (mod order)
    // Compute u = scalar * z_abs mod order
    signal order_sig[k];
    for (var i = 0; i < k; i++) order_sig[i] <== order_const[i];

    signal u[k];
    u <== BigMultModP(n, k)(scalar, z_abs, order_sig);

    // If sx=0: u == x_abs. If sx=1: u == order - x_abs.
    // Compute order - x_abs
    signal order_minus_x[k];
    order_minus_x <== BigSub(n, k)(order_sig, x_abs);

    // Select expected value: sx ? (order - x_abs) : x_abs
    signal expected[k];
    for (var i = 0; i < k; i++) {
        expected[i] <== sx * (order_minus_x[i] - x_abs[i]) + x_abs[i];
    }
    signal u_eq_expected <== BigIsEqual(k)(u, expected);
    u_eq_expected === 1;

    // ───────────────────────────────────────────────
    // Phase 3: GLV decomposition of x and z
    // x ≡ x1 + x2·λ (mod order), |x1|, |x2| < 2^64
    // z ≡ z1 + z2·λ (mod order), |z1|, |z2| < 2^64
    // ───────────────────────────────────────────────

    // Lambda constant
    var lambda_const[8];
    lambda_const[0] = 455327090;   lambda_const[1] = 3741488764;
    lambda_const[2] = 545351288;   lambda_const[3] = 305013482;
    lambda_const[4] = 2282906714;  lambda_const[5] = 2770738178;
    lambda_const[6] = 3227267296;  lambda_const[7] = 1399041356;

    signal lambda_sig[k];
    for (var i = 0; i < k; i++) lambda_sig[i] <== lambda_const[i];

    // --- Decompose x ---
    var x_decomp[4][200] = glv_decompose(n, k, x_abs);
    signal x1_abs[k];
    signal x2_abs[k];
    signal sx1, sx2;
    for (var i = 0; i < k; i++) {
        x1_abs[i] <-- x_decomp[0][i];
        x2_abs[i] <-- x_decomp[1][i];
    }
    sx1 <-- x_decomp[2][0];
    sx2 <-- x_decomp[3][0];
    sx1 * (sx1 - 1) === 0;
    sx2 * (sx2 - 1) === 0;

    // Range-check x1_abs < 2^64: limbs 0-1 are 32-bit, limbs 2-7 are 0
    component x1_rc[2];
    for (var i = 0; i < 2; i++) {
        x1_rc[i] = Num2Bits(n);
        x1_rc[i].in <== x1_abs[i];
    }
    for (var i = 2; i < k; i++) x1_abs[i] === 0;

    // Range-check x2_abs < 2^64
    component x2_rc[2];
    for (var i = 0; i < 2; i++) {
        x2_rc[i] = Num2Bits(n);
        x2_rc[i].in <== x2_abs[i];
    }
    for (var i = 2; i < k; i++) x2_abs[i] === 0;

    // Verify: x_abs ≡ x1 + x2·λ (mod order) with signs
    signal x2l[k];
    x2l <== BigMultModP(n, k)(x2_abs, lambda_sig, order_sig);

    signal sx1_x1[k];
    signal sx2_x2l[k];
    for (var i = 0; i < k; i++) {
        sx1_x1[i] <== sx1 * x1_abs[i];
        sx2_x2l[i] <== sx2 * x2l[i];
    }

    // Witness q for x decomposition
    var x2l_var[200] = prod_mod_p(n, k, x_decomp[1], lambda_const, order_const);
    var x_pos_limbs[200];
    var x_neg_limbs[200];
    for (var i = 0; i < 200; i++) { x_pos_limbs[i] = 0; x_neg_limbs[i] = 0; }
    for (var i = 0; i < k; i++) {
        x_pos_limbs[i] = x_abs[i] + 2 * x_decomp[2][0] * x_decomp[0][i]
                                   + 2 * x_decomp[3][0] * x2l_var[i];
        x_neg_limbs[i] = x_decomp[0][i] + x2l_var[i];
    }
    for (var i = 0; i < k; i++) {
        x_pos_limbs[i+1] = x_pos_limbs[i+1] + (x_pos_limbs[i] >> n);
        x_pos_limbs[i] = x_pos_limbs[i] % (1 << n);
    }
    for (var i = 0; i < k; i++) {
        x_neg_limbs[i+1] = x_neg_limbs[i+1] + (x_neg_limbs[i] >> n);
        x_neg_limbs[i] = x_neg_limbs[i] % (1 << n);
    }
    var xq_witness = 0;
    if (long_gt(n, k + 1, x_neg_limbs, x_pos_limbs) == 1) {
        var xd[200] = long_sub(n, k + 1, x_neg_limbs, x_pos_limbs);
        var xdv[2][200] = long_div2(n, k, 1, xd, order_const);
        xq_witness = 0 - xdv[0][0];
    } else {
        var xd[200] = long_sub(n, k + 1, x_pos_limbs, x_neg_limbs);
        var xdv[2][200] = long_div2(n, k, 1, xd, order_const);
        xq_witness = xdv[0][0];
    }

    signal xq_pos, xq_neg;
    if (xq_witness >= 0) {
        xq_pos <-- xq_witness;
        xq_neg <-- 0;
    } else {
        xq_pos <-- 0;
        xq_neg <-- 0 - xq_witness;
    }
    signal _xq_pos_bits[2] <== Num2Bits(2)(xq_pos);
    xq_neg * (xq_neg - 1) === 0;
    xq_pos * xq_neg === 0;

    signal xq_order[k];
    for (var i = 0; i < k; i++) {
        xq_order[i] <== (xq_pos - xq_neg) * order_sig[i];
    }

    signal x_verify_diff[k];
    for (var i = 0; i < k; i++) {
        x_verify_diff[i] <== x_abs[i] + 2 * sx1_x1[i] + 2 * sx2_x2l[i]
                           - x1_abs[i] - x2l[i] - xq_order[i];
    }
    CheckCarryToZero(n, n + 4, k)(x_verify_diff);

    // --- Decompose z ---
    var z_decomp[4][200] = glv_decompose(n, k, z_abs);
    signal z1_abs[k];
    signal z2_abs[k];
    signal sz1, sz2;
    for (var i = 0; i < k; i++) {
        z1_abs[i] <-- z_decomp[0][i];
        z2_abs[i] <-- z_decomp[1][i];
    }
    sz1 <-- z_decomp[2][0];
    sz2 <-- z_decomp[3][0];
    sz1 * (sz1 - 1) === 0;
    sz2 * (sz2 - 1) === 0;

    // Range-check z1_abs < 2^64
    component z1_rc[2];
    for (var i = 0; i < 2; i++) {
        z1_rc[i] = Num2Bits(n);
        z1_rc[i].in <== z1_abs[i];
    }
    for (var i = 2; i < k; i++) z1_abs[i] === 0;

    // Range-check z2_abs < 2^64
    component z2_rc[2];
    for (var i = 0; i < 2; i++) {
        z2_rc[i] = Num2Bits(n);
        z2_rc[i].in <== z2_abs[i];
    }
    for (var i = 2; i < k; i++) z2_abs[i] === 0;

    // Verify: z_abs ≡ z1 + z2·λ (mod order) with signs
    signal z2l[k];
    z2l <== BigMultModP(n, k)(z2_abs, lambda_sig, order_sig);

    signal sz1_z1[k];
    signal sz2_z2l[k];
    for (var i = 0; i < k; i++) {
        sz1_z1[i] <== sz1 * z1_abs[i];
        sz2_z2l[i] <== sz2 * z2l[i];
    }

    var z2l_var[200] = prod_mod_p(n, k, z_decomp[1], lambda_const, order_const);
    var z_pos_limbs[200];
    var z_neg_limbs[200];
    for (var i = 0; i < 200; i++) { z_pos_limbs[i] = 0; z_neg_limbs[i] = 0; }
    for (var i = 0; i < k; i++) {
        z_pos_limbs[i] = z_abs[i] + 2 * z_decomp[2][0] * z_decomp[0][i]
                                   + 2 * z_decomp[3][0] * z2l_var[i];
        z_neg_limbs[i] = z_decomp[0][i] + z2l_var[i];
    }
    for (var i = 0; i < k; i++) {
        z_pos_limbs[i+1] = z_pos_limbs[i+1] + (z_pos_limbs[i] >> n);
        z_pos_limbs[i] = z_pos_limbs[i] % (1 << n);
    }
    for (var i = 0; i < k; i++) {
        z_neg_limbs[i+1] = z_neg_limbs[i+1] + (z_neg_limbs[i] >> n);
        z_neg_limbs[i] = z_neg_limbs[i] % (1 << n);
    }
    var zq_witness = 0;
    if (long_gt(n, k + 1, z_neg_limbs, z_pos_limbs) == 1) {
        var zd[200] = long_sub(n, k + 1, z_neg_limbs, z_pos_limbs);
        var zdv[2][200] = long_div2(n, k, 1, zd, order_const);
        zq_witness = 0 - zdv[0][0];
    } else {
        var zd[200] = long_sub(n, k + 1, z_pos_limbs, z_neg_limbs);
        var zdv[2][200] = long_div2(n, k, 1, zd, order_const);
        zq_witness = zdv[0][0];
    }

    signal zq_pos, zq_neg;
    if (zq_witness >= 0) {
        zq_pos <-- zq_witness;
        zq_neg <-- 0;
    } else {
        zq_pos <-- 0;
        zq_neg <-- 0 - zq_witness;
    }
    signal _zq_pos_bits[2] <== Num2Bits(2)(zq_pos);
    zq_neg * (zq_neg - 1) === 0;
    zq_pos * zq_neg === 0;

    signal zq_order[k];
    for (var i = 0; i < k; i++) {
        zq_order[i] <== (zq_pos - zq_neg) * order_sig[i];
    }

    signal z_verify_diff[k];
    for (var i = 0; i < k; i++) {
        z_verify_diff[i] <== z_abs[i] + 2 * sz1_z1[i] + 2 * sz2_z2l[i]
                           - z1_abs[i] - z2l[i] - zq_order[i];
    }
    CheckCarryToZero(n, n + 4, k)(z_verify_diff);

    // ───────────────────────────────────────────────
    // Phase 4: Compute endomorphism and signed points
    //
    // We need 4 base points for the MSM:
    //   B0 = sign-adjusted P for x1 scalar
    //   B1 = sign-adjusted φ(P) for x2 scalar
    //   B2 = sign-adjusted (-Q) for z1 scalar
    //   B3 = sign-adjusted (-φ(Q)) for z2 scalar
    //
    // Net sign for each:
    //   B0: negate P.y iff sx XOR sx1 = 1
    //   B1: negate P.y iff sx XOR sx2 = 1
    //   B2: negate Q.y iff NOT(sz1) = 1 (start negated, then sign-adjust)
    //   B3: negate Q.y iff NOT(sz2) = 1
    //
    // The relation is: [x1]B0 + [x2]B1 + [z1]B2 + [z2]B3 = O
    // when scalar·z ≡ x (mod order).
    // ───────────────────────────────────────────────

    signal p_sig[k];
    signal beta_sig[k];
    for (var i = 0; i < k; i++) {
        p_sig[i] <== p_const[i];
        beta_sig[i] <== beta_const[i];
    }

    // Endomorphism x-coordinates: φ(P).x = β·P.x, φ(Q).x = β·Q.x
    signal phiP_x[k];
    phiP_x <== BigMultModP(n, k)(beta_sig, point[0], p_sig);

    signal phiQ_x[k];
    phiQ_x <== BigMultModP(n, k)(beta_sig, hint[0], p_sig);

    // Negated y-coordinates: neg_Py = p - P.y, neg_Qy = p - Q.y
    signal neg_Py[k];
    var neg_Py_wit[200] = long_sub(n, k, p_const, point[1]);
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
    var neg_Qy_wit[200] = long_sub(n, k, p_const, hint[1]);
    for (var i = 0; i < k; i++) neg_Qy[i] <-- neg_Qy_wit[i];
    component neg_Qy_rc[k];
    for (var i = 0; i < k; i++) {
        neg_Qy_rc[i] = Num2Bits(n);
        neg_Qy_rc[i].in <== neg_Qy[i];
    }
    signal neg_Qy_check[k];
    for (var i = 0; i < k; i++) neg_Qy_check[i] <== neg_Qy[i] + hint[1][i] - p_sig[i];
    CheckCarryToZero(n, n + 1, k)(neg_Qy_check);

    // Sign bits for each base point (XOR via a + b - 2ab)
    // B0 negate iff sx XOR sx1
    signal neg_b0 <== sx + sx1 - 2 * sx * sx1;
    // B1 negate iff sx XOR sx2
    signal neg_b1 <== sx + sx2 - 2 * sx * sx2;
    // B2 negate iff sz1 = 0 (we want -Q, then sign-adjust by sz1)
    signal neg_b2 <== 1 - sz1;
    // B3 negate iff sz2 = 0
    signal neg_b3 <== 1 - sz2;

    // Construct 4 base points
    signal base[4][2][k];
    for (var i = 0; i < k; i++) {
        // B0 = (P.x, neg_b0 ? neg_Py : P.y)
        base[0][0][i] <== point[0][i];
        base[0][1][i] <== neg_b0 * (neg_Py[i] - point[1][i]) + point[1][i];
        // B1 = (φ(P).x, neg_b1 ? neg_Py : P.y)
        base[1][0][i] <== phiP_x[i];
        base[1][1][i] <== neg_b1 * (neg_Py[i] - point[1][i]) + point[1][i];
        // B2 = (Q.x, neg_b2 ? neg_Qy : Q.y)
        base[2][0][i] <== hint[0][i];
        base[2][1][i] <== neg_b2 * (neg_Qy[i] - hint[1][i]) + hint[1][i];
        // B3 = (φ(Q).x, neg_b3 ? neg_Qy : Q.y)
        base[3][0][i] <== phiQ_x[i];
        base[3][1][i] <== neg_b3 * (neg_Qy[i] - hint[1][i]) + hint[1][i];
    }

    // ───────────────────────────────────────────────
    // Phase 5: Precompute 16-entry Pippenger table
    //
    // Entry idx = b0_bit + 2*b1_bit + 4*b2_bit + 8*b3_bit
    //   0: DUMMY (offset point)
    //   1: B0
    //   2: B1
    //   3: B0+B1
    //   4: B2
    //   5: B0+B2
    //   6: B1+B2
    //   7: B0+B1+B2
    //   8: B3
    //   9: B0+B3
    //  10: B1+B3
    //  11: B0+B1+B3
    //  12: B2+B3
    //  13: B0+B2+B3
    //  14: B1+B2+B3
    //  15: B0+B1+B2+B3
    // ───────────────────────────────────────────────

    var dummyVar[2][8] = SECP256K1_DUMMY(n, k);
    signal table[16][2][k];

    // Entry 0: DUMMY
    for (var i = 0; i < k; i++) {
        table[0][0][i] <== dummyVar[0][i];
        table[0][1][i] <== dummyVar[1][i];
    }

    // Entries 1, 2, 4, 8: single base points
    for (var i = 0; i < k; i++) {
        table[1][0][i] <== base[0][0][i];
        table[1][1][i] <== base[0][1][i];
        table[2][0][i] <== base[1][0][i];
        table[2][1][i] <== base[1][1][i];
        table[4][0][i] <== base[2][0][i];
        table[4][1][i] <== base[2][1][i];
        table[8][0][i] <== base[3][0][i];
        table[8][1][i] <== base[3][1][i];
    }

    // Entry 3: B0+B1
    signal t3[2][k];
    t3 <== Secp256k1AddUnequal(n, k)(base[0], base[1]);
    for (var i = 0; i < k; i++) {
        table[3][0][i] <== t3[0][i];
        table[3][1][i] <== t3[1][i];
    }

    // Entry 5: B0+B2
    signal t5[2][k];
    t5 <== Secp256k1AddUnequal(n, k)(base[0], base[2]);
    for (var i = 0; i < k; i++) {
        table[5][0][i] <== t5[0][i];
        table[5][1][i] <== t5[1][i];
    }

    // Entry 6: B1+B2
    signal t6[2][k];
    t6 <== Secp256k1AddUnequal(n, k)(base[1], base[2]);
    for (var i = 0; i < k; i++) {
        table[6][0][i] <== t6[0][i];
        table[6][1][i] <== t6[1][i];
    }

    // Entry 7: B0+B1+B2 = t3+B2
    signal t7[2][k];
    t7 <== Secp256k1AddUnequal(n, k)(t3, base[2]);
    for (var i = 0; i < k; i++) {
        table[7][0][i] <== t7[0][i];
        table[7][1][i] <== t7[1][i];
    }

    // Entry 9: B0+B3
    signal t9[2][k];
    t9 <== Secp256k1AddUnequal(n, k)(base[0], base[3]);
    for (var i = 0; i < k; i++) {
        table[9][0][i] <== t9[0][i];
        table[9][1][i] <== t9[1][i];
    }

    // Entry 10: B1+B3
    signal t10[2][k];
    t10 <== Secp256k1AddUnequal(n, k)(base[1], base[3]);
    for (var i = 0; i < k; i++) {
        table[10][0][i] <== t10[0][i];
        table[10][1][i] <== t10[1][i];
    }

    // Entry 11: B0+B1+B3 = t3+B3
    signal t11[2][k];
    t11 <== Secp256k1AddUnequal(n, k)(t3, base[3]);
    for (var i = 0; i < k; i++) {
        table[11][0][i] <== t11[0][i];
        table[11][1][i] <== t11[1][i];
    }

    // Entry 12: B2+B3
    signal t12[2][k];
    t12 <== Secp256k1AddUnequal(n, k)(base[2], base[3]);
    for (var i = 0; i < k; i++) {
        table[12][0][i] <== t12[0][i];
        table[12][1][i] <== t12[1][i];
    }

    // Entry 13: B0+B2+B3 = t5+B3
    signal t13[2][k];
    t13 <== Secp256k1AddUnequal(n, k)(t5, base[3]);
    for (var i = 0; i < k; i++) {
        table[13][0][i] <== t13[0][i];
        table[13][1][i] <== t13[1][i];
    }

    // Entry 14: B1+B2+B3 = t6+B3
    signal t14[2][k];
    t14 <== Secp256k1AddUnequal(n, k)(t6, base[3]);
    for (var i = 0; i < k; i++) {
        table[14][0][i] <== t14[0][i];
        table[14][1][i] <== t14[1][i];
    }

    // Entry 15: B0+B1+B2+B3 = t7+B3
    signal t15[2][k];
    t15 <== Secp256k1AddUnequal(n, k)(t7, base[3]);
    for (var i = 0; i < k; i++) {
        table[15][0][i] <== t15[0][i];
        table[15][1][i] <== t15[1][i];
    }

    // ───────────────────────────────────────────────
    // Phase 6: MSM(4, 64) main loop with offset technique
    //
    // Accumulator starts at DUMMY. At each bit position (MSB to LSB):
    //   1. Double accumulator
    //   2. Mux table entry based on 4-bit selector
    //   3. Add mux output (if selector != 0, else skip via conditional mux)
    //
    // After 64 iterations, if the relation holds:
    //   accumulator = [2^64]·DUMMY + O = DUMMY_SHIFTED_64
    // ───────────────────────────────────────────────

    // Bit decomposition of x1_abs, x2_abs, z1_abs, z2_abs (each 2 limbs × 32 bits)
    component x1_bits[2];
    component x2_bits[2];
    component z1_bits[2];
    component z2_bits[2];
    for (var i = 0; i < 2; i++) {
        x1_bits[i] = Num2Bits(n);
        x1_bits[i].in <== x1_abs[i];
        x2_bits[i] = Num2Bits(n);
        x2_bits[i].in <== x2_abs[i];
        z1_bits[i] = Num2Bits(n);
        z1_bits[i].in <== z1_abs[i];
        z2_bits[i] = Num2Bits(n);
        z2_bits[i].in <== z2_abs[i];
    }

    // Main loop signals
    signal sel[NUM_BITS];
    signal partial[NUM_BITS + 1][2][k];
    component doublers[NUM_BITS];
    component adders[NUM_BITS];
    component mux_x[NUM_BITS];
    component mux_y[NUM_BITS];
    component is_zero_sel[NUM_BITS];
    signal intermed[NUM_BITS][2][k];

    // Initialize accumulator with DUMMY
    for (var i = 0; i < k; i++) {
        partial[NUM_BITS][0][i] <== dummyVar[0][i];
        partial[NUM_BITS][1][i] <== dummyVar[1][i];
    }

    for (var idx = NUM_BITS - 1; idx >= 0; idx--) {
        // Build 4-bit selector from current bit of each sub-scalar
        var limb_idx = idx \ n;
        var bit_pos = idx % n;
        sel[idx] <== x1_bits[limb_idx].out[bit_pos]
                   + 2 * x2_bits[limb_idx].out[bit_pos]
                   + 4 * z1_bits[limb_idx].out[bit_pos]
                   + 8 * z2_bits[limb_idx].out[bit_pos];

        is_zero_sel[idx] = IsZero();
        is_zero_sel[idx].in <== sel[idx];

        // 16-way mux for x and y coordinates
        mux_x[idx] = Multiplexer(k, 16);
        mux_y[idx] = Multiplexer(k, 16);
        mux_x[idx].sel <== sel[idx];
        mux_y[idx].sel <== sel[idx];
        for (var j = 0; j < 16; j++) {
            for (var l = 0; l < k; l++) {
                mux_x[idx].inp[j][l] <== table[j][0][l];
                mux_y[idx].inp[j][l] <== table[j][1][l];
            }
        }

        // Double previous accumulator
        doublers[idx] = Secp256k1Double(n, k);
        for (var l = 0; l < k; l++) {
            doublers[idx].in[0][l] <== partial[idx + 1][0][l];
            doublers[idx].in[1][l] <== partial[idx + 1][1][l];
        }

        // Add mux output to doubled accumulator
        adders[idx] = Secp256k1AddUnequal(n, k);
        for (var l = 0; l < k; l++) {
            adders[idx].a[0][l] <== doublers[idx].out[0][l];
            adders[idx].a[1][l] <== doublers[idx].out[1][l];
            adders[idx].b[0][l] <== mux_x[idx].out[l];
            adders[idx].b[1][l] <== mux_y[idx].out[l];
        }

        // If sel==0: skip add (use doubled only). Otherwise: use added.
        for (var l = 0; l < k; l++) {
            intermed[idx][0][l] <== (1 - is_zero_sel[idx].out) * (adders[idx].out[0][l] - doublers[idx].out[0][l]) + doublers[idx].out[0][l];
            intermed[idx][1][l] <== (1 - is_zero_sel[idx].out) * (adders[idx].out[1][l] - doublers[idx].out[1][l]) + doublers[idx].out[1][l];
        }

        for (var l = 0; l < k; l++) {
            partial[idx][0][l] <== intermed[idx][0][l];
            partial[idx][1][l] <== intermed[idx][1][l];
        }
    }

    // ───────────────────────────────────────────────
    // Phase 7: Final equality check
    // If the MSM relation holds, accumulator == DUMMY_SHIFTED_64
    // ───────────────────────────────────────────────

    var dummyShifted[2][8] = SECP256K1_DUMMY_SHIFTED_64(n, k);
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
