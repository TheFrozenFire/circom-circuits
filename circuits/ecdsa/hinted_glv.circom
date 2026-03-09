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
// Hinted scalar multiplication on secp256k1.
// Based on "Fast elliptic curve scalar multiplications in SNARK circuits"
// (eprint 2025/933).
//
// Instead of computing [k]P via double-and-add, the prover hints Q=[k]P
// and the circuit verifies the relation using half-GCD decomposition
// and MSM(2, 128) via Pippenger with offset technique.
//
// Half-GCD gives scalar·z ≡ ±x (mod order) with |x|, |z| < 2^128.
// Verification: [x](±P) + [z](-Q) = O via 128-iteration MSM with
// 4-entry table {DUMMY, B0, B1, B0+B1}.
// ═══════════════════════════════════════════════════

/// Hinted scalar multiplication: out = scalar * point on secp256k1.
///
/// The prover provides hint = [scalar]·point externally. The circuit verifies
/// the hint via half-GCD decomposition + Pippenger MSM(2, 128) with offset.
///
/// Algorithm:
///   1. Verify hint is on curve
///   2. Half-GCD: scalar·z ≡ ±x (mod order), |x|,|z| < 2^128
///   3. Verify [x](±P) + [z](-Q) = O
///      via MSM(2, 128) with offset technique
///
/// NOTE: Does not handle scalar = 0 or point = identity.
/// The caller must ensure scalar ∈ [1, order-1] and point is a valid curve point.
template Secp256k1HintedGLVScalarMult(n, k) {
    assert(n == 32 && k == 8);

    signal input scalar[k];
    signal input point[2][k];
    signal input hint[2][k];
    signal output out[2][k];

    var NUM_BITS = 128;
    var p_const[8] = SECP256K1_PRIME(n, k);
    var order_const[8] = SECP256K1_ORDER(n, k);

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
    // Phase 3: Compute signed base points
    //
    // We need 2 base points for the MSM:
    //   B0 = sign-adjusted P for x_abs scalar
    //   B1 = -Q (always negated for z_abs scalar)
    //
    // The relation [x_abs]P - [z_abs]Q = O when sx=0,
    // or [x_abs](-P) - [z_abs]Q = O when sx=1.
    //
    // So: B0.y = sx ? (p - P.y) : P.y
    //     B1.y = p - Q.y (always negated)
    // ───────────────────────────────────────────────

    signal p_sig[k];
    for (var i = 0; i < k; i++) p_sig[i] <== p_const[i];

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

    // B0 = (P.x, sx ? neg_Py : P.y)
    signal base0[2][k];
    for (var i = 0; i < k; i++) {
        base0[0][i] <== point[0][i];
        base0[1][i] <== sx * (neg_Py[i] - point[1][i]) + point[1][i];
    }

    // B1 = (Q.x, neg_Qy) — always negated
    signal base1[2][k];
    for (var i = 0; i < k; i++) {
        base1[0][i] <== hint[0][i];
        base1[1][i] <== neg_Qy[i];
    }

    // ───────────────────────────────────────────────
    // Phase 4: Precompute 4-entry Pippenger table
    //
    // Entry idx = x_bit + 2*z_bit
    //   0: DUMMY (offset point)
    //   1: B0
    //   2: B1
    //   3: B0+B1
    // ───────────────────────────────────────────────

    var dummyVar[2][8] = SECP256K1_DUMMY(n, k);
    signal table[4][2][k];

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

    // ───────────────────────────────────────────────
    // Phase 5: MSM(2, 128) main loop with offset technique
    //
    // Accumulator starts at DUMMY. At each bit position (MSB to LSB):
    //   1. Double accumulator
    //   2. Mux table entry based on 2-bit selector
    //   3. Add mux output (if selector != 0, else skip via conditional mux)
    //
    // After 128 iterations, if the relation holds:
    //   accumulator = [2^128]·DUMMY + O = DUMMY_SHIFTED_128
    // ───────────────────────────────────────────────

    // Reuse Phase 2 Num2Bits outputs (x_rc, z_rc) as bit decompositions

    // Main loop signals
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
        // Build 2-bit selector from current bit of x_abs and z_abs
        var limb_idx = idx \ n;
        var bit_pos = idx % n;
        sel[idx] <== x_rc[limb_idx].out[bit_pos]
                   + 2 * z_rc[limb_idx].out[bit_pos];

        is_zero_sel[idx] = IsZero();
        is_zero_sel[idx].in <== sel[idx];

        // 4-way mux for x and y coordinates — shared Decoder
        muxes[idx] = DualMultiplexer(k, 4);
        muxes[idx].sel <== sel[idx];
        for (var j = 0; j < 4; j++) {
            for (var l = 0; l < k; l++) {
                muxes[idx].inp0[j][l] <== table[j][0][l];
                muxes[idx].inp1[j][l] <== table[j][1][l];
            }
        }

        // Double previous accumulator (loop-optimized: no < p canonicality)
        doublers[idx] = Secp256k1DoubleLoop(n, k);
        for (var l = 0; l < k; l++) {
            doublers[idx].in[0][l] <== partial[idx + 1][0][l];
            doublers[idx].in[1][l] <== partial[idx + 1][1][l];
        }

        // Add mux output to doubled accumulator (loop-optimized)
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
    // If the MSM relation holds, accumulator == DUMMY_SHIFTED_128
    // ───────────────────────────────────────────────

    var dummyShifted[2][8] = SECP256K1_DUMMY_SHIFTED_128(n, k);
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
