pragma circom 2.2.2;

include "arithmetic/bigint.circom";
include "arithmetic/bigint_func.circom";
include "core/comparators.circom";
include "packing/bitify.circom";
include "ecdsa/constants.circom";
include "ecdsa/point.circom";
include "ecdsa/scalarmul.circom";

// ═══════════════════════════════════════════════════
// ECDSA signature verification on secp256k1.
// Does NOT validate that pubkey is a valid curve point.
// ═══════════════════════════════════════════════════

/// Verifies an ECDSA signature (r, s) against a message hash and public key.
///
/// Algorithm:
///   1. sinv = s^(-1) mod order     (witness + constrain sinv*s ≡ 1)
///   2. u1   = msghash * sinv mod order
///   3. u2   = r * sinv mod order
///   4. R    = u1*G + u2*pubkey     (PrivToPub + ScalarMult + AddUnequal)
///   5. result = (R.x == r)
///
/// Inputs are k limbs of n bits, little-endian.
/// result = 1 if valid, 0 if invalid.
template ECDSAVerifyNoPubkeyCheck(n, k) {
    assert(n == 64 && k == 4);

    signal input r[k];
    signal input s[k];
    signal input msghash[k];
    signal input pubkey[2][k];
    signal output result;

    var order[200] = SECP256K1_ORDER(n, k);

    // ─── Step 1: Witness s^(-1) mod order ───

    var s_var[200];
    for (var i = 0; i < k; i++) s_var[i] = s[i];
    var sinv_comp[200] = mod_inv(n, k, s_var, order);

    signal sinv[k];
    component sinv_rc[k];
    for (var i = 0; i < k; i++) {
        sinv[i] <-- sinv_comp[i];
        sinv_rc[i] = Num2Bits(n);
        sinv_rc[i].in <== sinv[i];
    }

    // Constrain: sinv * s ≡ 1 (mod order)
    component sinv_check = BigMultModP(n, k);
    for (var i = 0; i < k; i++) {
        sinv_check.a[i] <== sinv[i];
        sinv_check.b[i] <== s[i];
        sinv_check.p[i] <== order[i];
    }
    sinv_check.out[0] === 1;
    for (var i = 1; i < k; i++) {
        sinv_check.out[i] === 0;
    }

    // ─── Step 2: u1 = msghash * sinv mod order ───

    component u1_comp = BigMultModP(n, k);
    for (var i = 0; i < k; i++) {
        u1_comp.a[i] <== sinv[i];
        u1_comp.b[i] <== msghash[i];
        u1_comp.p[i] <== order[i];
    }

    // ─── Step 3: u1 * G (fixed-base) ───

    component u1G = Secp256k1PrivToPub(n, k);
    for (var i = 0; i < k; i++) {
        u1G.privkey[i] <== u1_comp.out[i];
    }

    // ─── Step 4: u2 = r * sinv mod order ───

    component u2_comp = BigMultModP(n, k);
    for (var i = 0; i < k; i++) {
        u2_comp.a[i] <== sinv[i];
        u2_comp.b[i] <== r[i];
        u2_comp.p[i] <== order[i];
    }

    // ─── Step 5: u2 * pubkey (variable-base) ───

    component u2Pub = Secp256k1ScalarMult(n, k);
    for (var i = 0; i < k; i++) {
        u2Pub.scalar[i] <== u2_comp.out[i];
        u2Pub.point[0][i] <== pubkey[0][i];
        u2Pub.point[1][i] <== pubkey[1][i];
    }

    // ─── Step 6: R = u1*G + u2*pubkey ───

    component R = Secp256k1AddUnequal(n, k);
    for (var i = 0; i < k; i++) {
        R.a[0][i] <== u1G.pubkey[0][i];
        R.a[1][i] <== u1G.pubkey[1][i];
        R.b[0][i] <== u2Pub.out[0][i];
        R.b[1][i] <== u2Pub.out[1][i];
    }

    // ─── Step 7: result = (R.x == r) ───

    result <== BigIsEqual(k)(R.out[0], r);
}
