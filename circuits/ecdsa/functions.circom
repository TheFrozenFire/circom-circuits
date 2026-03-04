pragma circom 2.2.2;

include "arithmetic/bigint_func.circom";
include "ecdsa/constants.circom";

/// Point addition for two distinct points on secp256k1.
/// λ = (y2 - y1) / (x2 - x1) mod p
/// x3 = λ² - x1 - x2 mod p
/// y3 = λ(x1 - x3) - y1 mod p
function secp256k1_addunequal_func(n, k, x1, y1, x2, y2) {
    var out[2][200];
    var p[200] = SECP256K1_PRIME(n, k);

    // λ = (y2 - y1) * (x2 - x1)^(-1)
    var dy[200] = long_sub_mod_p(n, k, y2, y1, p);
    var dx[200] = long_sub_mod_p(n, k, x2, x1, p);
    var dx_inv[200] = mod_inv(n, k, dx, p);
    var lambda[200] = prod_mod_p(n, k, dy, dx_inv, p);

    // x3 = λ² - x1 - x2
    var lsq[200] = prod_mod_p(n, k, lambda, lambda, p);
    var x3_tmp[200] = long_sub_mod_p(n, k, lsq, x1, p);
    var x3[200] = long_sub_mod_p(n, k, x3_tmp, x2, p);
    for (var i = 0; i < k; i++) out[0][i] = x3[i];

    // y3 = λ(x1 - x3) - y1
    var x1_minus_x3[200] = long_sub_mod_p(n, k, x1, x3, p);
    var lx[200] = prod_mod_p(n, k, lambda, x1_minus_x3, p);
    var y3[200] = long_sub_mod_p(n, k, lx, y1, p);
    for (var i = 0; i < k; i++) out[1][i] = y3[i];

    return out;
}

/// Point doubling on secp256k1.
/// λ = 3x1² / (2y1) mod p  (a=0 for secp256k1)
/// x3 = λ² - 2x1 mod p
/// y3 = λ(x1 - x3) - y1 mod p
function secp256k1_double_func(n, k, x1, y1) {
    var out[2][200];
    var p[200] = SECP256K1_PRIME(n, k);

    // λ = 3x1² / (2y1)
    var x1sq[200] = prod_mod_p(n, k, x1, x1, p);
    var three[200];
    for (var i = 0; i < 200; i++) three[i] = 0;
    three[0] = 3;
    var numer[200] = prod_mod_p(n, k, x1sq, three, p);

    var two[200];
    for (var i = 0; i < 200; i++) two[i] = 0;
    two[0] = 2;
    var denom[200] = prod_mod_p(n, k, y1, two, p);
    var denom_inv[200] = mod_inv(n, k, denom, p);
    var lambda[200] = prod_mod_p(n, k, numer, denom_inv, p);

    // x3 = λ² - 2x1
    var lsq[200] = prod_mod_p(n, k, lambda, lambda, p);
    var x3_tmp[200] = long_sub_mod_p(n, k, lsq, x1, p);
    var x3[200] = long_sub_mod_p(n, k, x3_tmp, x1, p);
    for (var i = 0; i < k; i++) out[0][i] = x3[i];

    // y3 = λ(x1 - x3) - y1
    var x1_minus_x3[200] = long_sub_mod_p(n, k, x1, x3, p);
    var lx[200] = prod_mod_p(n, k, lambda, x1_minus_x3, p);
    var y3[200] = long_sub_mod_p(n, k, lx, y1, p);
    for (var i = 0; i < k; i++) out[1][i] = y3[i];

    return out;
}

/// GLV scalar decomposition: k = k1 + k2·λ (mod n) with |k1|, |k2| < 2^129.
/// Uses Babai's nearest-plane algorithm on the GLV lattice for secp256k1.
/// Returns out[4][200]:
///   out[0] = |k1| (k limbs, zero-padded)
///   out[1] = |k2| (k limbs, zero-padded)
///   out[2][0] = s1 (1 if k1 is negative, 0 if positive)
///   out[3][0] = s2 (1 if k2 is negative, 0 if positive)
function glv_decompose(n, k, scalar) {
    assert(n == 32 && k == 8);

    var out[4][200];
    for (var i = 0; i < 4; i++)
        for (var j = 0; j < 200; j++) out[i][j] = 0;

    var order[200] = SECP256K1_ORDER(n, k);

    // GLV lattice basis constants (32-bit LE limbs).
    // v1 = (a1, -b1_abs), v2 = (a2, a1) span the kernel lattice of
    // the map (k1,k2) → k1 + k2·λ mod n.
    // a1 = 0x3086D221A7D46BCDE86C90E49284EB15  (126 bits)
    var a1[200];
    for (var i = 0; i < 200; i++) a1[i] = 0;
    a1[0] = 2458184469;  a1[1] = 3899429092;
    a1[2] = 2815716301;  a1[3] = 814141985;

    // |b1| = 0xE4437ED6010E88286F547FA90ABFE4C3  (128 bits)
    var b1_abs[200];
    for (var i = 0; i < 200; i++) b1_abs[i] = 0;
    b1_abs[0] = 180348099;   b1_abs[1] = 1867808681;
    b1_abs[2] = 17729576;    b1_abs[3] = 3829628630;

    // λ = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
    var lam[200];
    for (var i = 0; i < 200; i++) lam[i] = 0;
    lam[0] = 455327090;   lam[1] = 3741488764;
    lam[2] = 545351288;   lam[3] = 305013482;
    lam[4] = 2282906714;  lam[5] = 2770738178;
    lam[6] = 3227267296;  lam[7] = 1399041356;

    // Step 1: c1 = floor(a1 · scalar / order)
    var a1s[200] = prod(n, k, a1, scalar);
    var div1[2][200] = long_div2(n, k, k, a1s, order);

    // Step 2: c2 = floor(|b1| · scalar / order)
    var b1s[200] = prod(n, k, b1_abs, scalar);
    var div2[2][200] = long_div2(n, k, k, b1s, order);

    // Step 3: k2 = c1·|b1| − c2·a1  (with sign tracking)
    var c1b1[200] = prod(n, k, div1[0], b1_abs);
    var c2a1[200] = prod(n, k, div2[0], a1);

    var s2 = 0;
    var k2_abs[200];
    for (var i = 0; i < 200; i++) k2_abs[i] = 0;
    if (long_gt(n, k, c1b1, c2a1) == 1) {
        k2_abs = long_sub(n, k, c1b1, c2a1);
    } else if (long_gt(n, k, c2a1, c1b1) == 1) {
        k2_abs = long_sub(n, k, c2a1, c1b1);
        s2 = 1;
    }
    // else: k2 = 0, s2 = 0

    // Step 4: k1 = scalar − k2·λ mod order  (using signs)
    // If s2=0 (k2 positive): k1 = scalar − |k2|·λ mod order
    // If s2=1 (k2 negative): k1 = scalar + |k2|·λ mod order
    var k2l[200] = prod_mod_p(n, k, k2_abs, lam, order);

    var k1_mod[200];
    for (var i = 0; i < 200; i++) k1_mod[i] = 0;
    if (s2 == 0) {
        k1_mod = long_sub_mod_p(n, k, scalar, k2l, order);
    } else {
        // scalar + k2l mod order = scalar − (order − k2l) mod order
        var neg_k2l[200] = long_sub(n, k, order, k2l);
        k1_mod = long_sub_mod_p(n, k, scalar, neg_k2l, order);
    }

    // Determine sign: if k1_mod has significant upper limbs, it's n − |k1|
    var s1 = 0;
    for (var i = 5; i < k; i++) {
        if (k1_mod[i] != 0) s1 = 1;
    }

    var k1_abs[200];
    for (var i = 0; i < 200; i++) k1_abs[i] = 0;
    if (s1 == 1) {
        k1_abs = long_sub(n, k, order, k1_mod);
    } else {
        for (var i = 0; i < k; i++) k1_abs[i] = k1_mod[i];
    }

    for (var i = 0; i < k; i++) {
        out[0][i] = k1_abs[i];
        out[1][i] = k2_abs[i];
    }
    out[2][0] = s1;
    out[3][0] = s2;

    return out;
}

/// Endomorphism: φ(x, y) = (β·x mod p, y).
/// Returns β·x mod p as a k-limb array.
function secp256k1_endomorphism_func(n, k, x) {
    var p[200] = SECP256K1_PRIME(n, k);
    var beta[200] = SECP256K1_BETA(n, k);
    return prod_mod_p(n, k, beta, x, p);
}
