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
