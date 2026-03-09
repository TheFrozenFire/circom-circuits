pragma circom 2.2.2;

include "arithmetic/bigint_func.circom";
include "ecdsa/constants.circom";

/// Point addition for two distinct points on secp256k1.
/// Returns out[3][200]: out[0] = x3, out[1] = y3, out[2] = λ (slope).
/// λ = (y2 - y1) / (x2 - x1) mod p
/// x3 = λ² - x1 - x2 mod p
/// y3 = λ(x1 - x3) - y1 mod p
function secp256k1_addunequal_func(n, k, x1, y1, x2, y2) {
    var out[3][200];
    for (var i = 0; i < 3; i++)
        for (var j = 0; j < 200; j++) out[i][j] = 0;

    var p[200] = SECP256K1_PRIME(n, k);

    // λ = (y2 - y1) * (x2 - x1)^(-1)
    var dy[200] = long_sub_mod_p(n, k, y2, y1, p);
    var dx[200] = long_sub_mod_p(n, k, x2, x1, p);
    var dx_inv[200] = mod_inv(n, k, dx, p);
    var lambda[200] = prod_mod_p(n, k, dy, dx_inv, p);
    for (var i = 0; i < k; i++) out[2][i] = lambda[i];

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
/// Returns out[3][200]: out[0] = x3, out[1] = y3, out[2] = λ (tangent slope).
/// λ = 3x1² / (2y1) mod p  (a=0 for secp256k1)
/// x3 = λ² - 2x1 mod p
/// y3 = λ(x1 - x3) - y1 mod p
function secp256k1_double_func(n, k, x1, y1) {
    var out[3][200];
    for (var i = 0; i < 3; i++)
        for (var j = 0; j < 200; j++) out[i][j] = 0;

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
    for (var i = 0; i < k; i++) out[2][i] = lambda[i];

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

/// Multi-limb addition: out = a + b (k-limb, n-bit). Returns (k+1)-limb result.
function long_add(n, k, a, b) {
    var out[200];
    for (var i = 0; i < 200; i++) out[i] = 0;
    var carry = 0;
    for (var i = 0; i < k; i++) {
        var s = a[i] + b[i] + carry;
        out[i] = s % (1 << n);
        carry = s \ (1 << n);
    }
    out[k] = carry;
    return out;
}

/// Scalar multiplication on secp256k1 (witness computation only).
/// Returns Q = [scalar]·P as out[2][200] (x, y in k limbs each).
/// scalar is a k-limb number, point is (px, py) each k limbs.
function secp256k1_scalar_mul_func(n, k, scalar, px, py) {
    var out[2][200];
    for (var i = 0; i < 2; i++)
        for (var j = 0; j < 200; j++) out[i][j] = 0;

    var acc_x[200];
    var acc_y[200];
    for (var j = 0; j < 200; j++) { acc_x[j] = 0; acc_y[j] = 0; }

    var first = 1;
    for (var bit_idx = n * k - 1; bit_idx >= 0; bit_idx--) {
        var limb_idx = bit_idx \ n;
        var bit_pos = bit_idx % n;
        var bit = (scalar[limb_idx] >> bit_pos) & 1;

        if (first == 0) {
            var doubled[3][200] = secp256k1_double_func(n, k, acc_x, acc_y);
            for (var j = 0; j < k; j++) { acc_x[j] = doubled[0][j]; acc_y[j] = doubled[1][j]; }
        }

        if (bit == 1) {
            if (first == 1) {
                for (var j = 0; j < k; j++) { acc_x[j] = px[j]; acc_y[j] = py[j]; }
                first = 0;
            } else {
                var added[3][200] = secp256k1_addunequal_func(n, k, acc_x, acc_y, px, py);
                for (var j = 0; j < k; j++) { acc_x[j] = added[0][j]; acc_y[j] = added[1][j]; }
            }
        }
    }

    for (var j = 0; j < k; j++) { out[0][j] = acc_x[j]; out[1][j] = acc_y[j]; }
    return out;
}

/// Half-GCD: find (x, z) with scalar·z ≡ x (mod order), |x|, |z| < 2^128.
/// Uses partial extended Euclidean algorithm (Lehmer-style).
/// Returns out[4][200]:
///   out[0] = x_abs (k limbs)
///   out[1] = z_abs (k limbs)
///   out[2][0] = sx (1 if scalar·z_abs ≡ -x_abs mod order, 0 if ≡ +x_abs)
///   out[3][0] = sz (always 0; z_abs is always positive)
function half_gcd(n, k, scalar, order) {
    assert(n == 32 && k == 8);

    var out[4][200];
    for (var i = 0; i < 4; i++)
        for (var j = 0; j < 200; j++) out[i][j] = 0;

    // Extended GCD: r_i = s_i * order + t_i * scalar
    // We track r (remainder, always >= 0) and t (coefficient of scalar, signed)
    var r_prev[200];
    var r_curr[200];
    for (var i = 0; i < 200; i++) { r_prev[i] = 0; r_curr[i] = 0; }
    for (var i = 0; i < k; i++) { r_prev[i] = order[i]; r_curr[i] = scalar[i]; }

    var t_prev_abs[200];
    var t_curr_abs[200];
    for (var i = 0; i < 200; i++) { t_prev_abs[i] = 0; t_curr_abs[i] = 0; }
    var t_prev_sign = 0;
    var t_curr_sign = 0;
    // t_0 = 0, t_1 = 1
    t_curr_abs[0] = 1;

    // bound = 2^128 (limb 4 = 1, all others 0)
    var bound[200];
    for (var i = 0; i < 200; i++) bound[i] = 0;
    bound[4] = 1;

    var done = 0;
    // Extended GCD loop — at most ~256 iterations for 256-bit inputs
    for (var iter = 0; iter < 300; iter++) {
        if (done == 0) {
            // Check if r_curr < bound (2^128)
            if (long_gt(n, k, bound, r_curr) == 1) {
                done = 1;
            } else {
                // q = floor(r_prev / r_curr), r_next = r_prev mod r_curr
                // Find effective number of limbs in r_curr (long_div2
                // requires the top limb of the divisor to be nonzero)
                var ek = 1;
                for (var j = 0; j < k; j++) {
                    if (r_curr[j] != 0) ek = j + 1;
                }
                // m = extra dividend limbs beyond ek
                var ek_prev = 1;
                for (var j = 0; j < k; j++) {
                    if (r_prev[j] != 0) ek_prev = j + 1;
                }
                var m = ek_prev - ek;
                if (m < 0) m = 0;

                var div[2][200] = long_div2(n, ek, m, r_prev, r_curr);
                var q[200];
                var r_next[200];
                for (var j = 0; j < 200; j++) { q[j] = 0; r_next[j] = 0; }
                for (var j = 0; j <= m; j++) q[j] = div[0][j];
                for (var j = 0; j < ek; j++) r_next[j] = div[1][j];

                // t_next = t_prev - q * t_curr (with sign handling)
                // qt = q * |t_curr| — full k×k multiplication since q may
                // exceed a single limb (e.g. first GCD step: order / 5 ≈ 2^254)
                var qt[200] = prod(n, k, q, t_curr_abs);

                var t_next_abs[200];
                for (var j = 0; j < 200; j++) t_next_abs[j] = 0;
                var t_next_sign = 0;

                if (t_prev_sign == t_curr_sign) {
                    // Same sign: t_next = |t_prev| - qt (may flip sign)
                    if (long_gt(n, 2 * k, t_prev_abs, qt) == 1) {
                        t_next_abs = long_sub(n, 2 * k, t_prev_abs, qt);
                        t_next_sign = t_prev_sign;
                    } else {
                        t_next_abs = long_sub(n, 2 * k, qt, t_prev_abs);
                        t_next_sign = 1 - t_prev_sign;
                    }
                } else {
                    // Opposite signs: t_next = |t_prev| + qt
                    t_next_abs = long_add(n, 2 * k, t_prev_abs, qt);
                    t_next_sign = t_prev_sign;
                }

                // Shift: prev <- curr, curr <- next
                for (var j = 0; j < 200; j++) {
                    r_prev[j] = r_curr[j];
                    r_curr[j] = r_next[j];
                    t_prev_abs[j] = t_curr_abs[j];
                    t_curr_abs[j] = t_next_abs[j];
                }
                t_prev_sign = t_curr_sign;
                t_curr_sign = t_next_sign;
            }
        }
    }

    // r_curr < 2^128 and r_curr = t_curr * scalar (mod order)
    // x = r_curr, z = |t_curr|
    for (var j = 0; j < k; j++) {
        out[0][j] = r_curr[j];
        out[1][j] = t_curr_abs[j];
    }

    // Determine sign relationship:
    // We have r_curr ≡ t_curr_signed * scalar (mod order)
    // where t_curr_signed = (-1)^t_curr_sign * |t_curr|
    // We want: scalar * z_abs ≡ ±x_abs (mod order)
    // z_abs = |t_curr|, x_abs = r_curr
    // scalar * z_abs = scalar * |t_curr|
    // If t_curr_sign == 0: scalar * |t_curr| ≡ r_curr (mod order) → sx = 0
    // If t_curr_sign == 1: scalar * |t_curr| ≡ -r_curr (mod order) → sx = 1
    out[2][0] = t_curr_sign;
    out[3][0] = 0;

    return out;
}

// ═══════════════════════════════════════════════════
// Slim (var[30]) arithmetic for Eisenstein GCD
// ═══════════════════════════════════════════════════
// Mirror the var[200] functions in bigint_func.circom but with var[30] arrays.
// This reduces WASM local count from ~44,000 to ~12,000, avoiding V8 limits.

/// Slim addition: out = a + b. Returns (k+1)-limb result in var[30].
function long_add_s(n, k, a, b) {
    var out[30];
    for (var i = 0; i < 30; i++) out[i] = 0;
    var carry = 0;
    for (var i = 0; i < k; i++) {
        var s = a[i] + b[i] + carry;
        out[i] = s % (1 << n);
        carry = s \ (1 << n);
    }
    out[k] = carry;
    return out;
}

/// Slim subtraction: out = a - b. Assumes a >= b. Returns k-limb result.
function long_sub_s(n, k, a, b) {
    var diff[30];
    for (var i = 0; i < 30; i++) diff[i] = 0;
    var borrow = 0;
    for (var i = 0; i < k; i++) {
        if (a[i] >= b[i] + borrow) {
            diff[i] = a[i] - b[i] - borrow;
            borrow = 0;
        } else {
            diff[i] = (1 << n) + a[i] - b[i] - borrow;
            borrow = 1;
        }
    }
    return diff;
}

/// Slim scalar multiply: out = a * b (a is single limb, b is k-limb).
function long_scalar_mult_s(n, k, a, b) {
    var out[30];
    for (var i = 0; i < 30; i++) out[i] = 0;
    for (var i = 0; i < k; i++) {
        var temp = out[i] + (a * b[i]);
        out[i] = temp % (1 << n);
        out[i + 1] = out[i + 1] + temp \ (1 << n);
    }
    return out;
}

/// Slim full multiplication: a * b (both k-limb). Returns 2k-limb result.
function prod_s(n, k, a, b) {
    var pv[30];
    for (var i = 0; i < 30; i++) pv[i] = 0;
    for (var i = 0; i < 2 * k - 1; i++) {
        if (i < k) {
            for (var a_idx = 0; a_idx <= i; a_idx++) {
                pv[i] = pv[i] + a[a_idx] * b[i - a_idx];
            }
        } else {
            for (var a_idx = i - k + 1; a_idx < k; a_idx++) {
                pv[i] = pv[i] + a[a_idx] * b[i - a_idx];
            }
        }
    }

    var out[30];
    for (var i = 0; i < 30; i++) out[i] = 0;
    var sp[30][3];
    for (var i = 0; i < 30; i++) for (var j = 0; j < 3; j++) sp[i][j] = 0;
    for (var i = 0; i < 2 * k - 1; i++) {
        sp[i] = SplitThreeFn(pv[i], n, n, n);
    }

    var carry = 0;
    out[0] = sp[0][0];
    if (2 * k - 1 > 1) {
        var sc[2] = SplitFn(sp[0][1] + sp[1][0], n, n);
        out[1] = sc[0];
        carry = sc[1];
    }
    if (2 * k - 1 > 2) {
        for (var i = 2; i < 2 * k - 1; i++) {
            var sc[2] = SplitFn(
                sp[i][0] + sp[i - 1][1] + sp[i - 2][2] + carry, n, n
            );
            out[i] = sc[0];
            carry = sc[1];
        }
        out[2 * k - 1] = sp[2 * k - 2][1] + sp[2 * k - 3][2] + carry;
    }
    return out;
}

/// Slim normalized short division.
function short_div_norm_s(n, k, a, b) {
    var qhat = (a[k] * (1 << n) + a[k - 1]) \ b[k - 1];
    if (qhat > (1 << n) - 1) qhat = (1 << n) - 1;
    var mult[30] = long_scalar_mult_s(n, k, qhat, b);
    if (long_gt(n, k + 1, mult, a) == 1) {
        mult = long_sub_s(n, k + 1, mult, b);
        if (long_gt(n, k + 1, mult, a) == 1) {
            return qhat - 2;
        } else {
            return qhat - 1;
        }
    }
    return qhat;
}

/// Slim short division.
function short_div_s(n, k, a, b) {
    var scale = (1 << n) \ (1 + b[k - 1]);
    var norm_a[30] = long_scalar_mult_s(n, k + 1, scale, a);
    var norm_b[30] = long_scalar_mult_s(n, k, scale, b);
    if (norm_b[k] != 0) {
        return short_div_norm_s(n, k + 1, norm_a, norm_b);
    } else {
        return short_div_norm_s(n, k, norm_a, norm_b);
    }
}

/// Slim long division: a has (k+m) limbs, b has k limbs.
/// Returns [quotient, remainder] as var[2][30].
function long_div2_s(n, k, m, a, b) {
    var out[2][30];
    for (var i = 0; i < 30; i++) { out[0][i] = 0; out[1][i] = 0; }

    var remainder[30];
    for (var i = 0; i < 30; i++) remainder[i] = 0;
    for (var i = 0; i < m + k; i++) remainder[i] = a[i];

    var dividend[30];
    for (var i = m; i >= 0; i--) {
        for (var j = 0; j < 30; j++) dividend[j] = 0;
        if (i == m) {
            dividend[k] = 0;
            for (var j = k - 1; j >= 0; j--) dividend[j] = remainder[j + m];
        } else {
            for (var j = k; j >= 0; j--) dividend[j] = remainder[j + i];
        }

        out[0][i] = short_div_s(n, k, dividend, b);

        var mult_shift[30] = long_scalar_mult_s(n, k, out[0][i], b);
        var subtrahend[30];
        for (var j = 0; j < 30; j++) subtrahend[j] = 0;
        for (var j = 0; j <= k; j++) {
            if (i + j < m + k) subtrahend[i + j] = mult_shift[j];
        }
        remainder = long_sub_s(n, m + k, remainder, subtrahend);
    }
    for (var i = 0; i < k; i++) out[1][i] = remainder[i];
    return out;
}

/// Slim modular multiplication: (a * b) mod p.
function prod_mod_p_s(n, k, a, b, p) {
    var ab[30] = prod_s(n, k, a, b);
    var div_result[2][30] = long_div2_s(n, k, k, ab, p);
    return div_result[1];
}

/// Eisenstein half-GCD: decompose scalar into 4 sub-scalars via Z[ω] GCD.
///
/// Given scalar k, finds x₀,x₁,z₀,z₁ with |xi|,|zi| < 2^NUM_BITS such that
/// k·(z₀ + z₁·λ) ≡ ±(x₀ + x₁·λ) (mod order).
///
/// Returns out[10][30]:
///   out[0] = x0_abs, out[1] = x1_abs, out[2] = z0_abs, out[3] = z1_abs
///   out[4][0] = s0 (sign of x0: 0=positive, 1=negative)
///   out[5][0] = s1 (sign of x1)
///   out[6][0] = s2 (sign of z0, with Q negation baked in)
///   out[7][0] = s3 (sign of z1, with Q negation baked in)
///   out[8][0] = sx (overall sign: 1 if relation has minus)
///   out[9][0] = unused
function eisenstein_half_gcd(n, k, scalar) {
    assert(n == 32 && k == 8);

    var out[10][30];
    for (var i = 0; i < 10; i++)
        for (var j = 0; j < 30; j++) out[i][j] = 0;

    var order[200] = SECP256K1_ORDER(n, k);

    // Eisenstein short vector w = w0 + w1·ω with N(w) = order.
    // w0 = -64502973549206556628585045361533709077 (negative)
    // w1 =  303414439467246543595250775667605759171 (positive)
    // Stored as (abs, sign) pairs.
    var w0_abs[30];
    var w1_abs[30];
    for (var i = 0; i < 30; i++) { w0_abs[i] = 0; w1_abs[i] = 0; }
    w0_abs[0] = 2458184469;  w0_abs[1] = 3899429092;
    w0_abs[2] = 2815716301;  w0_abs[3] = 814141985;
    var w0_sign = 1;  // negative
    w1_abs[0] = 180348099;   w1_abs[1] = 1867808681;
    w1_abs[2] = 17729576;    w1_abs[3] = 3829628630;
    var w1_sign = 0;  // positive

    // Eisenstein GCD: r_prev = w, r_curr = scalar + 0ω
    // Each Eisenstein integer is stored as (c0_abs, c0_sign, c1_abs, c1_sign)
    // representing (-1)^c0_sign * c0_abs + (-1)^c1_sign * c1_abs * ω

    // r_prev = (w0, w1)
    var rp0[30]; var rp1[30];
    for (var i = 0; i < 30; i++) { rp0[i] = w0_abs[i]; rp1[i] = w1_abs[i]; }
    var rp0s = w0_sign;
    var rp1s = w1_sign;

    // r_curr = (scalar, 0)
    var rc0[30]; var rc1[30];
    for (var i = 0; i < 30; i++) { rc0[i] = 0; rc1[i] = 0; }
    for (var i = 0; i < k; i++) rc0[i] = scalar[i];
    var rc0s = 0;
    var rc1s = 0;

    // t_prev = (0, 0)
    var tp0[30]; var tp1[30];
    for (var i = 0; i < 30; i++) { tp0[i] = 0; tp1[i] = 0; }
    var tp0s = 0;
    var tp1s = 0;

    // t_curr = (1, 0)
    var tc0[30]; var tc1[30];
    for (var i = 0; i < 30; i++) { tc0[i] = 0; tc1[i] = 0; }
    tc0[0] = 1;
    var tc0s = 0;
    var tc1s = 0;

    // Eisenstein norm N(a0+a1ω) = a0² - a0a1 + a1²
    // Threshold: N < 2^(2*68) = 2^136. Check by seeing if norm fits in 5 limbs.
    var done = 0;

    // Pre-allocate all loop temporaries outside the loop to avoid
    // circom's WASM compiler allocating separate memory per iteration.
    var _p1[30]; var _p2[30]; var _p3[30]; var _p4[30];
    var _p5[30]; var _p6[30]; var _p7[30]; var _p8[30];
    var _norm[30]; var _c0[30]; var _c1[30];
    var _d[30]; var _c0_2[30]; var _c0_2d[30]; var _d_2[30];
    var _c1_2[30]; var _c1_2d[30]; var _div[2][30];
    var _q0[30]; var _q1[30];
    var _qr0[30]; var _qr1[30]; var _qt0[30]; var _qt1[30];
    var _rn0[30]; var _rn1[30]; var _tn0[30]; var _tn1[30];
    var _c0_new[30];

    // Eisenstein GCD converges in O(log(order)) steps. Worst case for
    // 256-bit inputs: ~40 iterations. 50 gives comfortable margin.
    for (var iter = 0; iter < 50; iter++) {
        if (done == 0) {
            // Compute N(r_curr) and check against threshold
            var rc_has_high = 0;
            // Quick check: if any limb >= 5 is nonzero, norm is definitely large
            for (var j = 5; j < k; j++) {
                if (rc0[j] != 0) rc_has_high = 1;
                if (rc1[j] != 0) rc_has_high = 1;
            }

            if (rc_has_high == 0) {
                _p1 = prod_s(n, k, rc0, rc0);
                _p2 = prod_s(n, k, rc1, rc1);
                _p3 = prod_s(n, k, rc0, rc1);
                _norm = long_add_s(n, 2*k, _p1, _p2);
                if (rc0s == rc1s) {
                    _norm = long_sub_s(n, 2*k+1, _norm, _p3);
                } else {
                    _norm = long_add_s(n, 2*k+1, _norm, _p3);
                }

                var norm_small = 1;
                for (var j = 5; j < 2*k+2; j++) {
                    if (_norm[j] != 0) norm_small = 0;
                }
                if (_norm[4] >= 256) norm_small = 0;

                // Also check that all 4 component magnitudes fit in NUM_BITS=68 bits.
                // 68 bits = 2 full 32-bit limbs + 4 bits, so limb[2] < 16 and limbs[3..7] == 0.
                if (norm_small == 1) {
                    for (var j = 3; j < k; j++) {
                        if (rc0[j] != 0) norm_small = 0;
                        if (rc1[j] != 0) norm_small = 0;
                        if (tc0[j] != 0) norm_small = 0;
                        if (tc1[j] != 0) norm_small = 0;
                    }
                    if (rc0[2] >= 16) norm_small = 0;
                    if (rc1[2] >= 16) norm_small = 0;
                    if (tc0[2] >= 16) norm_small = 0;
                    if (tc1[2] >= 16) norm_small = 0;
                }

                if (norm_small == 1) done = 1;
            }

            if (done == 0) {
                // Eisenstein division: q = round(r_prev * conj(r_curr) / N(r_curr))
                // c = r_prev * conj(r_curr), d = N(r_curr)
                // conj(rc0+rc1ω) = (rc0-rc1) + (-rc1)ω
                // c0 = rp0*rc0 - rp0*rc1 + rp1*rc1
                // c1 = rp1*rc0 - rp0*rc1

                _p1 = prod_s(n, k, rp0, rc0);
                var _p1_s = rp0s ^ rc0s;
                _p2 = prod_s(n, k, rp1, rc1);
                var _p2_s = rp1s ^ rc1s;
                _p3 = prod_s(n, k, rp0, rc1);
                var _p3_s = rp0s ^ rc1s;
                _p4 = prod_s(n, k, rp1, rc0);
                var _p4_s = rp1s ^ rc0s;

                // c0 = _p1 + (-_p3) + _p2
                for (var j = 0; j < 30; j++) _c0[j] = _p1[j];
                var _c0_s = _p1_s;
                var _neg_p3_s = 1 - _p3_s;
                var _cn_s = 0;
                if (_c0_s == _neg_p3_s) {
                    _c0_new = long_add_s(n, 2*k, _c0, _p3);
                    _cn_s = _c0_s;
                } else {
                    if (long_gt(n, 2*k, _c0, _p3) == 1) {
                        _c0_new = long_sub_s(n, 2*k, _c0, _p3);
                        _cn_s = _c0_s;
                    } else if (long_gt(n, 2*k, _p3, _c0) == 1) {
                        _c0_new = long_sub_s(n, 2*k, _p3, _c0);
                        _cn_s = _neg_p3_s;
                    } else {
                        for (var j = 0; j < 30; j++) _c0_new[j] = 0;
                        _cn_s = 0;
                    }
                }
                for (var j = 0; j < 30; j++) _c0[j] = _c0_new[j];
                _c0_s = _cn_s;

                if (_c0_s == _p2_s) {
                    _c0 = long_add_s(n, 2*k+1, _c0, _p2);
                } else {
                    if (long_gt(n, 2*k+1, _c0, _p2) == 1) {
                        _c0 = long_sub_s(n, 2*k+1, _c0, _p2);
                    } else if (long_gt(n, 2*k+1, _p2, _c0) == 1) {
                        _c0 = long_sub_s(n, 2*k+1, _p2, _c0);
                        _c0_s = _p2_s;
                    } else {
                        for (var j = 0; j < 30; j++) _c0[j] = 0;
                        _c0_s = 0;
                    }
                }

                // c1 = _p4 - _p3
                for (var j = 0; j < 30; j++) _c1[j] = _p4[j];
                var _c1_s = _p4_s;
                var _sub_s = 1 - _p3_s;
                if (_c1_s == _sub_s) {
                    _c1 = long_add_s(n, 2*k, _c1, _p3);
                } else {
                    if (long_gt(n, 2*k, _c1, _p3) == 1) {
                        _c1 = long_sub_s(n, 2*k, _c1, _p3);
                    } else if (long_gt(n, 2*k, _p3, _c1) == 1) {
                        _c1 = long_sub_s(n, 2*k, _p3, _c1);
                        _c1_s = _sub_s;
                    } else {
                        for (var j = 0; j < 30; j++) _c1[j] = 0;
                        _c1_s = 0;
                    }
                }

                // d = N(rc) = rc0² ± rc0*rc1 + rc1²
                _p5 = prod_s(n, k, rc0, rc0);
                _p6 = prod_s(n, k, rc1, rc1);
                _p7 = prod_s(n, k, rc0, rc1);
                _d = long_add_s(n, 2*k, _p5, _p6);
                if (rc0s == rc1s) {
                    _d = long_sub_s(n, 2*k+1, _d, _p7);
                } else {
                    _d = long_add_s(n, 2*k+1, _d, _p7);
                }

                // q0 = round(c0/d), q1 = round(c1/d)
                var dk = 1;
                for (var j = 0; j < 2*k+2; j++) {
                    if (_d[j] != 0) dk = j + 1;
                }

                _c0_2 = long_add_s(n, 2*k+2, _c0, _c0);
                _c0_2d = long_add_s(n, 2*k+3, _c0_2, _d);
                _d_2 = long_add_s(n, 2*k+2, _d, _d);

                var d2k = 1;
                for (var j = 0; j < 2*k+3; j++) {
                    if (_d_2[j] != 0) d2k = j + 1;
                }
                var c0m = 1;
                for (var j = 0; j < 2*k+4; j++) {
                    if (_c0_2d[j] != 0) c0m = j + 1;
                }
                var q0_m = c0m - d2k;
                if (q0_m < 0) q0_m = 0;

                _div = long_div2_s(n, d2k, q0_m, _c0_2d, _d_2);
                for (var j = 0; j < 30; j++) _q0[j] = 0;
                for (var j = 0; j <= q0_m; j++) _q0[j] = _div[0][j];
                var q0_sign = _c0_s;

                _c1_2 = long_add_s(n, 2*k+2, _c1, _c1);
                _c1_2d = long_add_s(n, 2*k+3, _c1_2, _d);

                var c1m = 1;
                for (var j = 0; j < 2*k+4; j++) {
                    if (_c1_2d[j] != 0) c1m = j + 1;
                }
                var q1_m = c1m - d2k;
                if (q1_m < 0) q1_m = 0;

                _div = long_div2_s(n, d2k, q1_m, _c1_2d, _d_2);
                for (var j = 0; j < 30; j++) _q1[j] = 0;
                for (var j = 0; j <= q1_m; j++) _q1[j] = _div[0][j];
                var q1_sign = _c1_s;

                // r_next = r_prev - q * r_curr
                // q*rc = (q0*rc0 - q1*rc1) + (q0*rc1 + q1*rc0 - q1*rc1)ω
                _p1 = prod_s(n, k, _q0, rc0);
                _p1_s = q0_sign ^ rc0s;
                _p2 = prod_s(n, k, _q1, rc1);
                _p2_s = q1_sign ^ rc1s;
                _p3 = prod_s(n, k, _q0, rc1);
                _p3_s = q0_sign ^ rc1s;
                _p4 = prod_s(n, k, _q1, rc0);
                _p4_s = q1_sign ^ rc0s;

                // qr0 = _p1 - _p2
                for (var j = 0; j < 30; j++) _qr0[j] = _p1[j];
                var _qr0_s = _p1_s;
                var _neg_p2_s = 1 - _p2_s;
                if (_qr0_s == _neg_p2_s) {
                    _qr0 = long_add_s(n, 2*k, _qr0, _p2);
                } else {
                    if (long_gt(n, 2*k, _qr0, _p2) == 1) {
                        _qr0 = long_sub_s(n, 2*k, _qr0, _p2);
                    } else if (long_gt(n, 2*k, _p2, _qr0) == 1) {
                        _qr0 = long_sub_s(n, 2*k, _p2, _qr0);
                        _qr0_s = _neg_p2_s;
                    } else {
                        for (var j = 0; j < 30; j++) _qr0[j] = 0;
                        _qr0_s = 0;
                    }
                }

                // qr1 = _p3 + _p4 - _p2
                for (var j = 0; j < 30; j++) _qr1[j] = _p3[j];
                var _qr1_s = _p3_s;
                if (_qr1_s == _p4_s) {
                    _qr1 = long_add_s(n, 2*k, _qr1, _p4);
                } else {
                    if (long_gt(n, 2*k, _qr1, _p4) == 1) {
                        _qr1 = long_sub_s(n, 2*k, _qr1, _p4);
                    } else if (long_gt(n, 2*k, _p4, _qr1) == 1) {
                        _qr1 = long_sub_s(n, 2*k, _p4, _qr1);
                        _qr1_s = _p4_s;
                    } else {
                        for (var j = 0; j < 30; j++) _qr1[j] = 0;
                        _qr1_s = 0;
                    }
                }
                _neg_p2_s = 1 - _p2_s;
                if (_qr1_s == _neg_p2_s) {
                    _qr1 = long_add_s(n, 2*k+1, _qr1, _p2);
                } else {
                    if (long_gt(n, 2*k+1, _qr1, _p2) == 1) {
                        _qr1 = long_sub_s(n, 2*k+1, _qr1, _p2);
                    } else if (long_gt(n, 2*k+1, _p2, _qr1) == 1) {
                        _qr1 = long_sub_s(n, 2*k+1, _p2, _qr1);
                        _qr1_s = _neg_p2_s;
                    } else {
                        for (var j = 0; j < 30; j++) _qr1[j] = 0;
                        _qr1_s = 0;
                    }
                }

                // rn0 = rp0 - qr0
                var _rn0_s = 0;
                var _neg_qr0_s = 1 - _qr0_s;
                if (rp0s == _neg_qr0_s) {
                    _rn0 = long_add_s(n, 2*k+1, rp0, _qr0);
                    _rn0_s = rp0s;
                } else {
                    if (long_gt(n, 2*k+1, rp0, _qr0) == 1) {
                        _rn0 = long_sub_s(n, 2*k+1, rp0, _qr0);
                        _rn0_s = rp0s;
                    } else if (long_gt(n, 2*k+1, _qr0, rp0) == 1) {
                        _rn0 = long_sub_s(n, 2*k+1, _qr0, rp0);
                        _rn0_s = _neg_qr0_s;
                    } else {
                        for (var j = 0; j < 30; j++) _rn0[j] = 0;
                        _rn0_s = 0;
                    }
                }

                // rn1 = rp1 - qr1
                var _rn1_s = 0;
                var _neg_qr1_s = 1 - _qr1_s;
                if (rp1s == _neg_qr1_s) {
                    _rn1 = long_add_s(n, 2*k+1, rp1, _qr1);
                    _rn1_s = rp1s;
                } else {
                    if (long_gt(n, 2*k+1, rp1, _qr1) == 1) {
                        _rn1 = long_sub_s(n, 2*k+1, rp1, _qr1);
                        _rn1_s = rp1s;
                    } else if (long_gt(n, 2*k+1, _qr1, rp1) == 1) {
                        _rn1 = long_sub_s(n, 2*k+1, _qr1, rp1);
                        _rn1_s = _neg_qr1_s;
                    } else {
                        for (var j = 0; j < 30; j++) _rn1[j] = 0;
                        _rn1_s = 0;
                    }
                }

                // t_next = t_prev - q * t_curr
                _p5 = prod_s(n, k, _q0, tc0);
                var _p5_s = q0_sign ^ tc0s;
                _p6 = prod_s(n, k, _q1, tc1);
                var _p6_s = q1_sign ^ tc1s;
                _p7 = prod_s(n, k, _q0, tc1);
                var _p7_s = q0_sign ^ tc1s;
                _p8 = prod_s(n, k, _q1, tc0);
                var _p8_s = q1_sign ^ tc0s;

                // qt0 = _p5 - _p6
                for (var j = 0; j < 30; j++) _qt0[j] = _p5[j];
                var _qt0_s = _p5_s;
                var _neg_p6_s = 1 - _p6_s;
                if (_qt0_s == _neg_p6_s) {
                    _qt0 = long_add_s(n, 2*k, _qt0, _p6);
                } else {
                    if (long_gt(n, 2*k, _qt0, _p6) == 1) {
                        _qt0 = long_sub_s(n, 2*k, _qt0, _p6);
                    } else if (long_gt(n, 2*k, _p6, _qt0) == 1) {
                        _qt0 = long_sub_s(n, 2*k, _p6, _qt0);
                        _qt0_s = _neg_p6_s;
                    } else {
                        for (var j = 0; j < 30; j++) _qt0[j] = 0;
                        _qt0_s = 0;
                    }
                }

                // qt1 = _p7 + _p8 - _p6
                for (var j = 0; j < 30; j++) _qt1[j] = _p7[j];
                var _qt1_s = _p7_s;
                if (_qt1_s == _p8_s) {
                    _qt1 = long_add_s(n, 2*k, _qt1, _p8);
                } else {
                    if (long_gt(n, 2*k, _qt1, _p8) == 1) {
                        _qt1 = long_sub_s(n, 2*k, _qt1, _p8);
                    } else if (long_gt(n, 2*k, _p8, _qt1) == 1) {
                        _qt1 = long_sub_s(n, 2*k, _p8, _qt1);
                        _qt1_s = _p8_s;
                    } else {
                        for (var j = 0; j < 30; j++) _qt1[j] = 0;
                        _qt1_s = 0;
                    }
                }
                _neg_p6_s = 1 - _p6_s;
                if (_qt1_s == _neg_p6_s) {
                    _qt1 = long_add_s(n, 2*k+1, _qt1, _p6);
                } else {
                    if (long_gt(n, 2*k+1, _qt1, _p6) == 1) {
                        _qt1 = long_sub_s(n, 2*k+1, _qt1, _p6);
                    } else if (long_gt(n, 2*k+1, _p6, _qt1) == 1) {
                        _qt1 = long_sub_s(n, 2*k+1, _p6, _qt1);
                        _qt1_s = _neg_p6_s;
                    } else {
                        for (var j = 0; j < 30; j++) _qt1[j] = 0;
                        _qt1_s = 0;
                    }
                }

                // tn0 = tp0 - qt0
                var _tn0_s = 0;
                var _neg_qt0_s = 1 - _qt0_s;
                if (tp0s == _neg_qt0_s) {
                    _tn0 = long_add_s(n, 2*k+1, tp0, _qt0);
                    _tn0_s = tp0s;
                } else {
                    if (long_gt(n, 2*k+1, tp0, _qt0) == 1) {
                        _tn0 = long_sub_s(n, 2*k+1, tp0, _qt0);
                        _tn0_s = tp0s;
                    } else if (long_gt(n, 2*k+1, _qt0, tp0) == 1) {
                        _tn0 = long_sub_s(n, 2*k+1, _qt0, tp0);
                        _tn0_s = _neg_qt0_s;
                    } else {
                        for (var j = 0; j < 30; j++) _tn0[j] = 0;
                        _tn0_s = 0;
                    }
                }

                // tn1 = tp1 - qt1
                var _tn1_s = 0;
                var _neg_qt1_s = 1 - _qt1_s;
                if (tp1s == _neg_qt1_s) {
                    _tn1 = long_add_s(n, 2*k+1, tp1, _qt1);
                    _tn1_s = tp1s;
                } else {
                    if (long_gt(n, 2*k+1, tp1, _qt1) == 1) {
                        _tn1 = long_sub_s(n, 2*k+1, tp1, _qt1);
                        _tn1_s = tp1s;
                    } else if (long_gt(n, 2*k+1, _qt1, tp1) == 1) {
                        _tn1 = long_sub_s(n, 2*k+1, _qt1, tp1);
                        _tn1_s = _neg_qt1_s;
                    } else {
                        for (var j = 0; j < 30; j++) _tn1[j] = 0;
                        _tn1_s = 0;
                    }
                }

                // Shift: prev <- curr, curr <- next
                for (var j = 0; j < 30; j++) {
                    rp0[j] = rc0[j]; rp1[j] = rc1[j];
                    rc0[j] = _rn0[j]; rc1[j] = _rn1[j];
                    tp0[j] = tc0[j]; tp1[j] = tc1[j];
                    tc0[j] = _tn0[j]; tc1[j] = _tn1[j];
                }
                rp0s = rc0s; rp1s = rc1s;
                rc0s = _rn0_s; rc1s = _rn1_s;
                tp0s = tc0s; tp1s = tc1s;
                tc0s = _tn0_s; tc1s = _tn1_s;
            }
        }
    }

    // r_curr = x0 + x1·ω, t_curr = z0 + z1·ω
    // Relation: k·(z0+z1λ) ≡ ±(x0+x1λ) (mod order)
    //
    // Determine sign bits for the base points.
    // Default (positive relation, no component negation): s0=0, s1=0, s2=1, s3=1
    // (negate Q side since equation is [x]P - [z]Q = O)
    //
    // Component sign adjustments:
    //   x0 negative → flip s0
    //   x1 negative → flip s1
    //   z0 negative → flip s2
    //   z1 negative → flip s3

    // Compute overall sign sx using modular verification
    var lambda_const[200] = SECP256K1_LAMBDA(n, k);
    var z1l[30] = prod_mod_p_s(n, k, tc1, lambda_const, order);
    var z_comp[30];
    for (var j = 0; j < 30; j++) z_comp[j] = 0;
    if (tc0s == tc1s) {
        z_comp = long_add_s(n, k, tc0, z1l);
        if (long_gt(n, k+1, z_comp, order) == 1) {
            z_comp = long_sub_s(n, k+1, z_comp, order);
        }
    } else {
        if (long_gt(n, k, tc0, z1l) == 1) {
            z_comp = long_sub_s(n, k, tc0, z1l);
        } else {
            z_comp = long_sub_s(n, k, z1l, tc0);
        }
    }

    var tc0_mod[30];
    for (var j = 0; j < 30; j++) tc0_mod[j] = 0;
    if (tc0s == 0) {
        for (var j = 0; j < k; j++) tc0_mod[j] = tc0[j];
    } else {
        tc0_mod = long_sub_s(n, k, order, tc0);
    }
    var tc1_mod[30];
    for (var j = 0; j < 30; j++) tc1_mod[j] = 0;
    if (tc1s == 0) {
        for (var j = 0; j < k; j++) tc1_mod[j] = tc1[j];
    } else {
        tc1_mod = long_sub_s(n, k, order, tc1);
    }
    var z1l_mod[30] = prod_mod_p_s(n, k, tc1_mod, lambda_const, order);
    var z_val[30] = long_add_s(n, k, tc0_mod, z1l_mod);
    if (long_gt(n, k+1, z_val, order) == 1) {
        z_val = long_sub_s(n, k+1, z_val, order);
    }

    var lhs[30] = prod_mod_p_s(n, k, scalar, z_val, order);

    var rc0_mod[30];
    for (var j = 0; j < 30; j++) rc0_mod[j] = 0;
    if (rc0s == 0) {
        for (var j = 0; j < k; j++) rc0_mod[j] = rc0[j];
    } else {
        rc0_mod = long_sub_s(n, k, order, rc0);
    }
    var rc1_mod[30];
    for (var j = 0; j < 30; j++) rc1_mod[j] = 0;
    if (rc1s == 0) {
        for (var j = 0; j < k; j++) rc1_mod[j] = rc1[j];
    } else {
        rc1_mod = long_sub_s(n, k, order, rc1);
    }
    var x1l_mod[30] = prod_mod_p_s(n, k, rc1_mod, lambda_const, order);
    var x_val[30] = long_add_s(n, k, rc0_mod, x1l_mod);
    if (long_gt(n, k+1, x_val, order) == 1) {
        x_val = long_sub_s(n, k+1, x_val, order);
    }

    // Check: lhs == x_val → sx = 0, lhs == order - x_val → sx = 1
    // The extended GCD invariant guarantees r_curr ≡ scalar·t_curr (mod w),
    // which maps to x₀+x₁λ ≡ scalar·(z₀+z₁λ) (mod order) — always positive.
    // sx is always 0; the ± case does not arise.
    var sx = 0;
    var is_positive = 1;
    for (var j = 0; j < k; j++) {
        if (lhs[j] != x_val[j]) is_positive = 0;
    }

    // Compute sign bits for base point construction
    // Default: s0=0, s1=0, s2=1, s3=1 (negate Q side)
    var s0 = 0;
    var s1 = 0;
    var s2 = 1;
    var s3 = 1;

    // Flip for component signs
    if (rc0s == 1) s0 = 1 - s0;
    if (rc1s == 1) s1 = 1 - s1;
    if (tc0s == 1) s2 = 1 - s2;
    if (tc1s == 1) s3 = 1 - s3;

    for (var j = 0; j < k; j++) {
        out[0][j] = rc0[j];  // x0_abs
        out[1][j] = rc1[j];  // x1_abs
        out[2][j] = tc0[j];  // z0_abs
        out[3][j] = tc1[j];  // z1_abs
    }
    out[4][0] = s0;
    out[5][0] = s1;
    out[6][0] = s2;
    out[7][0] = s3;
    out[8][0] = sx;

    return out;
}
