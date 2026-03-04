pragma circom 2.2.2;

// ═══════════════════════════════════════════════════
// Utility functions
// ═══════════════════════════════════════════════════

/// Returns 1 if x represents a "negative" field element (> p_field/2).
function isNegative(x) {
    return x > 10944121435919637611123202872628637544274182200208017171849102093287904247808 ? 1 : 0;
}

/// Ceiling division: ceil(m / n).
function div_ceil(m, n) {
    if (m % n == 0) {
        return m \ n;
    } else {
        return m \ n + 1;
    }
}

/// Ceiling log2.
function log_ceil(n) {
    var n_temp = n;
    for (var i = 0; i < 254; i++) {
        if (n_temp == 0) return i;
        n_temp = n_temp \ 2;
    }
    return 254;
}

/// Splits a value into a low part (n bits) and overflow (m bits).
/// Returns [low, high] where in = low + high * 2^n.
function SplitFn(in, n, m) {
    return [in % (1 << n), (in >> n) % (1 << m)];
}

/// Splits a value into three parts of n, m, k bits.
function SplitThreeFn(in, n, m, k) {
    return [in % (1 << n), (in \ (1 << n)) % (1 << m), (in \ (1 << (n + m))) % (1 << k)];
}

// ═══════════════════════════════════════════════════
// Register splitting and representation
// ═══════════════════════════════════════════════════

/// Splits an m-bit number into ceil(m/n) n-bit registers.
function splitOverflowedRegister(m, n, in) {
    var out[200];
    for (var i = 0; i < 200; i++) out[i] = 0;
    var nRegisters = div_ceil(m, n);
    var running = in;
    for (var i = 0; i < nRegisters; i++) {
        out[i] = running % (1 << n);
        running = running >> n;
    }
    return out;
}

/// Converts k registers of m-bit (potentially overflowed/negative) values
/// into proper n-bit representation. Output has k + ceil(m/n) registers.
/// The highest-order register may be negative; all others are non-negative.
function getProperRepresentation(m, n, k, in) {
    var ceilMN = div_ceil(m, n);

    var pieces[100][100];
    for (var i = 0; i < k; i++) {
        for (var j = 0; j < 100; j++) pieces[i][j] = 0;
        if (isNegative(in[i]) == 1) {
            var negPieces[200] = splitOverflowedRegister(m, n, -1 * in[i]);
            for (var j = 0; j < ceilMN; j++) {
                pieces[i][j] = -1 * negPieces[j];
            }
        } else {
            var posPieces[200] = splitOverflowedRegister(m, n, in[i]);
            for (var j = 0; j < ceilMN; j++) {
                pieces[i][j] = posPieces[j];
            }
        }
    }

    var out[200];
    var carries[200];
    for (var i = 0; i < 200; i++) { out[i] = 0; carries[i] = 0; }

    for (var registerIdx = 0; registerIdx < k + ceilMN; registerIdx++) {
        var thisRegisterValue = 0;
        if (registerIdx > 0) {
            thisRegisterValue = carries[registerIdx - 1];
        }

        var start = 0;
        if (registerIdx >= ceilMN) {
            start = registerIdx - ceilMN + 1;
        }
        for (var i = start; i <= registerIdx; i++) {
            if (i < k) {
                thisRegisterValue += pieces[i][registerIdx - i];
            }
        }

        if (isNegative(thisRegisterValue) == 1) {
            var thisRegisterAbs = -1 * thisRegisterValue;
            out[registerIdx] = (1 << n) - (thisRegisterAbs % (1 << n));
            carries[registerIdx] = -1 * (thisRegisterAbs >> n) - 1;
        } else {
            out[registerIdx] = thisRegisterValue % (1 << n);
            carries[registerIdx] = thisRegisterValue >> n;
        }
    }
    return out;
}

// ═══════════════════════════════════════════════════
// Multi-limb comparison and arithmetic
// ═══════════════════════════════════════════════════

/// Returns 1 if a > b (both k-limb, n-bit, little-endian). 0 otherwise.
function long_gt(n, k, a, b) {
    for (var i = k - 1; i >= 0; i--) {
        if (a[i] > b[i]) return 1;
        if (a[i] < b[i]) return 0;
    }
    return 0;
}

/// Subtracts two k-limb numbers: out = a - b. Assumes a >= b.
function long_sub(n, k, a, b) {
    var diff[200];
    var borrow[200];
    for (var i = 0; i < 200; i++) { diff[i] = 0; borrow[i] = 0; }
    for (var i = 0; i < k; i++) {
        if (i == 0) {
            if (a[i] >= b[i]) {
                diff[i] = a[i] - b[i];
                borrow[i] = 0;
            } else {
                diff[i] = a[i] - b[i] + (1 << n);
                borrow[i] = 1;
            }
        } else {
            if (a[i] >= b[i] + borrow[i - 1]) {
                diff[i] = a[i] - b[i] - borrow[i - 1];
                borrow[i] = 0;
            } else {
                diff[i] = (1 << n) + a[i] - b[i] - borrow[i - 1];
                borrow[i] = 1;
            }
        }
    }
    return diff;
}

/// Multiplies a k-limb number b by an n-bit scalar a. Returns (k+1)-limb result.
function long_scalar_mult(n, k, a, b) {
    var out[200];
    for (var i = 0; i < 200; i++) out[i] = 0;
    for (var i = 0; i < k; i++) {
        var temp = out[i] + (a * b[i]);
        out[i] = temp % (1 << n);
        out[i + 1] = out[i + 1] + temp \ (1 << n);
    }
    return out;
}

/// Full multiplication of two k-limb numbers with n-bit limbs.
/// Returns a 2k-limb result (schoolbook multiplication with carry propagation).
function prod(n, k, a, b) {
    var prod_val[200];
    for (var i = 0; i < 2 * k - 1; i++) {
        prod_val[i] = 0;
        if (i < k) {
            for (var a_idx = 0; a_idx <= i; a_idx++) {
                prod_val[i] = prod_val[i] + a[a_idx] * b[i - a_idx];
            }
        } else {
            for (var a_idx = i - k + 1; a_idx < k; a_idx++) {
                prod_val[i] = prod_val[i] + a[a_idx] * b[i - a_idx];
            }
        }
    }

    var out[200];
    for (var i = 0; i < 200; i++) out[i] = 0;
    var split[200][3];
    for (var i = 0; i < 2 * k - 1; i++) {
        split[i] = SplitThreeFn(prod_val[i], n, n, n);
    }

    var carry[200];
    for (var i = 0; i < 200; i++) carry[i] = 0;
    out[0] = split[0][0];
    if (2 * k - 1 > 1) {
        var sumAndCarry[2] = SplitFn(split[0][1] + split[1][0], n, n);
        out[1] = sumAndCarry[0];
        carry[1] = sumAndCarry[1];
    }
    if (2 * k - 1 > 2) {
        for (var i = 2; i < 2 * k - 1; i++) {
            var sumAndCarry[2] = SplitFn(
                split[i][0] + split[i - 1][1] + split[i - 2][2] + carry[i - 1], n, n
            );
            out[i] = sumAndCarry[0];
            carry[i] = sumAndCarry[1];
        }
        out[2 * k - 1] = split[2 * k - 2][1] + split[2 * k - 3][2] + carry[2 * k - 2];
    }
    return out;
}

// ═══════════════════════════════════════════════════
// Division (Knuth's schoolbook algorithm)
// Operates purely on limb arrays — never accumulates full multi-limb values.
// ═══════════════════════════════════════════════════

/// Normalized short division: divides (k+1)-limb a by k-limb b.
/// Assumes leading digit of b is at least 2^(n-1).
function short_div_norm(n, k, a, b) {
    var qhat = (a[k] * (1 << n) + a[k - 1]) \ b[k - 1];
    if (qhat > (1 << n) - 1) {
        qhat = (1 << n) - 1;
    }
    var mult[200] = long_scalar_mult(n, k, qhat, b);
    if (long_gt(n, k + 1, mult, a) == 1) {
        mult = long_sub(n, k + 1, mult, b);
        if (long_gt(n, k + 1, mult, a) == 1) {
            return qhat - 2;
        } else {
            return qhat - 1;
        }
    } else {
        return qhat;
    }
}

/// Short division: divides (k+1)-limb a by k-limb b.
/// Assumes b[k-1] != 0 and 0 <= a < (2^n) * b.
function short_div(n, k, a, b) {
    var scale = (1 << n) \ (1 + b[k - 1]);
    var norm_a[200] = long_scalar_mult(n, k + 1, scale, a);
    var norm_b[200] = long_scalar_mult(n, k, scale, b);

    var ret;
    if (norm_b[k] != 0) {
        ret = short_div_norm(n, k + 1, norm_a, norm_b);
    } else {
        ret = short_div_norm(n, k, norm_a, norm_b);
    }
    return ret;
}

/// General long division: a has (k+m) limbs, b has k limbs.
/// Returns out[2][200]: out[0] = quotient (m+1 limbs), out[1] = remainder (k limbs).
/// b[k-1] must be nonzero.
function long_div2(n, k, m, a, b) {
    var out[2][200];
    for (var i = 0; i < 200; i++) { out[0][i] = 0; out[1][i] = 0; }

    var remainder[200];
    for (var i = 0; i < 200; i++) remainder[i] = 0;
    for (var i = 0; i < m + k; i++) remainder[i] = a[i];

    var dividend[200];
    for (var i = m; i >= 0; i--) {
        for (var j = 0; j < 200; j++) dividend[j] = 0;
        if (i == m) {
            dividend[k] = 0;
            for (var j = k - 1; j >= 0; j--) {
                dividend[j] = remainder[j + m];
            }
        } else {
            for (var j = k; j >= 0; j--) {
                dividend[j] = remainder[j + i];
            }
        }

        out[0][i] = short_div(n, k, dividend, b);

        var mult_shift[200] = long_scalar_mult(n, k, out[0][i], b);
        var subtrahend[200];
        for (var j = 0; j < 200; j++) subtrahend[j] = 0;
        for (var j = 0; j <= k; j++) {
            if (i + j < m + k) {
                subtrahend[i + j] = mult_shift[j];
            }
        }
        remainder = long_sub(n, m + k, remainder, subtrahend);
    }
    for (var i = 0; i < k; i++) {
        out[1][i] = remainder[i];
    }
    return out;
}

/// Long division of a (k+1)-limb number by a k-limb number.
/// Returns [quotient[200], remainder[200]].
/// Delegates to long_div2 with m=1.
function long_div(n, k, a, b) {
    return long_div2(n, k, 1, a, b);
}

// ═══════════════════════════════════════════════════
// Modular arithmetic (multi-limb, no overflow)
// ═══════════════════════════════════════════════════

/// (a - b) mod p. All are k-limb, n-bit numbers in [0, p).
function long_sub_mod_p(n, k, a, b, p) {
    var gt = long_gt(n, k, a, b);
    var tmp[200];
    if (gt) {
        tmp = long_sub(n, k, a, b);
    } else {
        tmp = long_sub(n, k, b, a);
    }
    for (var i = k; i < 2 * k; i++) tmp[i] = 0;
    var div_result[2][200] = long_div2(n, k, k, tmp, p);
    if (gt == 0) {
        // Check if remainder is zero (a == b case)
        var isZeroRem = 1;
        for (var i = 0; i < k; i++) {
            if (div_result[1][i] != 0) isZeroRem = 0;
        }
        if (isZeroRem == 1) {
            for (var i = 0; i < 200; i++) tmp[i] = 0;
        } else {
            tmp = long_sub(n, k, p, div_result[1]);
        }
    } else {
        for (var i = 0; i < k; i++) tmp[i] = div_result[1][i];
    }
    return tmp;
}

/// (a * b) mod p. All are k-limb, n-bit numbers.
function prod_mod_p(n, k, a, b, p) {
    var ab[200] = prod(n, k, a, b);
    var div_result[2][200] = long_div2(n, k, k, ab, p);
    return div_result[1];
}

/// Modular exponentiation: a^e mod p using multi-limb arithmetic.
/// e is a k-limb number. p must be prime. k*n <= 500.
function mod_exp(n, k, a, p, e) {
    var eBits[500];
    for (var i = 0; i < k; i++) {
        for (var j = 0; j < n; j++) {
            eBits[j + n * i] = (e[i] >> j) & 1;
        }
    }

    var out[200];
    for (var i = 0; i < 200; i++) out[i] = 0;
    out[0] = 1;

    for (var i = k * n - 1; i >= 0; i--) {
        if (eBits[i] == 1) {
            var temp[200] = prod(n, k, out, a);
            var temp2[2][200] = long_div2(n, k, k, temp, p);
            out = temp2[1];
        }
        if (i > 0) {
            var sq[200] = prod(n, k, out, out);
            var sq2[2][200] = long_div2(n, k, k, sq, p);
            out = sq2[1];
        }
    }
    return out;
}

/// Modular inverse: a^(-1) mod p via Fermat's little theorem (a^(p-2) mod p).
function mod_inv(n, k, a, p) {
    var isZero = 1;
    for (var i = 0; i < k; i++) {
        if (a[i] != 0) isZero = 0;
    }
    if (isZero == 1) {
        var ret[200];
        for (var i = 0; i < 200; i++) ret[i] = 0;
        return ret;
    }

    var pCopy[200];
    for (var i = 0; i < 200; i++) pCopy[i] = 0;
    for (var i = 0; i < k; i++) pCopy[i] = p[i];

    var two[200];
    for (var i = 0; i < 200; i++) two[i] = 0;
    two[0] = 2;

    var pMinusTwo[200] = long_sub(n, k, pCopy, two);
    return mod_exp(n, k, a, pCopy, pMinusTwo);
}
