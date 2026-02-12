pragma circom 2.2.2;

/// Splits a value into a low part (n bits) and overflow.
/// Returns [low, high] where in = low + high * 2^n.
function SplitFn(in, n, m) {
    return [in % (1 << n), (in >> n) % (1 << m)];
}

/// Full multiplication of two k-limb numbers with n-bit limbs.
/// Returns a 2k-limb result (schoolbook multiplication).
function prod(n, k, a, b) {
    var result[200]; // large enough for 2k limbs
    for (var i = 0; i < 2 * k; i++) {
        result[i] = 0;
    }
    for (var i = 0; i < k; i++) {
        for (var j = 0; j < k; j++) {
            result[i + j] += a[i] * b[j];
        }
    }
    // Propagate carries
    for (var i = 0; i < 2 * k - 1; i++) {
        result[i + 1] += result[i] >> n;
        result[i] = result[i] % (1 << n);
    }
    return result;
}

/// Long division of a (k+1)-limb number a by a k-limb number b.
/// Both have n-bit limbs. Returns [quotient, remainder].
/// Quotient is 2 limbs, remainder is k limbs.
function long_div(n, k, a, b) {
    // Convert to single values for division
    var a_val = 0;
    for (var i = k; i >= 0; i--) {
        a_val = a_val * (1 << n) + a[i];
    }
    var b_val = 0;
    for (var i = k - 1; i >= 0; i--) {
        b_val = b_val * (1 << n) + b[i];
    }

    var quot[200];
    var rem[200];

    if (b_val == 0) {
        // Division by zero: return zeros
        for (var i = 0; i < 200; i++) {
            quot[i] = 0;
            rem[i] = 0;
        }
        return [quot, rem];
    }

    var q_val = a_val \ b_val;
    var r_val = a_val % b_val;

    for (var i = 0; i < 200; i++) {
        quot[i] = 0;
        rem[i] = 0;
    }
    for (var i = 0; i < 2; i++) {
        quot[i] = (q_val >> (i * n)) % (1 << n);
    }
    for (var i = 0; i < k; i++) {
        rem[i] = (r_val >> (i * n)) % (1 << n);
    }

    return [quot, rem];
}

/// Modular inverse of a mod p. Both are k-limb numbers with n-bit limbs.
/// Uses Fermat's little theorem: a^(-1) = a^(p-2) mod p (requires p prime).
/// Returns the inverse as a k-limb number, or zero if no inverse exists.
function mod_inv(n, k, a, p) {
    // Convert to single values
    var a_val = 0;
    for (var i = k - 1; i >= 0; i--) {
        a_val = a_val * (1 << n) + a[i];
    }
    var p_val = 0;
    for (var i = k - 1; i >= 0; i--) {
        p_val = p_val * (1 << n) + p[i];
    }

    var result[200];
    for (var i = 0; i < 200; i++) {
        result[i] = 0;
    }

    if (a_val == 0 || p_val == 0) {
        return result;
    }

    // a^(p-2) mod p via square-and-multiply
    var e = p_val - 2;
    var acc = 1;
    var b = a_val % p_val;
    while (e > 0) {
        if (e % 2 == 1) {
            acc = (acc * b) % p_val;
        }
        b = (b * b) % p_val;
        e = e \ 2;
    }

    for (var i = 0; i < k; i++) {
        result[i] = (acc >> (i * n)) % (1 << n);
    }

    return result;
}

/// Modular exponentiation: base^exp mod modulus.
/// All are k-limb numbers with n-bit limbs.
/// Uses square-and-multiply.
function mod_exp(n, k, base, exp, modulus) {
    // Convert to single values
    var base_val = 0;
    for (var i = k - 1; i >= 0; i--) {
        base_val = base_val * (1 << n) + base[i];
    }
    var exp_val = 0;
    for (var i = k - 1; i >= 0; i--) {
        exp_val = exp_val * (1 << n) + exp[i];
    }
    var mod_val = 0;
    for (var i = k - 1; i >= 0; i--) {
        mod_val = mod_val * (1 << n) + modulus[i];
    }

    var result[200];
    for (var i = 0; i < 200; i++) {
        result[i] = 0;
    }

    if (mod_val == 0) {
        return result;
    }

    // Square-and-multiply
    var acc = 1;
    var b = base_val % mod_val;
    var e = exp_val;
    while (e > 0) {
        if (e % 2 == 1) {
            acc = (acc * b) % mod_val;
        }
        b = (b * b) % mod_val;
        e = e \ 2;
    }

    for (var i = 0; i < k; i++) {
        result[i] = (acc >> (i * n)) % (1 << n);
    }

    return result;
}
