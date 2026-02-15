pragma circom 2.2.2;

include "core/comparators.circom";
include "packing/bitify.circom";
include "arithmetic/bigint_func.circom";

/// Checks that a k-limb "carry" representation equals zero.
/// Each limb has n bits; carries are bounded to m bits (signed).
/// Adds a bias of 2^(n+m) before division to handle negative limb values.
template CheckCarryToZero(n, m, k) {
    assert(k >= 2);

    signal input in[k];

    signal carry[k - 1];
    component carry_rc[k - 1];

    var bias = 1 << (n + m);
    var carry_bias = 1 << m;

    carry[0] <-- (in[0] + bias) \ (1 << n) - carry_bias;
    in[0] === carry[0] * (1 << n);
    carry_rc[0] = Num2Bits(m + 1);
    carry_rc[0].in <== carry[0] + carry_bias;

    for (var i = 1; i < k - 1; i++) {
        carry[i] <-- (in[i] + carry[i - 1] + bias) \ (1 << n) - carry_bias;
        in[i] + carry[i - 1] === carry[i] * (1 << n);
        carry_rc[i] = Num2Bits(m + 1);
        carry_rc[i].in <== carry[i] + carry_bias;
    }

    in[k - 1] + carry[k - 2] === 0;
}

/// Converts a k-limb number where limbs may exceed n bits
/// into proper n-bit limbs. Assumes no carry out of the last limb.
template LongToShortNoEndCarry(n, k) {
    signal input in[k];
    signal output out[k];

    signal carry[k - 1];
    component rc[k];

    out[0] <-- in[0] % (1 << n);
    carry[0] <-- in[0] >> n;
    in[0] === out[0] + carry[0] * (1 << n);
    rc[0] = Num2Bits(n);
    rc[0].in <== out[0];

    for (var i = 1; i < k - 1; i++) {
        out[i] <-- (in[i] + carry[i - 1]) % (1 << n);
        carry[i] <-- (in[i] + carry[i - 1]) >> n;
        in[i] + carry[i - 1] === out[i] + carry[i] * (1 << n);
        rc[i] = Num2Bits(n);
        rc[i].in <== out[i];
    }

    out[k - 1] <== in[k - 1] + carry[k - 2];
    rc[k - 1] = Num2Bits(n);
    rc[k - 1].in <== out[k - 1];
}

/// Adds two k-limb numbers with n-bit limbs.
/// Output is (k+1) limbs to accommodate overflow.
template BigAdd(n, k) {
    signal input a[k];
    signal input b[k];
    signal output out[k + 1];

    signal carry[k];
    component rc[k];
    component cc[k];

    var split[2] = SplitFn(a[0] + b[0], n, n);
    out[0] <-- split[0];
    carry[0] <-- split[1];
    a[0] + b[0] === out[0] + carry[0] * (1 << n);
    rc[0] = Num2Bits(n);
    rc[0].in <== out[0];
    cc[0] = Num2Bits(1);
    cc[0].in <== carry[0];

    for (var i = 1; i < k; i++) {
        split = SplitFn(a[i] + b[i] + carry[i - 1], n, n);
        out[i] <-- split[0];
        carry[i] <-- split[1];
        a[i] + b[i] + carry[i - 1] === out[i] + carry[i] * (1 << n);
        rc[i] = Num2Bits(n);
        rc[i].in <== out[i];
        cc[i] = Num2Bits(1);
        cc[i].in <== carry[i];
    }

    out[k] <== carry[k - 1];
}

/// Subtracts two k-limb numbers: out = a - b.
/// Assumes a >= b. Underflow is a constraint violation.
template BigSub(n, k) {
    signal input a[k];
    signal input b[k];
    signal output out[k];

    signal borrow[k - 1];
    component rc[k];
    component bc[k - 1];

    borrow[0] <-- (a[0] < b[0]) ? 1 : 0;
    out[0] <== a[0] - b[0] + borrow[0] * (1 << n);
    rc[0] = Num2Bits(n);
    rc[0].in <== out[0];
    bc[0] = Num2Bits(1);
    bc[0].in <== borrow[0];

    for (var i = 1; i < k - 1; i++) {
        borrow[i] <-- (a[i] - borrow[i - 1] < b[i]) ? 1 : 0;
        out[i] <== a[i] - borrow[i - 1] - b[i] + borrow[i] * (1 << n);
        rc[i] = Num2Bits(n);
        rc[i].in <== out[i];
        bc[i] = Num2Bits(1);
        bc[i].in <== borrow[i];
    }

    out[k - 1] <== a[k - 1] - borrow[k - 2] - b[k - 1];
    rc[k - 1] = Num2Bits(n);
    rc[k - 1].in <== out[k - 1];
}

/// Multiplies two k-limb numbers with n-bit limbs.
/// Output is 2k limbs (schoolbook multiplication).
template BigMult(n, k) {
    signal input a[k];
    signal input b[k];
    signal output out[2 * k];

    signal products[k][k];
    for (var i = 0; i < k; i++) {
        for (var j = 0; j < k; j++) {
            products[i][j] <== a[i] * b[j];
        }
    }

    var rawLimbs[200];
    for (var i = 0; i < 2 * k; i++) {
        rawLimbs[i] = 0;
    }
    for (var i = 0; i < k; i++) {
        for (var j = 0; j < k; j++) {
            rawLimbs[i + j] += products[i][j];
        }
    }

    signal carry[2 * k - 1];
    component rc[2 * k];

    out[0] <-- rawLimbs[0] % (1 << n);
    carry[0] <-- rawLimbs[0] >> n;
    rawLimbs[0] === out[0] + carry[0] * (1 << n);
    rc[0] = Num2Bits(n);
    rc[0].in <== out[0];

    for (var i = 1; i < 2 * k - 1; i++) {
        out[i] <-- (rawLimbs[i] + carry[i - 1]) % (1 << n);
        carry[i] <-- (rawLimbs[i] + carry[i - 1]) >> n;
        rawLimbs[i] + carry[i - 1] === out[i] + carry[i] * (1 << n);
        rc[i] = Num2Bits(n);
        rc[i].in <== out[i];
    }

    out[2 * k - 1] <== rawLimbs[2 * k - 1] + carry[2 * k - 2];
    rc[2 * k - 1] = Num2Bits(n);
    rc[2 * k - 1].in <== out[2 * k - 1];
}

/// Multiplies two multi-limb numbers without carry propagation.
/// a has ka limbs of ma bits, b has kb limbs of mb bits.
/// Output has (ka + kb - 1) limbs, each potentially wider than n bits.
template BigMultNoCarry(n, ma, mb, ka, kb) {
    assert(ma + mb <= 253);

    signal input a[ka];
    signal input b[kb];
    signal output out[ka + kb - 1];

    signal products[ka][kb];
    for (var i = 0; i < ka; i++) {
        for (var j = 0; j < kb; j++) {
            products[i][j] <== a[i] * b[j];
        }
    }

    var sums[200];
    for (var i = 0; i < ka + kb - 1; i++) {
        sums[i] = 0;
    }
    for (var i = 0; i < ka; i++) {
        for (var j = 0; j < kb; j++) {
            sums[i + j] += products[i][j];
        }
    }

    for (var i = 0; i < ka + kb - 1; i++) {
        out[i] <== sums[i];
    }
}

/// Computes a mod b where a is (k+1) limbs and b is k limbs.
/// Both have n-bit limbs. Output remainder is k limbs.
template BigMod(n, k) {
    signal input a[k + 1];
    signal input b[k];
    signal output out[k];

    var div_result[2][200] = long_div(n, k, a, b);

    signal quotient[2];
    for (var i = 0; i < 2; i++) {
        quotient[i] <-- div_result[0][i];
    }
    for (var i = 0; i < k; i++) {
        out[i] <-- div_result[1][i];
    }

    // Range checks
    component rcRem[k];
    for (var i = 0; i < k; i++) {
        rcRem[i] = Num2Bits(n);
        rcRem[i].in <== out[i];
    }
    component rcQuot[2];
    for (var i = 0; i < 2; i++) {
        rcQuot[i] = Num2Bits(n);
        rcQuot[i].in <== quotient[i];
    }

    // Constrain: a = quotient * b + remainder
    signal qb_products[2][k];
    for (var i = 0; i < 2; i++) {
        for (var j = 0; j < k; j++) {
            qb_products[i][j] <== quotient[i] * b[j];
        }
    }

    var qb_raw[200];
    for (var i = 0; i < k + 1; i++) {
        qb_raw[i] = 0;
    }
    for (var i = 0; i < 2; i++) {
        for (var j = 0; j < k; j++) {
            qb_raw[i + j] += qb_products[i][j];
        }
    }
    for (var i = 0; i < k; i++) {
        qb_raw[i] += out[i];
    }

    signal diff[k + 1];
    for (var i = 0; i < k + 1; i++) {
        diff[i] <== qb_raw[i] - a[i];
    }
    CheckCarryToZero(n, n + 2, k + 1)(diff);
}

/// (a - b) mod p, where a, b, p are k-limb numbers with n-bit limbs.
template BigSubModP(n, k) {
    signal input a[k];
    signal input b[k];
    signal input p[k];
    signal output out[k];

    // Witness: compute (a - b) mod p using only non-negative arithmetic
    var a_val = 0;
    var b_val = 0;
    var p_val = 0;
    for (var i = k - 1; i >= 0; i--) {
        a_val = a_val * (1 << n) + a[i];
        b_val = b_val * (1 << n) + b[i];
        p_val = p_val * (1 << n) + p[i];
    }
    var result_val;
    if (a_val >= b_val) {
        result_val = (a_val - b_val) % p_val;
    } else {
        var diff = (b_val - a_val) % p_val;
        if (diff == 0) {
            result_val = 0;
        } else {
            result_val = p_val - diff;
        }
    }

    for (var i = 0; i < k; i++) {
        out[i] <-- (result_val >> (i * n)) % (1 << n);
    }

    component rcOut[k];
    for (var i = 0; i < k; i++) {
        rcOut[i] = Num2Bits(n);
        rcOut[i].in <== out[i];
    }

    // Constrain: out + b ≡ a (mod p)
    // out + b = a + q*p → (out + b - a) must be a multiple of p
    signal sum[k + 1];
    sum <== BigAdd(n, k)(out, b);

    signal sumDiff[k + 1];
    for (var i = 0; i < k; i++) {
        sumDiff[i] <== sum[i] - a[i];
    }
    sumDiff[k] <== sum[k];

    signal remainder[k];
    remainder <== BigMod(n, k)(sumDiff, p);
    for (var i = 0; i < k; i++) {
        remainder[i] === 0;
    }
}

/// (a * b) mod p, where a, b, p are k-limb numbers with n-bit limbs.
template BigMultModP(n, k) {
    signal input a[k];
    signal input b[k];
    signal input p[k];
    signal output out[k];

    // Witness
    var a_val = 0;
    var b_val = 0;
    var p_val = 0;
    for (var i = k - 1; i >= 0; i--) {
        a_val = a_val * (1 << n) + a[i];
        b_val = b_val * (1 << n) + b[i];
        p_val = p_val * (1 << n) + p[i];
    }
    var result_val = (a_val * b_val) % p_val;
    var q_val = (a_val * b_val) \ p_val;

    for (var i = 0; i < k; i++) {
        out[i] <-- (result_val >> (i * n)) % (1 << n);
    }

    component rcOut[k];
    for (var i = 0; i < k; i++) {
        rcOut[i] = Num2Bits(n);
        rcOut[i].in <== out[i];
    }

    // Quotient witness
    signal quotient[k];
    for (var i = 0; i < k; i++) {
        quotient[i] <-- (q_val >> (i * n)) % (1 << n);
    }
    component rcQ[k];
    for (var i = 0; i < k; i++) {
        rcQ[i] = Num2Bits(n);
        rcQ[i].in <== quotient[i];
    }

    // Constrain: a * b = q * p + out
    signal ab[2 * k];
    ab <== BigMult(n, k)(a, b);

    signal qp[2 * k];
    qp <== BigMult(n, k)(quotient, p);

    signal diff[2 * k];
    for (var i = 0; i < k; i++) {
        diff[i] <== ab[i] - qp[i] - out[i];
    }
    for (var i = k; i < 2 * k; i++) {
        diff[i] <== ab[i] - qp[i];
    }
    CheckCarryToZero(n, n + 2, 2 * k)(diff);
}

/// Modular inverse: out = a^(-1) mod p.
template BigModInv(n, k) {
    signal input a[k];
    signal input p[k];
    signal output out[k];

    var inv[200] = mod_inv(n, k, a, p);
    for (var i = 0; i < k; i++) {
        out[i] <-- inv[i];
    }

    component rcOut[k];
    for (var i = 0; i < k; i++) {
        rcOut[i] = Num2Bits(n);
        rcOut[i].in <== out[i];
    }

    // Constrain: a * out ≡ 1 (mod p)
    signal product[k];
    product <== BigMultModP(n, k)(a, out, p);

    product[0] === 1;
    for (var i = 1; i < k; i++) {
        product[i] === 0;
    }
}

/// Compares two k-limb numbers with n-bit limbs.
/// out = 1 if a < b, 0 otherwise. Limbs are little-endian.
template BigLessThan(n, k) {
    signal input a[k];
    signal input b[k];
    signal output out;

    component lt[k];
    component eq[k];

    for (var i = 0; i < k; i++) {
        lt[i] = LessThan(n);
        lt[i].in[0] <== a[i];
        lt[i].in[1] <== b[i];

        eq[i] = IsEqual();
        eq[i].in[0] <== a[i];
        eq[i].in[1] <== b[i];
    }

    // Build comparison from LSB to MSB.
    // At each limb: if limbs are equal, defer to lower result; otherwise use this limb's lt.
    signal result[k];
    result[0] <== lt[0].out;
    for (var i = 1; i < k; i++) {
        result[i] <== lt[i].out + eq[i].out * result[i - 1];
    }

    out <== result[k - 1];
}

/// Checks equality of two k-limb numbers.
/// out = 1 if a == b, 0 otherwise.
template BigIsEqual(k) {
    signal input a[k];
    signal input b[k];
    signal output out;

    component eq[k];
    for (var i = 0; i < k; i++) {
        eq[i] = IsEqual();
        eq[i].in[0] <== a[i];
        eq[i].in[1] <== b[i];
    }

    signal acc[k];
    acc[0] <== eq[0].out;
    for (var i = 1; i < k; i++) {
        acc[i] <== acc[i - 1] * eq[i].out;
    }
    out <== acc[k - 1];
}
