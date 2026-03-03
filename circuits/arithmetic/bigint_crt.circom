pragma circom 2.2.2;

include "arithmetic/bigint.circom";

// ═══════════════════════════════════════════════════
// Compile-time helper functions
// ═══════════════════════════════════════════════════

/// Modular exponentiation at compile time: base^exp mod modulus.
function pow_mod(base, exp, modulus) {
    var result = 1;
    var b = base % modulus;
    var e = exp;
    while (e > 0) {
        if (e % 2 == 1) {
            result = (result * b) % modulus;
        }
        b = (b * b) % modulus;
        e = e \ 2;
    }
    return result;
}

/// Returns the idx-th CRT prime (50-bit primes starting near 2^49).
function crt_prime(idx) {
    var primes[80];
    primes[0] = 562949953421381;
    primes[1] = 562949953421503;
    primes[2] = 562949953421573;
    primes[3] = 562949953421591;
    primes[4] = 562949953421641;
    primes[5] = 562949953421711;
    primes[6] = 562949953421719;
    primes[7] = 562949953421729;
    primes[8] = 562949953421771;
    primes[9] = 562949953421773;
    primes[10] = 562949953421831;
    primes[11] = 562949953421851;
    primes[12] = 562949953421857;
    primes[13] = 562949953421861;
    primes[14] = 562949953421887;
    primes[15] = 562949953421929;
    primes[16] = 562949953421951;
    primes[17] = 562949953421957;
    primes[18] = 562949953421959;
    primes[19] = 562949953422097;
    primes[20] = 562949953422119;
    primes[21] = 562949953422121;
    primes[22] = 562949953422139;
    primes[23] = 562949953422161;
    primes[24] = 562949953422253;
    primes[25] = 562949953422287;
    primes[26] = 562949953422293;
    primes[27] = 562949953422301;
    primes[28] = 562949953422473;
    primes[29] = 562949953422497;
    primes[30] = 562949953422523;
    primes[31] = 562949953422553;
    primes[32] = 562949953422557;
    primes[33] = 562949953422583;
    primes[34] = 562949953422589;
    primes[35] = 562949953422679;
    primes[36] = 562949953422719;
    primes[37] = 562949953422733;
    primes[38] = 562949953422743;
    primes[39] = 562949953422757;
    primes[40] = 562949953422839;
    primes[41] = 562949953422841;
    primes[42] = 562949953422937;
    primes[43] = 562949953422991;
    primes[44] = 562949953423049;
    primes[45] = 562949953423087;
    primes[46] = 562949953423139;
    primes[47] = 562949953423157;
    primes[48] = 562949953423177;
    primes[49] = 562949953423223;
    primes[50] = 562949953423229;
    primes[51] = 562949953423283;
    primes[52] = 562949953423313;
    primes[53] = 562949953423357;
    primes[54] = 562949953423381;
    primes[55] = 562949953423391;
    primes[56] = 562949953423409;
    primes[57] = 562949953423423;
    primes[58] = 562949953423427;
    primes[59] = 562949953423447;
    primes[60] = 562949953423489;
    primes[61] = 562949953423577;
    primes[62] = 562949953423619;
    primes[63] = 562949953423661;
    primes[64] = 562949953423691;
    primes[65] = 562949953423699;
    primes[66] = 562949953423709;
    primes[67] = 562949953423717;
    primes[68] = 562949953423723;
    primes[69] = 562949953423751;
    primes[70] = 562949953423777;
    primes[71] = 562949953423841;
    primes[72] = 562949953423883;
    primes[73] = 562949953423901;
    primes[74] = 562949953423951;
    primes[75] = 562949953423981;
    primes[76] = 562949953423999;
    primes[77] = 562949953424099;
    primes[78] = 562949953424119;
    primes[79] = 562949953424161;
    return primes[idx];
}

/// Number of CRT moduli needed for soundness given n-bit limbs and k limbs.
/// The product p_field * Π(primes) must exceed 2^(2nk+2).
/// p_field provides ~254 bits; each 50-bit prime adds ~50 bits.
function crt_num_primes(n, k) {
    var total_bits = 2 * n * k + 2;
    if (total_bits <= 254) {
        return 0;
    }
    var extra = total_bits - 254;
    var num = (extra + 49) \ 50;
    assert(num <= 80);
    return num;
}

/// Bit-width for range-checking the CRT quotient kj.
/// kj = (ab_j - qp_j - R_j + BIAS*mj) / mj, with max value
/// 2*k²*2^(2n)*mj + k*2^n.
function crt_kj_range_bits(n, k, mj) {
    var max_kj = 2 * k * k * (1 << (2 * n)) * mj + k * (1 << n);
    var bits = 0;
    var temp = max_kj;
    while (temp > 0) {
        bits++;
        temp = temp \ 2;
    }
    return bits;
}

// ═══════════════════════════════════════════════════
// Templates
// ═══════════════════════════════════════════════════

/// CRT-verified modular multiplication: out = (a * b) mod p.
///
/// Drop-in compatible with BigMultModP but uses Chinese Remainder Theorem
/// verification instead of schoolbook multiplication. Verifies a*b = q*p + r
/// by checking the equation modulo p_field (native) and several small primes.
/// Each modular check is cheap because reducing a big integer mod a compile-time
/// constant is a linear combination with known coefficients (free in R1CS).
///
/// Constraint savings: ~40-60% for large parameters (k >= 4).
template BigMultModP_CRT(n, k) {
    signal input a[k];
    signal input b[k];
    signal input p[k];
    signal output out[k];

    var num_primes = crt_num_primes(n, k);

    // ── Witness computation ──
    // Use limb-wise multiplication (prod) to avoid field overflow when nk > 127.
    // Then limb-by-limb long division with a running remainder that fits in the
    // field (requires nk + n < 254, i.e. nk < 222 for n=32).
    var ab_limbs[200] = prod(n, k, a, b);

    var p_val = 0;
    for (var i = k - 1; i >= 0; i--) {
        p_val = p_val * (1 << n) + p[i];
    }

    var rem = 0;
    var q_limbs[200];
    for (var i = 0; i < 200; i++) {
        q_limbs[i] = 0;
    }
    for (var i = 2 * k - 1; i >= 0; i--) {
        rem = rem * (1 << n) + ab_limbs[i];
        q_limbs[i] = rem \ p_val;
        rem = rem % p_val;
    }
    for (var i = 0; i < 2 * k - 1; i++) {
        q_limbs[i + 1] += q_limbs[i] >> n;
        q_limbs[i] = q_limbs[i] % (1 << n);
    }
    var result_val = rem;

    for (var i = 0; i < k; i++) {
        out[i] <-- (result_val >> (i * n)) % (1 << n);
    }

    signal quotient[k];
    for (var i = 0; i < k; i++) {
        quotient[i] <-- q_limbs[i];
    }

    // ── Step 1: Range checks on output and quotient limbs ──
    component rcOut[k];
    component rcQ[k];
    for (var i = 0; i < k; i++) {
        rcOut[i] = Num2Bits(n);
        rcOut[i].in <== out[i];
        rcQ[i] = Num2Bits(n);
        rcQ[i].in <== quotient[i];
    }

    // ── Step 2: Native field check (2 constraints) ──
    // Reconstruct big integers as field elements via linear combinations.
    // Coefficients 2^(ni) wrap modulo p_field, giving a free mod-p_field check.
    var A = 0;
    var B = 0;
    var Q = 0;
    var P = 0;
    var R = 0;
    for (var i = 0; i < k; i++) {
        var base_i = 1 << (n * i);
        A += a[i] * base_i;
        B += b[i] * base_i;
        Q += quotient[i] * base_i;
        P += p[i] * base_i;
        R += out[i] * base_i;
    }

    signal ab <== A * B;
    signal qp <== Q * P;
    ab === qp + R;

    // ── Step 3: CRT modular checks (one per small prime) ──
    // For each prime mj, verify a*b ≡ q*p + r (mod mj).
    // Reducing a k-limb number mod mj is a linear combination with
    // compile-time coefficients (2^(ni) mod mj), costing 0 constraints.
    signal crt_ab[num_primes];
    signal crt_qp[num_primes];
    signal crt_kj[num_primes];
    component crt_rc[num_primes];

    for (var j = 0; j < num_primes; j++) {
        var mj = crt_prime(j);

        // Reduce each big integer mod mj (free: compile-time coefficients)
        var Aj = 0;
        var Bj = 0;
        var Qj = 0;
        var Pj = 0;
        var Rj = 0;
        for (var i = 0; i < k; i++) {
            var coeff = pow_mod(1 << n, i, mj);
            Aj += a[i] * coeff;
            Bj += b[i] * coeff;
            Qj += quotient[i] * coeff;
            Pj += p[i] * coeff;
            Rj += out[i] * coeff;
        }

        // Products mod mj (2 constraints)
        crt_ab[j] <== Aj * Bj;
        crt_qp[j] <== Qj * Pj;

        // Bias ensures non-negative before integer division.
        // BIAS*mj >= max|ab_j - qp_j - R_j|, keeping the division operand positive.
        var BIAS = k * k * (1 << (2 * n)) * mj + k * (1 << n);

        crt_kj[j] <-- (crt_ab[j] - crt_qp[j] - Rj + BIAS * mj) \ mj;
        crt_ab[j] + BIAS * mj === crt_qp[j] + Rj + crt_kj[j] * mj;

        // Range check on kj
        var range_bits = crt_kj_range_bits(n, k, mj);
        crt_rc[j] = Num2Bits(range_bits);
        crt_rc[j].in <== crt_kj[j];
    }

    // ── Step 4: Canonical reduction (out < p) ──
    signal lt_rem <== BigLessThan(n, k)(out, p);
    lt_rem === 1;
}

/// Fixed-exponent modular exponentiation: out = base^65537 mod modulus.
/// 65537 = 2^16 + 1, computed as 16 squarings followed by 1 multiply.
/// Total: 17 BigMultModP_CRT calls.
template BigModExp65537(n, k) {
    signal input base[k];
    signal input modulus[k];
    signal output out[k];

    // 16 squarings + 1 final multiply
    component mm[17];

    // First squaring: base²
    mm[0] = BigMultModP_CRT(n, k);
    for (var j = 0; j < k; j++) {
        mm[0].a[j] <== base[j];
        mm[0].b[j] <== base[j];
        mm[0].p[j] <== modulus[j];
    }

    // Chain squarings: base^4, base^8, ..., base^(2^16)
    for (var i = 1; i < 16; i++) {
        mm[i] = BigMultModP_CRT(n, k);
        for (var j = 0; j < k; j++) {
            mm[i].a[j] <== mm[i - 1].out[j];
            mm[i].b[j] <== mm[i - 1].out[j];
            mm[i].p[j] <== modulus[j];
        }
    }

    // Final multiply: base^(2^16) * base = base^65537
    mm[16] = BigMultModP_CRT(n, k);
    for (var j = 0; j < k; j++) {
        mm[16].a[j] <== mm[15].out[j];
        mm[16].b[j] <== base[j];
        mm[16].p[j] <== modulus[j];
    }

    for (var j = 0; j < k; j++) {
        out[j] <== mm[16].out[j];
    }
}

/// Variable-exponent modular exponentiation: out = base^exp mod modulus.
/// exp[i] is bit i of the exponent (LSB = exp[0]).
/// Uses square-and-multiply processing bits from MSB to LSB.
/// Total: 2*eBits BigMultModP_CRT calls + eBits mux operations.
template BigModExp(n, k, eBits) {
    signal input base[k];
    signal input exp[eBits];
    signal input modulus[k];
    signal output out[k];

    // Constrain exponent bits to be binary
    for (var i = 0; i < eBits; i++) {
        exp[i] * (exp[i] - 1) === 0;
    }

    // Accumulator starts at 1 (the multiplicative identity)
    signal acc[eBits + 1][k];
    acc[0][0] <== 1;
    for (var j = 1; j < k; j++) {
        acc[0][j] <== 0;
    }

    // Square-and-multiply: process exponent bits from MSB to LSB
    component sq[eBits];
    component mul[eBits];

    for (var i = 0; i < eBits; i++) {
        var bit_idx = eBits - 1 - i;

        // Square the accumulator
        sq[i] = BigMultModP_CRT(n, k);
        for (var j = 0; j < k; j++) {
            sq[i].a[j] <== acc[i][j];
            sq[i].b[j] <== acc[i][j];
            sq[i].p[j] <== modulus[j];
        }

        // Multiply by base
        mul[i] = BigMultModP_CRT(n, k);
        for (var j = 0; j < k; j++) {
            mul[i].a[j] <== sq[i].out[j];
            mul[i].b[j] <== base[j];
            mul[i].p[j] <== modulus[j];
        }

        // Mux: select multiplied (bit=1) or squared (bit=0)
        for (var j = 0; j < k; j++) {
            acc[i + 1][j] <== sq[i].out[j]
                + exp[bit_idx] * (mul[i].out[j] - sq[i].out[j]);
        }
    }

    for (var j = 0; j < k; j++) {
        out[j] <== acc[eBits][j];
    }
}
