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

/// Returns the idx-th CRT prime (89-bit primes starting near 2^88).
function crt_prime(idx) {
    var primes[50];
    primes[0] = 309485009821345068724781063;
    primes[1] = 309485009821345068724781189;
    primes[2] = 309485009821345068724781221;
    primes[3] = 309485009821345068724781329;
    primes[4] = 309485009821345068724781371;
    primes[5] = 309485009821345068724781401;
    primes[6] = 309485009821345068724781557;
    primes[7] = 309485009821345068724781569;
    primes[8] = 309485009821345068724781597;
    primes[9] = 309485009821345068724781813;
    primes[10] = 309485009821345068724781827;
    primes[11] = 309485009821345068724781839;
    primes[12] = 309485009821345068724781897;
    primes[13] = 309485009821345068724781909;
    primes[14] = 309485009821345068724781917;
    primes[15] = 309485009821345068724781941;
    primes[16] = 309485009821345068724782101;
    primes[17] = 309485009821345068724782107;
    primes[18] = 309485009821345068724782149;
    primes[19] = 309485009821345068724782361;
    primes[20] = 309485009821345068724782523;
    primes[21] = 309485009821345068724782539;
    primes[22] = 309485009821345068724782547;
    primes[23] = 309485009821345068724782707;
    primes[24] = 309485009821345068724782719;
    primes[25] = 309485009821345068724782779;
    primes[26] = 309485009821345068724782787;
    primes[27] = 309485009821345068724782947;
    primes[28] = 309485009821345068724783247;
    primes[29] = 309485009821345068724783307;
    primes[30] = 309485009821345068724783409;
    primes[31] = 309485009821345068724783411;
    primes[32] = 309485009821345068724783433;
    primes[33] = 309485009821345068724783507;
    primes[34] = 309485009821345068724783657;
    primes[35] = 309485009821345068724783697;
    primes[36] = 309485009821345068724783817;
    primes[37] = 309485009821345068724783867;
    primes[38] = 309485009821345068724783909;
    primes[39] = 309485009821345068724784077;
    primes[40] = 309485009821345068724784171;
    primes[41] = 309485009821345068724784389;
    primes[42] = 309485009821345068724784447;
    primes[43] = 309485009821345068724784513;
    primes[44] = 309485009821345068724784621;
    primes[45] = 309485009821345068724784647;
    primes[46] = 309485009821345068724784669;
    primes[47] = 309485009821345068724784671;
    primes[48] = 309485009821345068724784711;
    primes[49] = 309485009821345068724784831;
    return primes[idx];
}

/// Number of CRT moduli needed for soundness given n-bit limbs and k limbs.
/// The product p_field * Π(primes) must exceed 2^(2nk+2).
/// p_field provides ~254 bits; each 89-bit prime adds ~89 bits.
function crt_num_primes(n, k) {
    var total_bits = 2 * n * k + 2;
    if (total_bits <= 254) {
        return 0;
    }
    var extra = total_bits - 254;
    var num = (extra + 88) \ 89;
    assert(num <= 50);
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
/// Enforces canonical reduction: out < p.
template BigMultModP_CRT(n, k) {
    signal input a[k];
    signal input b[k];
    signal input p[k];
    signal output out[k];

    var num_primes = crt_num_primes(n, k);

    // ── Witness computation ──
    // Use multi-limb prod + long_div2 to avoid field overflow for nk > 254.
    var ab_limbs[200] = prod(n, k, a, b);
    var p_limbs[200];
    for (var i = 0; i < 200; i++) p_limbs[i] = 0;
    for (var i = 0; i < k; i++) p_limbs[i] = p[i];

    var div_result[2][200] = long_div2(n, k, k, ab_limbs, p_limbs);

    for (var i = 0; i < k; i++) {
        out[i] <-- div_result[1][i];
    }

    signal quotient[k];
    for (var i = 0; i < k; i++) {
        quotient[i] <-- div_result[0][i];
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

/// Like BigMultModP_CRT but without canonical reduction (out < p).
///
/// Proves out ≡ (a * b) mod p with 0 ≤ out < 2^(nk), but does not enforce
/// out < p. Use in chains where only the final result needs canonicality.
/// Saves one BigLessThan(n, k) call (~25% of constraint cost).
template BigMultModP_CRT_nocanon(n, k) {
    signal input a[k];
    signal input b[k];
    signal input p[k];
    signal output out[k];

    var num_primes = crt_num_primes(n, k);

    // ── Witness computation (identical to BigMultModP_CRT) ──
    var ab_limbs[200] = prod(n, k, a, b);
    var p_limbs[200];
    for (var i = 0; i < 200; i++) p_limbs[i] = 0;
    for (var i = 0; i < k; i++) p_limbs[i] = p[i];

    var div_result[2][200] = long_div2(n, k, k, ab_limbs, p_limbs);

    for (var i = 0; i < k; i++) {
        out[i] <-- div_result[1][i];
    }

    signal quotient[k];
    for (var i = 0; i < k; i++) {
        quotient[i] <-- div_result[0][i];
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
    signal crt_ab[num_primes];
    signal crt_qp[num_primes];
    signal crt_kj[num_primes];
    component crt_rc[num_primes];

    for (var j = 0; j < num_primes; j++) {
        var mj = crt_prime(j);

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

        crt_ab[j] <== Aj * Bj;
        crt_qp[j] <== Qj * Pj;

        var BIAS = k * k * (1 << (2 * n)) * mj + k * (1 << n);

        crt_kj[j] <-- (crt_ab[j] - crt_qp[j] - Rj + BIAS * mj) \ mj;
        crt_ab[j] + BIAS * mj === crt_qp[j] + Rj + crt_kj[j] * mj;

        var range_bits = crt_kj_range_bits(n, k, mj);
        crt_rc[j] = Num2Bits(range_bits);
        crt_rc[j].in <== crt_kj[j];
    }

    // No Step 4: canonical reduction omitted for intermediate chain use.
}

/// Fixed-exponent modular exponentiation: out = base^65537 mod modulus.
/// 65537 = 2^16 + 1, computed as 16 squarings followed by 1 multiply.
/// Uses nocanon for the 16 intermediate multiplications; only the final
/// output is canonically reduced (out < modulus).
/// Total: 16 BigMultModP_CRT_nocanon + 1 BigMultModP_CRT.
template BigModExp65537(n, k) {
    signal input base[k];
    signal input modulus[k];
    signal output out[k];

    // 16 squarings (nocanon) + 1 final multiply (canonical)
    component mm_nc[16];
    component mm_final;

    // First squaring: base²
    mm_nc[0] = BigMultModP_CRT_nocanon(n, k);
    for (var j = 0; j < k; j++) {
        mm_nc[0].a[j] <== base[j];
        mm_nc[0].b[j] <== base[j];
        mm_nc[0].p[j] <== modulus[j];
    }

    // Chain squarings: base^4, base^8, ..., base^(2^16)
    for (var i = 1; i < 16; i++) {
        mm_nc[i] = BigMultModP_CRT_nocanon(n, k);
        for (var j = 0; j < k; j++) {
            mm_nc[i].a[j] <== mm_nc[i - 1].out[j];
            mm_nc[i].b[j] <== mm_nc[i - 1].out[j];
            mm_nc[i].p[j] <== modulus[j];
        }
    }

    // Final multiply: base^(2^16) * base = base^65537 (canonical)
    mm_final = BigMultModP_CRT(n, k);
    for (var j = 0; j < k; j++) {
        mm_final.a[j] <== mm_nc[15].out[j];
        mm_final.b[j] <== base[j];
        mm_final.p[j] <== modulus[j];
    }

    for (var j = 0; j < k; j++) {
        out[j] <== mm_final.out[j];
    }
}

/// Variable-exponent modular exponentiation: out = base^exp mod modulus.
/// exp[i] is bit i of the exponent (LSB = exp[0]).
/// Uses square-and-multiply processing bits from MSB to LSB.
/// Intermediate multiplications use nocanon; final output is canonical.
/// Total: 2*eBits BigMultModP_CRT_nocanon + eBits mux + 1 BigLessThan.
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

        // Square the accumulator (nocanon)
        sq[i] = BigMultModP_CRT_nocanon(n, k);
        for (var j = 0; j < k; j++) {
            sq[i].a[j] <== acc[i][j];
            sq[i].b[j] <== acc[i][j];
            sq[i].p[j] <== modulus[j];
        }

        // Multiply by base (nocanon)
        mul[i] = BigMultModP_CRT_nocanon(n, k);
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

    // Canonical reduction on final output (out < modulus)
    signal lt_final <== BigLessThan(n, k)(acc[eBits], modulus);
    lt_final === 1;

    for (var j = 0; j < k; j++) {
        out[j] <== acc[eBits][j];
    }
}
