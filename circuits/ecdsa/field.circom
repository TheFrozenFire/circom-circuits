pragma circom 2.2.2;

include "arithmetic/bigint_func.circom";
include "arithmetic/bigint_crt.circom";
include "core/comparators.circom";
include "packing/bitify.circom";

// ═══════════════════════════════════════════════════
// Prime reduction templates (all linear — zero constraints)
// Exploit p = 2^256 - 2^32 - 977, so 2^256 ≡ (2^32 + 977) mod p.
// ═══════════════════════════════════════════════════

/// Reduces 15-register quadratic product (8×8→15) to 8 registers.
/// Adds 33 bits to overflow per register.
/// Input registers can be negative; overall input can be negative.
template Secp256k1PrimeReduce15To8() {
    signal input in[15];
    signal output out[8];

    // 2^256 ≡ offset (mod p), where offset = 2^32 + 977 (33 bits)
    var offset = (1 << 32) + 977;

    // Fold registers 8..14 back into 0..6: in[j+8] * 2^(32*(j+8)) ≡ in[j+8] * offset * 2^(32j)
    for (var j = 0; j < 7; j++) {
        out[j] <== in[j] + offset * in[j + 8];
    }
    out[7] <== in[7];
}

/// Reduces 22-register cubic product (15×8→22) to 8 registers.
/// Adds 66 bits to overflow for registers 0..5, 33 bits for registers 6..7.
/// Input registers can be negative; overall input can be negative.
template Secp256k1PrimeReduce22To8() {
    signal input in[22];
    signal output out[8];

    var offset = (1 << 32) + 977;          // 33 bits: 2^256 mod p
    var offset2 = offset * offset;          // 65 bits: 2^512 mod p

    // Direct fold using 2^(32*i) ≡ offset^(i\8) * 2^(32*(i%8)):
    //   registers 0..7:   coefficient 1
    //   registers 8..15:  coefficient offset (× 2^256)
    //   registers 16..21: coefficient offset² (× 2^512)
    for (var j = 0; j < 6; j++) {
        out[j] <== in[j] + offset * in[j + 8] + offset2 * in[j + 16];
    }
    out[6] <== in[6] + offset * in[14];
    out[7] <== in[7] + offset * in[15];
}

// ═══════════════════════════════════════════════════
// CRT-based modular zero checks
//
// Verifies expr ≡ 0 mod p using CRT instead of BigMultNoCarry + CheckCarryToZero.
// The equation positive = q * p is checked:
//   1. Modulo p_BN254 (native field constraint — linear, 0 non-linear constraints)
//   2. Modulo each CRT prime mj (linear constraint + kj range check)
// Only costs: Num2Bits on q (quotient) + Num2Bits on kj per CRT prime.
// ═══════════════════════════════════════════════════

/// Verifies a 15-register expression ≡ 0 mod p (for quadratic products at n=32).
/// Registers have m-bit overflow. Uses 1 CRT prime (89-bit).
/// Cost: Num2Bits(q_bits) + Num2Bits(kj_bits) ≈ 186 non-linear constraints.
template CheckQuadraticModPIsZero(m) {
    assert(m < 120);

    signal input in[15];

    var p[8];
    p[0] = 4294966319;  // 0xFFFFFC2F
    p[1] = 4294967294;  // 0xFFFFFFFE
    p[2] = 4294967295;  // 0xFFFFFFFF
    p[3] = 4294967295;
    p[4] = 4294967295;
    p[5] = 4294967295;
    p[6] = 4294967295;
    p[7] = 4294967295;

    // ── Step 1: Reduce 15 → 8 registers (adds 33 bits → m+34 bits max) ──
    signal reduced[8];
    reduced <== Secp256k1PrimeReduce15To8()(in);

    // ── Step 2: Add multiple of p to ensure positivity ──
    // |reduced[i]| < 2^(m+34). Need p[i] * factor > 2^(m+34).
    // p[i] ≈ 2^32, so factor > 2^(m+2). Use factor = 1 << (m + 2).
    // positive[i] < 2^(m+35).
    signal positive[8];
    for (var i = 0; i < 8; i++) {
        positive[i] <== reduced[i] + p[i] * (1 << (m + 2));
    }

    // ── Step 3: Witness quotient q ──
    // q = Σ positive[i] * 2^(32i) / p.
    // q < 8 * 2^(m+35+224) / 2^256 = 2^(m+6).
    var q_bits = m + 6;
    var proper_regs = 8 + div_ceil(m + 35, 32);
    var temp[200] = getProperRepresentation(m + 35, 32, 8, positive);
    var proper[200];
    for (var i = 0; i < 200; i++) proper[i] = temp[i];

    var p_arr[200];
    for (var i = 0; i < 200; i++) p_arr[i] = 0;
    for (var i = 0; i < 8; i++) p_arr[i] = p[i];

    var divResult[2][200] = long_div2(32, 8, proper_regs - 8, proper, p_arr);

    signal q;
    var q_val = 0;
    for (var i = 0; i < proper_regs - 8; i++) {
        q_val += divResult[0][i] * (1 << (32 * i));
    }
    q <-- q_val;

    // Range check q
    signal _q_bits[q_bits] <== Num2Bits(q_bits)(q);

    // ── Step 4: Native field check (linear — 0 non-linear constraints) ──
    // Σ positive[i] * 2^(32i) === q * p_native  (mod p_BN254)
    var p_native = 0;
    var expr_native = 0;
    for (var i = 0; i < 8; i++) {
        var base_i = 1 << (32 * i);
        expr_native += positive[i] * base_i;
        p_native += p[i] * base_i;
    }
    expr_native === q * p_native;

    // ── Step 5: CRT check with 1 × 89-bit prime ──
    var mj = crt_prime(0);

    var expr_j = 0;
    for (var i = 0; i < 8; i++) {
        expr_j += positive[i] * pow_mod(1 << 32, i, mj);
    }
    var p_j = pow_mod(1 << 32, 0, mj) * p[0];
    for (var i = 1; i < 8; i++) {
        p_j += pow_mod(1 << 32, i, mj) * p[i];
    }

    // BIAS ensures non-negative before integer division.
    // |expr_j - q * p_j| < 2^(m+38) * mj. BIAS = 1 << (m + 38).
    var BIAS = 1 << (m + 38);

    signal kj;
    kj <-- (expr_j - q * p_j + BIAS * mj) \ mj;
    expr_j + BIAS * mj === q * p_j + kj * mj;

    // kj ∈ [0, 2*BIAS + 2^(m+38)] < 2^(m+40)
    signal _kj_bits[m + 40] <== Num2Bits(m + 40)(kj);
}

/// Verifies a 22-register expression ≡ 0 mod p (for cubic products at n=32).
/// Registers have m-bit overflow. Uses 2 CRT primes (76-bit).
/// Cost: Num2Bits(q_bits) + 2 × Num2Bits(kj_bits) ≈ 497 non-linear constraints.
template CheckCubicModPIsZero(m) {
    assert(m < 180);

    signal input in[22];

    var p[8];
    p[0] = 4294966319;  // 0xFFFFFC2F
    p[1] = 4294967294;  // 0xFFFFFFFE
    p[2] = 4294967295;  // 0xFFFFFFFF
    p[3] = 4294967295;
    p[4] = 4294967295;
    p[5] = 4294967295;
    p[6] = 4294967295;
    p[7] = 4294967295;

    // ── Step 1: Reduce 22 → 8 registers (adds 66 bits → m+67 bits max) ──
    signal reduced[8];
    reduced <== Secp256k1PrimeReduce22To8()(in);

    // ── Step 2: Add multiple of p to ensure positivity ──
    // |reduced[i]| < 2^(m+67). Need p[i] * factor > 2^(m+67).
    // p[i] ≈ 2^32, so factor > 2^(m+35). Use factor = 1 << (m + 35).
    // positive[i] < 2^(m+68).
    signal positive[8];
    for (var i = 0; i < 8; i++) {
        positive[i] <== reduced[i] + p[i] * (1 << (m + 35));
    }

    // ── Step 3: Witness quotient q ──
    // q < 8 * 2^(m+68+224) / 2^256 = 2^(m+39).
    var q_bits = m + 39;
    var proper_regs = 8 + div_ceil(m + 68, 32);
    var temp[200] = getProperRepresentation(m + 68, 32, 8, positive);
    var proper[200];
    for (var i = 0; i < 200; i++) proper[i] = temp[i];

    var p_arr[200];
    for (var i = 0; i < 200; i++) p_arr[i] = 0;
    for (var i = 0; i < 8; i++) p_arr[i] = p[i];

    var divResult[2][200] = long_div2(32, 8, proper_regs - 8, proper, p_arr);

    signal q;
    var q_val = 0;
    for (var i = 0; i < proper_regs - 8; i++) {
        q_val += divResult[0][i] * (1 << (32 * i));
    }
    q <-- q_val;

    // Range check q
    signal _q_bits[q_bits] <== Num2Bits(q_bits)(q);

    // ── Step 4: Native field check (linear — 0 non-linear constraints) ──
    var p_native = 0;
    var expr_native = 0;
    for (var i = 0; i < 8; i++) {
        var base_i = 1 << (32 * i);
        expr_native += positive[i] * base_i;
        p_native += p[i] * base_i;
    }
    expr_native === q * p_native;

    // ── Step 5: CRT checks with 2 × 76-bit primes ──
    signal kj[2];
    component kj_rc[2];

    for (var j = 0; j < 2; j++) {
        var mj = crt_prime_76bit(j);

        var expr_j = 0;
        var p_j = 0;
        for (var i = 0; i < 8; i++) {
            var coeff = pow_mod(1 << 32, i, mj);
            expr_j += positive[i] * coeff;
            p_j += p[i] * coeff;
        }

        // BIAS ensures non-negative before integer division.
        // |expr_j - q * p_j| < 2^(m+71) * mj. BIAS = 1 << (m + 71).
        var BIAS = 1 << (m + 71);

        kj[j] <-- (expr_j - q * p_j + BIAS * mj) \ mj;
        expr_j + BIAS * mj === q * p_j + kj[j] * mj;

        // kj ∈ [0, 2*BIAS + 2^(m+71)] < 2^(m+73)
        var kj_bits = m + 73;
        kj_rc[j] = Num2Bits(kj_bits);
        kj_rc[j].in <== kj[j];
    }
}

// ═══════════════════════════════════════════════════
// Range check: value < secp256k1 prime
// ═══════════════════════════════════════════════════

/// Verifies 8 × 32-bit limbs represent a value in [0, p).
/// Range-checks each limb, then handles the boundary case where
/// all upper limbs equal 0xFFFFFFFF.
template CheckInRangeSecp256k1() {
    signal input in[8];

    // Range check each limb to 32 bits
    component rc[8];
    for (var i = 0; i < 8; i++) {
        rc[i] = Num2Bits(32);
        rc[i].in <== in[i];
    }

    // Check if top 7 limbs all equal 0xFFFFFFFF
    component isMax[7];
    signal allMax[8];
    allMax[0] <== 1;
    for (var i = 1; i < 8; i++) {
        isMax[i - 1] = IsEqual();
        isMax[i - 1].in[0] <== in[i];
        isMax[i - 1].in[1] <== (1 << 32) - 1;
        allMax[i] <== allMax[i - 1] * isMax[i - 1].out;
    }

    // p[0] = 0xFFFFFC2F = 4294966319
    // If all upper limbs are max, bottom limb must be < p[0]
    component lt = LessThan(32);
    lt.in[0] <== in[0];
    lt.in[1] <== 4294966319;
    (1 - lt.out) * allMax[7] === 0;
}
