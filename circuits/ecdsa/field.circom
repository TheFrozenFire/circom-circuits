pragma circom 2.2.2;

include "arithmetic/bigint.circom";
include "arithmetic/bigint_func.circom";
include "core/comparators.circom";
include "packing/bitify.circom";

// ═══════════════════════════════════════════════════
// Prime reduction templates (all linear — zero constraints)
// Exploit p = 2^256 - 2^32 - 977, so 2^256 ≡ (2^32 + 977) mod p.
// ═══════════════════════════════════════════════════

/// Reduces 15-register quadratic product (8×8→15) to 8 registers.
/// Adds 33 bits to overflow per register.
template Secp256k1PrimeReduce15To8() {
    signal input in[15];
    signal output out[8];

    // 2^256 ≡ offset (mod p), where offset = 2^32 + 977 = 4294968273 (33 bits)
    var offset = (1 << 32) + 977;

    // Fold registers 8..14 back into 0..6 using: in[j+8] * 2^(256+32j) ≡ in[j+8] * offset * 2^(32j)
    out[0] <== in[0] + offset * in[8];
    out[1] <== in[1] + offset * in[9];
    out[2] <== in[2] + offset * in[10];
    out[3] <== in[3] + offset * in[11];
    out[4] <== in[4] + offset * in[12];
    out[5] <== in[5] + offset * in[13];
    out[6] <== in[6] + offset * in[14];
    out[7] <== in[7];
}

/// Reduces 22-register cubic product (8×8×8→22) to 8 registers.
/// Adds 65 bits to overflow per register.
template Secp256k1PrimeReduce22To8() {
    signal input in[22];
    signal output out[8];

    var offset = (1 << 32) + 977;
    // offset² is exact in BN254 field: (2^32+977)^2 = 2^64 + 2*977*2^32 + 977^2
    // = 18446744082299486209 (65 bits)
    var offset2 = offset * offset;

    // Two-pass fold: registers 16..21 use offset², registers 8..15 use offset
    out[0] <== in[0] + offset * in[8] + offset2 * in[16];
    out[1] <== in[1] + offset * in[9] + offset2 * in[17];
    out[2] <== in[2] + offset * in[10] + offset2 * in[18];
    out[3] <== in[3] + offset * in[11] + offset2 * in[19];
    out[4] <== in[4] + offset * in[12] + offset2 * in[20];
    out[5] <== in[5] + offset * in[13] + offset2 * in[21];
    out[6] <== in[6] + offset * in[14];
    out[7] <== in[7] + offset * in[15];
}

// ═══════════════════════════════════════════════════
// Modular zero checks
// ═══════════════════════════════════════════════════

/// Verifies a 15-register expression ≡ 0 mod p (for quadratic products).
/// Registers have m-bit overflow. Uses polynomial multiply for q*p constraint.
///
/// Overflow analysis for n=32, k=8:
///   After reduce 15→8: each register has m+33 bits.
///   Total value bound: |val| < 2^(m+33) * sum(2^(32i), i=0..7) < 2^(m+258).
///   Quotient bound: |q| < 2^(m+258) / p < 2^(m+3).
///   Bias 2^(m+4) ensures positivity: q + 2^(m+4) > 0.
///   positive[i] has max(m+33, 32+(m+4))+1 = m+37 bits.
template CheckQuadraticModPIsZero(m) {
    assert(m < 245);

    signal input in[15];

    signal p[8];
    p[0] <== 4294966319;
    p[1] <== 4294967294;
    p[2] <== 4294967295;
    p[3] <== 4294967295;
    p[4] <== 4294967295;
    p[5] <== 4294967295;
    p[6] <== 4294967295;
    p[7] <== 4294967295;

    // Reduce 15 → 8 registers (adds 33 bits)
    signal reduced[8];
    reduced <== Secp256k1PrimeReduce15To8()(in);

    // Add multiple of p to ensure positivity.
    // With 32-bit limbs, bias exponent must be (m+4) to exceed |q| < 2^(m+3).
    // (Reference uses (m-20) which works for 64-bit limbs but not 32-bit.)
    signal positive[8];
    for (var i = 0; i < 8; i++) {
        positive[i] <== reduced[i] + p[i] * (1 << (m + 4));
    }

    // Witness quotient (3 registers of 32 bits)
    var temp[200] = getProperRepresentation(m + 37, 32, 8, positive);
    var proper[16];
    for (var i = 0; i < 16; i++) proper[i] = temp[i];

    var qVarTemp[2][200] = long_div2(32, 8, 8, proper, p);

    signal q[3];
    for (var i = 0; i < 3; i++) {
        q[i] <-- qVarTemp[0][i];
    }

    // Range check quotient
    component qRC[3];
    for (var i = 0; i < 3; i++) {
        qRC[i] = Num2Bits(32);
        qRC[i].in <== q[i];
    }

    // Constrain q * p == positive via polynomial multiplication
    signal qpProd[10];
    component qpComp = BigMultNoCarryPoly(32, 32, 32, 3, 8);
    for (var i = 0; i < 3; i++) qpComp.a[i] <== q[i];
    for (var i = 0; i < 8; i++) qpComp.b[i] <== p[i];
    for (var i = 0; i < 10; i++) qpProd[i] <== qpComp.out[i];

    // Check qpProd - positive == 0 via carry-to-zero
    // diff has max(67, m+37)+1 = m+38 bits
    signal diff[10];
    for (var i = 0; i < 10; i++) {
        if (i < 8) {
            diff[i] <== qpProd[i] - positive[i];
        } else {
            diff[i] <== qpProd[i];
        }
    }
    CheckCarryToZero(32, m + 38, 10)(diff);
}

/// Verifies a 22-register expression ≡ 0 mod p (for cubic products).
/// Registers have m-bit overflow.
///
/// Overflow analysis for n=32, k=8:
///   After reduce 22→8: each register has m+65 bits.
///   Total value bound: |val| < 2^(m+65) * sum(2^(32i), i=0..7) < 2^(m+290).
///   Quotient bound: |q| < 2^(m+290) / p < 2^(m+35).
///   Bias 2^(m+36) ensures positivity: q + 2^(m+36) > 0.
///   positive[i] has max(m+65, 32+(m+36))+1 = m+69 bits.
template CheckCubicModPIsZero(m) {
    assert(m < 213);

    signal input in[22];

    signal p[8];
    p[0] <== 4294966319;
    p[1] <== 4294967294;
    p[2] <== 4294967295;
    p[3] <== 4294967295;
    p[4] <== 4294967295;
    p[5] <== 4294967295;
    p[6] <== 4294967295;
    p[7] <== 4294967295;

    // Reduce 22 → 8 registers (adds 65 bits)
    signal reduced[8];
    reduced <== Secp256k1PrimeReduce22To8()(in);

    // Add multiple of p to ensure positivity.
    // With 32-bit limbs, bias exponent must be (m+36) to exceed |q| < 2^(m+35).
    // (Reference uses (m-20) which works for 64-bit limbs but not 32-bit.)
    signal positive[8];
    for (var i = 0; i < 8; i++) {
        positive[i] <== reduced[i] + p[i] * (1 << (m + 36));
    }

    // Witness quotient (up to 5 registers of 32 bits)
    var temp[200] = getProperRepresentation(m + 69, 32, 8, positive);
    var proper[16];
    for (var i = 0; i < 16; i++) proper[i] = temp[i];

    var qVarTemp[2][200] = long_div2(32, 8, 8, proper, p);

    signal q[5];
    for (var i = 0; i < 5; i++) {
        q[i] <-- qVarTemp[0][i];
    }

    // Range check quotient
    component qRC[5];
    for (var i = 0; i < 5; i++) {
        qRC[i] = Num2Bits(32);
        qRC[i].in <== q[i];
    }

    // Constrain q * p == positive via polynomial multiplication
    signal qpProd[12];
    component qpComp = BigMultNoCarryPoly(32, 32, 32, 5, 8);
    for (var i = 0; i < 5; i++) qpComp.a[i] <== q[i];
    for (var i = 0; i < 8; i++) qpComp.b[i] <== p[i];
    for (var i = 0; i < 12; i++) qpProd[i] <== qpComp.out[i];

    // Check qpProd - positive == 0
    // diff has max(67, m+69)+1 = m+70 bits
    signal diff[12];
    for (var i = 0; i < 12; i++) {
        if (i < 8) {
            diff[i] <== qpProd[i] - positive[i];
        } else {
            diff[i] <== qpProd[i];
        }
    }
    CheckCarryToZero(32, m + 70, 12)(diff);
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
