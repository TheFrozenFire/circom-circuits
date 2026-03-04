pragma circom 2.2.2;

include "arithmetic/bigint.circom";
include "arithmetic/bigint_func.circom";
include "core/comparators.circom";
include "packing/bitify.circom";

// ═══════════════════════════════════════════════════
// Prime reduction templates (all linear — zero constraints)
// Exploit p = 2^256 - 2^32 - 977, so 2^256 ≡ (2^32 + 977) mod p.
// ═══════════════════════════════════════════════════

/// Reduces 7-register quadratic product (4×4→7) to 4 registers.
/// Adds 33 bits to overflow per register.
/// Input registers can be negative; overall input can be negative.
template Secp256k1PrimeReduce7Registers() {
    signal input in[7];
    signal output out[4];

    // 2^256 ≡ offset (mod p), where offset = 2^32 + 977 (33 bits)
    var offset = (1 << 32) + 977;

    // Fold registers 4..6 back into 0..2 using: in[j+4] * 2^(256+64j) ≡ in[j+4] * offset * 2^(64j)
    out[0] <== offset * in[4] + in[0];
    out[1] <== offset * in[5] + in[1];
    out[2] <== offset * in[6] + in[2];
    out[3] <== in[3];
}

/// Reduces 10-register cubic product (7×4→10) to 4 registers.
/// Adds 43 bits to overflow per register.
/// Input registers can be negative; overall input can be negative.
template Secp256k1PrimeReduce10Registers() {
    signal input in[10];
    signal output out[4];

    var offset = (1 << 32) + 977;  // 33 bits
    var offset2 = ((1 << 33) * 977) + (977 ** 2);  // 43 bits

    // Two-pass fold: registers 8..9 use offset², registers 4..7 use offset
    out[0] <== (offset2 * in[8]) + (offset * in[4]) + in[0];
    out[1] <== (offset2 * in[9]) + (offset * in[5]) + in[1] + in[8];
    out[2] <== (offset * in[6]) + in[2] + in[9];
    out[3] <== (offset * in[7]) + in[3];
}

// ═══════════════════════════════════════════════════
// Modular zero checks
// ═══════════════════════════════════════════════════

/// Verifies a 7-register expression ≡ 0 mod p (for quadratic products).
/// Registers have m-bit overflow. Uses polynomial multiply for q*p constraint.
template CheckQuadraticModPIsZero(m) {
    assert(m < 147);

    signal input in[7];

    signal p[4];
    p[0] <== 18446744069414583343;
    p[1] <== 18446744073709551615;
    p[2] <== 18446744073709551615;
    p[3] <== 18446744073709551615;

    // Reduce 7 → 4 registers (adds 33 bits → m+33 bits per register)
    signal reduced[4];
    reduced <== Secp256k1PrimeReduce7Registers()(in);

    // Add multiple of p to ensure positivity.
    // |val| < 2^(m+33+192) + eps, so p * 2^(m-30) ≈ 2^(m+226) > |val|
    signal positive[4];
    for (var i = 0; i < 4; i++) {
        positive[i] <== reduced[i] + p[i] * (1 << (m - 30)); // m+34 bits
    }

    // Witness quotient (2 registers of 64 bits)
    var temp[100] = getProperRepresentation(m + 35, 64, 4, positive);
    var proper[8];
    for (var i = 0; i < 8; i++) proper[i] = temp[i];

    var qVarTemp[2][200] = long_div2(64, 4, 4, proper, p);

    signal q[2];
    for (var i = 0; i < 2; i++) {
        q[i] <-- qVarTemp[0][i];
    }

    // Range check quotient
    component qRC[2];
    for (var i = 0; i < 2; i++) {
        qRC[i] = Num2Bits(64);
        qRC[i].in <== q[i];
    }

    // Constrain q * p == positive
    signal qpProd[5];
    component qpComp = BigMultNoCarry(64, 64, 64, 2, 4);
    for (var i = 0; i < 2; i++) qpComp.a[i] <== q[i];
    for (var i = 0; i < 4; i++) qpComp.b[i] <== p[i];
    for (var i = 0; i < 5; i++) qpProd[i] <== qpComp.out[i];

    // Check qpProd - positive == 0 via carry-to-zero
    component zeroCheck = CheckCarryToZero(64, m + 36, 5);
    for (var i = 0; i < 5; i++) {
        if (i < 4) {
            zeroCheck.in[i] <== qpProd[i] - positive[i];
        } else {
            zeroCheck.in[i] <== qpProd[i];
        }
    }
}

/// Verifies a 10-register expression ≡ 0 mod p (for cubic products).
/// Registers have m-bit overflow.
template CheckCubicModPIsZero(m) {
    assert(m < 206);

    signal input in[10];

    signal p[4];
    p[0] <== 18446744069414583343;
    p[1] <== 18446744073709551615;
    p[2] <== 18446744073709551615;
    p[3] <== 18446744073709551615;

    // Reduce 10 → 4 registers (adds 43 bits → m+43 bits per register)
    signal reduced[4];
    reduced <== Secp256k1PrimeReduce10Registers()(in);

    // Add multiple of p to ensure positivity.
    // |val| < 2^(m+43+192) + eps, so p * 2^(m-20) ≈ 2^(m+236) > |val|
    signal positive[4];
    for (var i = 0; i < 4; i++) {
        positive[i] <== reduced[i] + p[i] * (1 << (m - 20)); // m+44 bits
    }

    // Witness quotient (3 registers of 64 bits)
    var temp[100] = getProperRepresentation(m + 45, 64, 4, positive);
    var proper[8];
    for (var i = 0; i < 8; i++) proper[i] = temp[i];

    var qVarTemp[2][200] = long_div2(64, 4, 4, proper, p);

    signal q[3];
    for (var i = 0; i < 3; i++) {
        q[i] <-- qVarTemp[0][i];
    }

    // Range check quotient
    component qRC[3];
    for (var i = 0; i < 3; i++) {
        qRC[i] = Num2Bits(64);
        qRC[i].in <== q[i];
    }

    // Constrain q * p == positive
    signal qpProd[6];
    component qpComp = BigMultNoCarry(64, 64, 64, 3, 4);
    for (var i = 0; i < 3; i++) qpComp.a[i] <== q[i];
    for (var i = 0; i < 4; i++) qpComp.b[i] <== p[i];
    for (var i = 0; i < 6; i++) qpProd[i] <== qpComp.out[i];

    // Check qpProd - positive == 0
    component zeroCheck = CheckCarryToZero(64, m + 46, 6);
    for (var i = 0; i < 6; i++) {
        if (i < 4) {
            zeroCheck.in[i] <== qpProd[i] - positive[i];
        } else {
            zeroCheck.in[i] <== qpProd[i];
        }
    }
}

// ═══════════════════════════════════════════════════
// Range check: value < secp256k1 prime
// ═══════════════════════════════════════════════════

/// Verifies 4 × 64-bit limbs represent a value in [0, p).
/// Range-checks each limb, then handles the boundary case where
/// all upper limbs equal 0xFFFFFFFFFFFFFFFF.
template CheckInRangeSecp256k1() {
    signal input in[4];

    // Range check each limb to 64 bits
    component rc[4];
    for (var i = 0; i < 4; i++) {
        rc[i] = Num2Bits(64);
        rc[i].in <== in[i];
    }

    // Check if top 3 limbs all equal 0xFFFFFFFFFFFFFFFF
    component isMax[3];
    signal allMax[4];
    allMax[0] <== 1;
    for (var i = 1; i < 4; i++) {
        isMax[i - 1] = IsEqual();
        isMax[i - 1].in[0] <== in[i];
        isMax[i - 1].in[1] <== (1 << 64) - 1;
        allMax[i] <== allMax[i - 1] * isMax[i - 1].out;
    }

    // p[0] = 0xFFFFFFFEFFFFFC2F = 18446744069414583343
    // If all upper limbs are max, bottom limb must be < p[0]
    signal c;
    c <== (1 << 64) - ((1 << 32) + (1 << 9) + (1 << 8) + (1 << 7) + (1 << 6) + (1 << 4) + 1);
    component lt = LessThan(64);
    lt.in[0] <== in[0];
    lt.in[1] <== c;
    (1 - lt.out) * allMax[3] === 0;
}
