pragma circom 2.2.2;

include "arithmetic/bigint.circom";
include "arithmetic/bigint_func.circom";
include "ecdsa/constants.circom";
include "ecdsa/functions.circom";
include "ecdsa/field.circom";

// ═══════════════════════════════════════════════════
// Polynomial constraint templates for secp256k1 point operations.
// These algebraically eliminate lambda (the slope), checking degree-3
// polynomial identities mod p instead. This avoids expensive in-circuit
// modular inverse, replacing it with cheap polynomial identity checks.
// ═══════════════════════════════════════════════════

/// Constrains: x1³+x2³-x1²x2-x1x2²+x2²x3+x1²x3-2x1x2x3-y1²+2y1y2-y2² ≡ 0 mod p.
/// This is the algebraic elimination of lambda from the point addition formula.
template Secp256k1AddUnequalCubicConstraint() {
    signal input x1[8];
    signal input y1[8];
    signal input x2[8];
    signal input y2[8];
    signal input x3[8];
    signal input y3[8];

    // Cubic products (22 registers each): x1³, x2³, x1²x2, x1x2², x2²x3, x1²x3, x1x2x3
    // Two-stage: first compute a*b (15 regs), then (a*b)*c (22 regs)

    // x1³ = x1 * x1 * x1
    signal x1sq[15];
    x1sq <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(x1, x1);
    signal x13[22];
    x13 <== BigMultNoCarryPoly(32, 67, 32, 15, 8)(x1sq, x1);

    // x2³ = x2 * x2 * x2
    signal x2sq[15];
    x2sq <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(x2, x2);
    signal x23[22];
    x23 <== BigMultNoCarryPoly(32, 67, 32, 15, 8)(x2sq, x2);

    // x1²x2
    signal x12x2[22];
    x12x2 <== BigMultNoCarryPoly(32, 67, 32, 15, 8)(x1sq, x2);

    // x1x2²
    signal x1x22[22];
    x1x22 <== BigMultNoCarryPoly(32, 67, 32, 15, 8)(x2sq, x1);

    // x2²x3
    signal x22x3[22];
    x22x3 <== BigMultNoCarryPoly(32, 67, 32, 15, 8)(x2sq, x3);

    // x1²x3
    signal x12x3[22];
    x12x3 <== BigMultNoCarryPoly(32, 67, 32, 15, 8)(x1sq, x3);

    // x1x2x3 = (x1*x2)*x3
    signal x1x2[15];
    x1x2 <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(x1, x2);
    signal x1x2x3[22];
    x1x2x3 <== BigMultNoCarryPoly(32, 67, 32, 15, 8)(x1x2, x3);

    // Quadratic products (15 registers each): y1², y2², y1y2
    signal y1sq[15];
    y1sq <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(y1, y1);

    signal y2sq[15];
    y2sq <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(y2, y2);

    signal y1y2[15];
    y1y2 <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(y1, y2);

    // Combine: x1³+x2³-x1²x2-x1x2²+x2²x3+x1²x3-2x1x2x3 -y1²+2y1y2-y2²
    signal combined[22];
    for (var i = 0; i < 22; i++) {
        if (i < 15) {
            combined[i] <== x13[i] + x23[i] - x12x2[i] - x1x22[i]
                + x22x3[i] + x12x3[i] - 2 * x1x2x3[i]
                - y1sq[i] + 2 * y1y2[i] - y2sq[i];
        } else {
            combined[i] <== x13[i] + x23[i] - x12x2[i] - x1x22[i]
                + x22x3[i] + x12x3[i] - 2 * x1x2x3[i];
        }
    }
    CheckCubicModPIsZero(105)(combined);
}

/// Constrains: x3y2+x2y3+x2y1-x3y1-x1y2-x1y3 ≡ 0 mod p.
/// Shows (x1,y1), (x2,y2), (x3,-y3) are collinear.
template Secp256k1PointOnLine() {
    signal input x1[8];
    signal input y1[8];
    signal input x2[8];
    signal input y2[8];
    signal input x3[8];
    signal input y3[8];

    signal x3y2[15];
    x3y2 <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(x3, y2);

    signal x2y3[15];
    x2y3 <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(x2, y3);

    signal x2y1[15];
    x2y1 <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(x2, y1);

    signal x3y1[15];
    x3y1 <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(x3, y1);

    signal x1y2[15];
    x1y2 <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(x1, y2);

    signal x1y3[15];
    x1y3 <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(x1, y3);

    signal combined[15];
    for (var i = 0; i < 15; i++) {
        combined[i] <== x3y2[i] + x2y3[i] + x2y1[i] - x3y1[i] - x1y2[i] - x1y3[i];
    }
    CheckQuadraticModPIsZero(70)(combined);
}

/// Constrains: 2y1²+2y1y3-3x1³+3x1²x3 ≡ 0 mod p.
/// Shows the output lies on the tangent line at (x1,y1).
template Secp256k1PointOnTangent() {
    signal input x1[8];
    signal input y1[8];
    signal input x3[8];
    signal input y3[8];

    signal y1sq[15];
    y1sq <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(y1, y1);

    signal y1y3[15];
    y1y3 <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(y1, y3);

    signal x1sq[15];
    x1sq <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(x1, x1);
    signal x13[22];
    x13 <== BigMultNoCarryPoly(32, 67, 32, 15, 8)(x1sq, x1);

    signal x12x3[22];
    x12x3 <== BigMultNoCarryPoly(32, 67, 32, 15, 8)(x1sq, x3);

    signal combined[22];
    for (var i = 0; i < 22; i++) {
        if (i < 15) {
            combined[i] <== 2 * y1sq[i] + 2 * y1y3[i] - 3 * x13[i] + 3 * x12x3[i];
        } else {
            combined[i] <== -3 * x13[i] + 3 * x12x3[i];
        }
    }
    CheckCubicModPIsZero(104)(combined);
}

/// Constrains: x³ + 7 - y² ≡ 0 mod p.
/// Verifies a point lies on the secp256k1 curve.
template Secp256k1PointOnCurve() {
    signal input x[8];
    signal input y[8];

    signal xsq[15];
    xsq <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(x, x);
    signal x3[22];
    x3 <== BigMultNoCarryPoly(32, 67, 32, 15, 8)(xsq, x);

    signal y2[15];
    y2 <== BigMultNoCarryPoly(32, 32, 32, 8, 8)(y, y);

    signal combined[22];
    for (var i = 0; i < 22; i++) {
        if (i == 0) {
            combined[i] <== x3[i] - y2[i] + 7;
        } else if (i < 15) {
            combined[i] <== x3[i] - y2[i];
        } else {
            combined[i] <== x3[i];
        }
    }
    CheckCubicModPIsZero(103)(combined);
}

// ═══════════════════════════════════════════════════
// Top-level point operation templates
// ═══════════════════════════════════════════════════

/// Point addition for two distinct secp256k1 points.
/// Witness via explicit formula, constrain via cubic identity + collinearity.
template Secp256k1AddUnequal(n, k) {
    assert(n == 32 && k == 8);

    signal input a[2][k];
    signal input b[2][k];
    signal output out[2][k];

    var x1[8];
    var y1[8];
    var x2[8];
    var y2[8];
    for (var i = 0; i < k; i++) {
        x1[i] = a[0][i];
        y1[i] = a[1][i];
        x2[i] = b[0][i];
        y2[i] = b[1][i];
    }

    var tmp[2][200] = secp256k1_addunequal_func(n, k, x1, y1, x2, y2);
    for (var i = 0; i < k; i++) {
        out[0][i] <-- tmp[0][i];
        out[1][i] <-- tmp[1][i];
    }

    // Constraints: cubic identity + collinearity + range checks
    component cubic = Secp256k1AddUnequalCubicConstraint();
    for (var i = 0; i < k; i++) {
        cubic.x1[i] <== a[0][i];
        cubic.y1[i] <== a[1][i];
        cubic.x2[i] <== b[0][i];
        cubic.y2[i] <== b[1][i];
        cubic.x3[i] <== out[0][i];
        cubic.y3[i] <== out[1][i];
    }

    component onLine = Secp256k1PointOnLine();
    for (var i = 0; i < k; i++) {
        onLine.x1[i] <== a[0][i];
        onLine.y1[i] <== a[1][i];
        onLine.x2[i] <== b[0][i];
        onLine.y2[i] <== b[1][i];
        onLine.x3[i] <== out[0][i];
        onLine.y3[i] <== out[1][i];
    }

    component xRange = CheckInRangeSecp256k1();
    component yRange = CheckInRangeSecp256k1();
    for (var i = 0; i < k; i++) {
        xRange.in[i] <== out[0][i];
        yRange.in[i] <== out[1][i];
    }
}

/// Point doubling on secp256k1.
/// Witness via explicit formula, constrain via tangent + on-curve + range.
template Secp256k1Double(n, k) {
    assert(n == 32 && k == 8);

    signal input in[2][k];
    signal output out[2][k];

    var x1[8];
    var y1[8];
    for (var i = 0; i < k; i++) {
        x1[i] = in[0][i];
        y1[i] = in[1][i];
    }

    var tmp[2][200] = secp256k1_double_func(n, k, x1, y1);
    for (var i = 0; i < k; i++) {
        out[0][i] <-- tmp[0][i];
        out[1][i] <-- tmp[1][i];
    }

    component tangent = Secp256k1PointOnTangent();
    for (var i = 0; i < k; i++) {
        tangent.x1[i] <== in[0][i];
        tangent.y1[i] <== in[1][i];
        tangent.x3[i] <== out[0][i];
        tangent.y3[i] <== out[1][i];
    }

    component onCurve = Secp256k1PointOnCurve();
    for (var i = 0; i < k; i++) {
        onCurve.x[i] <== out[0][i];
        onCurve.y[i] <== out[1][i];
    }

    component xRange = CheckInRangeSecp256k1();
    component yRange = CheckInRangeSecp256k1();
    for (var i = 0; i < k; i++) {
        xRange.in[i] <== out[0][i];
        yRange.in[i] <== out[1][i];
    }

    // Ensure x3 ≠ x1 (doubling must produce a distinct x-coordinate)
    signal x3_eq_x1 <== BigIsEqual(k)(out[0], in[0]);
    x3_eq_x1 === 0;
}
