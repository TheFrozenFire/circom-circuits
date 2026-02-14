pragma circom 2.2.2;

include "core/comparators.circom";

/// Verifies that all non-zero elements of right[] exist in left[].
/// Zero values in right are treated as empty slots and skipped.
/// Constraint-only — no outputs.
template Contains(nLeft, nRight) {
    signal input left[nLeft];
    signal input right[nRight];

    component rightIsZero[nRight];
    component eq[nRight][nLeft];
    component noMatch[nRight];
    component enforce[nRight];

    for (var i = 0; i < nRight; i++) {
        rightIsZero[i] = IsZero();
        rightIsZero[i].in <== right[i];

        var sum = 0;
        for (var j = 0; j < nLeft; j++) {
            eq[i][j] = IsEqual();
            eq[i][j].in[0] <== right[i];
            eq[i][j].in[1] <== left[j];
            sum += eq[i][j].out;
        }

        noMatch[i] = IsZero();
        noMatch[i].in <== sum;

        enforce[i] = ForceEqualIfEnabled();
        enforce[i].enabled <== 1 - rightIsZero[i].out;
        enforce[i].in[0] <== noMatch[i].out;
        enforce[i].in[1] <== 0;
    }
}

/// Verifies that all non-null points in right[] exist in left[].
/// (0,0) is the null sentinel and is skipped. Match requires both coordinates equal.
/// Constraint-only — no outputs.
template Contains_Points(nLeft, nRight) {
    signal input left[nLeft][2];
    signal input right[nRight][2];

    component rightXZero[nRight];
    component rightYZero[nRight];
    signal isNull[nRight];
    component eqX[nRight][nLeft];
    component eqY[nRight][nLeft];
    signal match[nRight][nLeft];
    component noMatch[nRight];
    component enforce[nRight];

    for (var i = 0; i < nRight; i++) {
        rightXZero[i] = IsZero();
        rightXZero[i].in <== right[i][0];

        rightYZero[i] = IsZero();
        rightYZero[i].in <== right[i][1];

        isNull[i] <== rightXZero[i].out * rightYZero[i].out;

        var sum = 0;
        for (var j = 0; j < nLeft; j++) {
            eqX[i][j] = IsEqual();
            eqX[i][j].in[0] <== right[i][0];
            eqX[i][j].in[1] <== left[j][0];

            eqY[i][j] = IsEqual();
            eqY[i][j].in[0] <== right[i][1];
            eqY[i][j].in[1] <== left[j][1];

            match[i][j] <== eqX[i][j].out * eqY[i][j].out;
            sum += match[i][j];
        }

        noMatch[i] = IsZero();
        noMatch[i].in <== sum;

        enforce[i] = ForceEqualIfEnabled();
        enforce[i].enabled <== 1 - isNull[i];
        enforce[i].in[0] <== noMatch[i].out;
        enforce[i].in[1] <== 0;
    }
}
