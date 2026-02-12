pragma circom 2.2.2;

include "curve/babyjub.circom";
include "curve/montgomery.circom";
include "comparators.circom";
include "mux.circom";

// ─── Fixed-base scalar multiplication ───

/// Lookup window: computes base*{1..8} in Montgomery, selects one via 3-bit input.
template WindowMulFix() {
    signal input in[3];
    signal input base[2];
    signal output out[2];
    signal output out8[2];

    component mux = MultiMux3(2);

    mux.s[0] <== in[0];
    mux.s[1] <== in[1];
    mux.s[2] <== in[2];

    component dbl2 = MontgomeryDouble();
    component adr3 = MontgomeryAdd();
    component adr4 = MontgomeryAdd();
    component adr5 = MontgomeryAdd();
    component adr6 = MontgomeryAdd();
    component adr7 = MontgomeryAdd();
    component adr8 = MontgomeryAdd();

    // 1*BASE
    mux.c[0][0] <== base[0];
    mux.c[1][0] <== base[1];

    // 2*BASE
    dbl2.in[0] <== base[0];
    dbl2.in[1] <== base[1];
    mux.c[0][1] <== dbl2.out[0];
    mux.c[1][1] <== dbl2.out[1];

    // 3*BASE
    adr3.in1[0] <== base[0];
    adr3.in1[1] <== base[1];
    adr3.in2[0] <== dbl2.out[0];
    adr3.in2[1] <== dbl2.out[1];
    mux.c[0][2] <== adr3.out[0];
    mux.c[1][2] <== adr3.out[1];

    // 4*BASE
    adr4.in1[0] <== base[0];
    adr4.in1[1] <== base[1];
    adr4.in2[0] <== adr3.out[0];
    adr4.in2[1] <== adr3.out[1];
    mux.c[0][3] <== adr4.out[0];
    mux.c[1][3] <== adr4.out[1];

    // 5*BASE
    adr5.in1[0] <== base[0];
    adr5.in1[1] <== base[1];
    adr5.in2[0] <== adr4.out[0];
    adr5.in2[1] <== adr4.out[1];
    mux.c[0][4] <== adr5.out[0];
    mux.c[1][4] <== adr5.out[1];

    // 6*BASE
    adr6.in1[0] <== base[0];
    adr6.in1[1] <== base[1];
    adr6.in2[0] <== adr5.out[0];
    adr6.in2[1] <== adr5.out[1];
    mux.c[0][5] <== adr6.out[0];
    mux.c[1][5] <== adr6.out[1];

    // 7*BASE
    adr7.in1[0] <== base[0];
    adr7.in1[1] <== base[1];
    adr7.in2[0] <== adr6.out[0];
    adr7.in2[1] <== adr6.out[1];
    mux.c[0][6] <== adr7.out[0];
    mux.c[1][6] <== adr7.out[1];

    // 8*BASE
    adr8.in1[0] <== base[0];
    adr8.in1[1] <== base[1];
    adr8.in2[0] <== adr7.out[0];
    adr8.in2[1] <== adr7.out[1];
    mux.c[0][7] <== adr8.out[0];
    mux.c[1][7] <== adr8.out[1];

    out8[0] <== adr8.out[0];
    out8[1] <== adr8.out[1];

    out[0] <== mux.out[0];
    out[1] <== mux.out[1];
}

/// Fixed-base segment: processes nWindows*3 scalar bits against a base point.
template SegmentMulFix(nWindows) {
    signal input e[nWindows * 3];
    signal input base[2];
    signal output out[2];
    signal output dbl[2];

    component e2m = Edwards2Montgomery();
    e2m.in[0] <== base[0];
    e2m.in[1] <== base[1];

    component windows[nWindows];
    component adders[nWindows];
    component cadders[nWindows];
    component dblLast = MontgomeryDouble();

    for (var i = 0; i < nWindows; i++) {
        windows[i] = WindowMulFix();
        cadders[i] = MontgomeryAdd();
        if (i == 0) {
            windows[i].base[0] <== e2m.out[0];
            windows[i].base[1] <== e2m.out[1];
            cadders[i].in1[0] <== e2m.out[0];
            cadders[i].in1[1] <== e2m.out[1];
        } else {
            windows[i].base[0] <== windows[i - 1].out8[0];
            windows[i].base[1] <== windows[i - 1].out8[1];
            cadders[i].in1[0] <== cadders[i - 1].out[0];
            cadders[i].in1[1] <== cadders[i - 1].out[1];
        }
        for (var j = 0; j < 3; j++) {
            windows[i].in[j] <== e[3 * i + j];
        }
        if (i < nWindows - 1) {
            cadders[i].in2[0] <== windows[i].out8[0];
            cadders[i].in2[1] <== windows[i].out8[1];
        } else {
            dblLast.in[0] <== windows[i].out8[0];
            dblLast.in[1] <== windows[i].out8[1];
            cadders[i].in2[0] <== dblLast.out[0];
            cadders[i].in2[1] <== dblLast.out[1];
        }
    }

    for (var i = 0; i < nWindows; i++) {
        adders[i] = MontgomeryAdd();
        if (i == 0) {
            adders[i].in1[0] <== dblLast.out[0];
            adders[i].in1[1] <== dblLast.out[1];
        } else {
            adders[i].in1[0] <== adders[i - 1].out[0];
            adders[i].in1[1] <== adders[i - 1].out[1];
        }
        adders[i].in2[0] <== windows[i].out[0];
        adders[i].in2[1] <== windows[i].out[1];
    }

    component m2e = Montgomery2Edwards();
    component cm2e = Montgomery2Edwards();

    m2e.in[0] <== adders[nWindows - 1].out[0];
    m2e.in[1] <== adders[nWindows - 1].out[1];
    cm2e.in[0] <== cadders[nWindows - 1].out[0];
    cm2e.in[1] <== cadders[nWindows - 1].out[1];

    component cAdd = BabyAdd();
    cAdd.x1 <== m2e.out[0];
    cAdd.y1 <== m2e.out[1];
    cAdd.x2 <== -cm2e.out[0];
    cAdd.y2 <== cm2e.out[1];

    cAdd.xout ==> out[0];
    cAdd.yout ==> out[1];

    windows[nWindows - 1].out8[0] ==> dbl[0];
    windows[nWindows - 1].out8[1] ==> dbl[1];
}

/// Fixed-base scalar multiplication: e (n bits) * BASE → out (twisted Edwards).
template EscalarMulFix(n, BASE) {
    signal input e[n];
    signal output out[2];

    var nsegments = (n - 1) \ 246 + 1;
    var nlastsegment = n - (nsegments - 1) * 249;

    component segments[nsegments];
    component m2e[nsegments - 1];
    component adders[nsegments - 1];

    for (var s = 0; s < nsegments; s++) {
        var nseg = (s < nsegments - 1) ? 249 : nlastsegment;
        var nWindows = ((nseg - 1) \ 3) + 1;

        segments[s] = SegmentMulFix(nWindows);

        for (var i = 0; i < nseg; i++) {
            segments[s].e[i] <== e[s * 249 + i];
        }
        for (var i = nseg; i < nWindows * 3; i++) {
            segments[s].e[i] <== 0;
        }

        if (s == 0) {
            segments[s].base[0] <== BASE[0];
            segments[s].base[1] <== BASE[1];
        } else {
            m2e[s - 1] = Montgomery2Edwards();
            adders[s - 1] = BabyAdd();

            segments[s - 1].dbl[0] ==> m2e[s - 1].in[0];
            segments[s - 1].dbl[1] ==> m2e[s - 1].in[1];

            m2e[s - 1].out[0] ==> segments[s].base[0];
            m2e[s - 1].out[1] ==> segments[s].base[1];

            if (s == 1) {
                segments[s - 1].out[0] ==> adders[s - 1].x1;
                segments[s - 1].out[1] ==> adders[s - 1].y1;
            } else {
                adders[s - 2].xout ==> adders[s - 1].x1;
                adders[s - 2].yout ==> adders[s - 1].y1;
            }
            segments[s].out[0] ==> adders[s - 1].x2;
            segments[s].out[1] ==> adders[s - 1].y2;
        }
    }

    if (nsegments == 1) {
        segments[0].out[0] ==> out[0];
        segments[0].out[1] ==> out[1];
    } else {
        adders[nsegments - 2].xout ==> out[0];
        adders[nsegments - 2].yout ==> out[1];
    }
}

// ─── Variable-base scalar multiplication ───

/// 2-to-1 point multiplexer: selects in[0] or in[1] based on sel.
template Multiplexor2() {
    signal input sel;
    signal input in[2][2];
    signal output out[2];

    out[0] <== (in[1][0] - in[0][0]) * sel + in[0][0];
    out[1] <== (in[1][1] - in[0][1]) * sel + in[0][1];
}

/// Single-bit step of variable-base multiplication.
/// Doubles dblIn, conditionally adds to addIn based on sel.
template BitElementMulAny() {
    signal input sel;
    signal input dblIn[2];
    signal input addIn[2];
    signal output dblOut[2];
    signal output addOut[2];

    component doubler = MontgomeryDouble();
    component adder = MontgomeryAdd();
    component selector = Multiplexor2();

    sel ==> selector.sel;

    dblIn[0] ==> doubler.in[0];
    dblIn[1] ==> doubler.in[1];
    doubler.out[0] ==> adder.in1[0];
    doubler.out[1] ==> adder.in1[1];
    addIn[0] ==> adder.in2[0];
    addIn[1] ==> adder.in2[1];
    addIn[0] ==> selector.in[0][0];
    addIn[1] ==> selector.in[0][1];
    adder.out[0] ==> selector.in[1][0];
    adder.out[1] ==> selector.in[1][1];

    doubler.out[0] ==> dblOut[0];
    doubler.out[1] ==> dblOut[1];
    selector.out[0] ==> addOut[0];
    selector.out[1] ==> addOut[1];
}

/// Variable-base segment: processes n scalar bits against point p.
/// p is twisted Edwards; internal computation in Montgomery.
template SegmentMulAny(n) {
    signal input e[n];
    signal input p[2];
    signal output out[2];
    signal output dbl[2];

    component bits[n - 1];
    component e2m = Edwards2Montgomery();

    p[0] ==> e2m.in[0];
    p[1] ==> e2m.in[1];

    bits[0] = BitElementMulAny();
    e2m.out[0] ==> bits[0].dblIn[0];
    e2m.out[1] ==> bits[0].dblIn[1];
    e2m.out[0] ==> bits[0].addIn[0];
    e2m.out[1] ==> bits[0].addIn[1];
    e[1] ==> bits[0].sel;

    for (var i = 1; i < n - 1; i++) {
        bits[i] = BitElementMulAny();

        bits[i - 1].dblOut[0] ==> bits[i].dblIn[0];
        bits[i - 1].dblOut[1] ==> bits[i].dblIn[1];
        bits[i - 1].addOut[0] ==> bits[i].addIn[0];
        bits[i - 1].addOut[1] ==> bits[i].addIn[1];
        e[i + 1] ==> bits[i].sel;
    }

    bits[n - 2].dblOut[0] ==> dbl[0];
    bits[n - 2].dblOut[1] ==> dbl[1];

    component m2e = Montgomery2Edwards();

    bits[n - 2].addOut[0] ==> m2e.in[0];
    bits[n - 2].addOut[1] ==> m2e.in[1];

    component eadder = BabyAdd();

    m2e.out[0] ==> eadder.x1;
    m2e.out[1] ==> eadder.y1;
    -p[0] ==> eadder.x2;
    p[1] ==> eadder.y2;

    component lastSel = Multiplexor2();

    e[0] ==> lastSel.sel;
    eadder.xout ==> lastSel.in[0][0];
    eadder.yout ==> lastSel.in[0][1];
    m2e.out[0] ==> lastSel.in[1][0];
    m2e.out[1] ==> lastSel.in[1][1];

    lastSel.out[0] ==> out[0];
    lastSel.out[1] ==> out[1];
}

/// Variable-base scalar multiplication: e (n bits) * p → out (twisted Edwards).
/// Assumes p is in the subgroup and differs from identity.
template EscalarMulAny(n) {
    signal input e[n];
    signal input p[2];
    signal output out[2];

    var nsegments = (n - 1) \ 148 + 1;
    var nlastsegment = n - (nsegments - 1) * 148;

    component segments[nsegments];
    component doublers[nsegments - 1];
    component m2e[nsegments - 1];
    component adders[nsegments - 1];
    component zeropoint = IsZero();
    zeropoint.in <== p[0];

    for (var s = 0; s < nsegments; s++) {
        var nseg = (s < nsegments - 1) ? 148 : nlastsegment;

        segments[s] = SegmentMulAny(nseg);

        for (var i = 0; i < nseg; i++) {
            e[s * 148 + i] ==> segments[s].e[i];
        }

        if (s == 0) {
            // Substitute G8 if input point is zero
            segments[s].p[0] <== p[0] + (5299619240641551281634865583518297030282874472190772894086521144482721001553 - p[0]) * zeropoint.out;
            segments[s].p[1] <== p[1] + (16950150798460657717958625567821834550301663161624707787222815936182638968203 - p[1]) * zeropoint.out;
        } else {
            doublers[s - 1] = MontgomeryDouble();
            m2e[s - 1] = Montgomery2Edwards();
            adders[s - 1] = BabyAdd();

            segments[s - 1].dbl[0] ==> doublers[s - 1].in[0];
            segments[s - 1].dbl[1] ==> doublers[s - 1].in[1];

            doublers[s - 1].out[0] ==> m2e[s - 1].in[0];
            doublers[s - 1].out[1] ==> m2e[s - 1].in[1];

            m2e[s - 1].out[0] ==> segments[s].p[0];
            m2e[s - 1].out[1] ==> segments[s].p[1];

            if (s == 1) {
                segments[s - 1].out[0] ==> adders[s - 1].x1;
                segments[s - 1].out[1] ==> adders[s - 1].y1;
            } else {
                adders[s - 2].xout ==> adders[s - 1].x1;
                adders[s - 2].yout ==> adders[s - 1].y1;
            }
            segments[s].out[0] ==> adders[s - 1].x2;
            segments[s].out[1] ==> adders[s - 1].y2;
        }
    }

    if (nsegments == 1) {
        segments[0].out[0] * (1 - zeropoint.out) ==> out[0];
        segments[0].out[1] + (1 - segments[0].out[1]) * zeropoint.out ==> out[1];
    } else {
        adders[nsegments - 2].xout * (1 - zeropoint.out) ==> out[0];
        adders[nsegments - 2].yout + (1 - adders[nsegments - 2].yout) * zeropoint.out ==> out[1];
    }
}
