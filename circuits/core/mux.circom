pragma circom 2.2.2;

/// n-channel 2-to-1 multiplexer. Selects c[i][0] or c[i][1] per channel based on s.
/// out[i] = (c[i][1] - c[i][0]) * s + c[i][0]. n constraints.
template MultiMux1(n) {
    signal input c[n][2];
    signal input s;
    signal output out[n];

    for (var i = 0; i < n; i++) {
        out[i] <== (c[i][1] - c[i][0]) * s + c[i][0];
    }
}

/// n-channel 8-to-1 multiplexer. 3-bit selector s[3] picks from c[i][0..7].
template MultiMux3(n) {
    signal input c[n][8];
    signal input s[3];
    signal output out[n];

    signal a210[n];
    signal a21[n];
    signal a20[n];
    signal a2[n];

    signal a10[n];
    signal a1[n];
    signal a0[n];
    signal a[n];

    signal s10;
    s10 <== s[1] * s[0];

    for (var i = 0; i < n; i++) {
        a210[i] <== (c[i][7] - c[i][6] - c[i][5] + c[i][4] - c[i][3] + c[i][2] + c[i][1] - c[i][0]) * s10;
         a21[i] <== (c[i][6] - c[i][4] - c[i][2] + c[i][0]) * s[1];
         a20[i] <== (c[i][5] - c[i][4] - c[i][1] + c[i][0]) * s[0];
          a2[i] <== (c[i][4] - c[i][0]);

         a10[i] <== (c[i][3] - c[i][2] - c[i][1] + c[i][0]) * s10;
          a1[i] <== (c[i][2] - c[i][0]) * s[1];
          a0[i] <== (c[i][1] - c[i][0]) * s[0];
           a[i] <== (c[i][0]);

         out[i] <== (a210[i] + a21[i] + a20[i] + a2[i]) * s[2] +
                     (a10[i] + a1[i] + a0[i] + a[i]);
    }
}
