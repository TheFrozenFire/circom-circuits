pragma circom 2.2.2;

include "circomlib/circuits/bitify.circom";
include "circomlib/circuits/comparators.circom";

template AND() {
    signal input in[2];
    signal output out;

    // (2AB - A - B + 1) * B
    signal equality <== (2 * in[0] * in[1]) - in[0] - in[1] + 1;
     // Lower if B is low
    out <== equality * in[1];
}

template OR() {
    signal input in[2];
    signal output out;

    // (A + B) - AB
    out <== (in[0] + in[1]) - (in[0] * in[1]);
}

template XOR() {
    signal input in[2];
    signal output out;

    // A + B - 2AB
    out <== (in[0] + in[1]) - (2 * in[0] * in[1]);
}

template MUXOR(n) {
    signal input in[n];
    signal output out;

    signal intermediate[n - 1];
    intermediate[0] <== XOR() ([in[0], in[1]]);
    for (var i = 1; i < n - 1; i++) {
        intermediate[i] <== XOR() ([intermediate[i - 1], in[i + 1]]);
    }
    out <== intermediate[n - 2];
}

template MultiXOR(n) {
    signal input in[2][n];
    signal output out[n];

    for (var i = 0; i < n; i++) {
        out[i] <== XOR() ([in[0][i], in[1][i]]);
    }
}

template BitwiseAND(n) {
    signal input a;
    signal input b;
    
    signal output out;
    
    component bitify[2];
    bitify[0] = Num2Bits(n);
    bitify[1] = Num2Bits(n);
    
    bitify[0].in <== a;
    bitify[1].in <== b;
    
    component debitify = Bits2Num(n);
    for(var i = 0; i < n; i++) {
        debitify.in[i] <== AND() ([bitify[0].out[i], bitify[1].out[i]]);
    }
    
    out <== debitify.out;
}

template BitwiseOR(n) {
    signal input a;
    signal input b;
    
    signal output out;
    
    component bitify[2];
    bitify[0] = Num2Bits(n);
    bitify[1] = Num2Bits(n);
    
    bitify[0].in <== a;
    bitify[1].in <== b;
    
    component debitify = Bits2Num(n);
    for(var i = 0; i < n; i++) {
        debitify.in[i] <== OR() ([bitify[0].out[i], bitify[1].out[i]]);
    }
    
    out <== debitify.out;
}

template BitwiseNOT(n) {
    signal input a;
    
    signal output out;
    
    out <== (2**n) - a - 1;
}

template BitwiseXOR(n) {
    signal input a;
    signal input b;
    
    signal output out;
    
    component bitify[2];
    bitify[0] = Num2Bits(n);
    bitify[1] = Num2Bits(n);
    
    bitify[0].in <== a;
    bitify[1].in <== b;
    
    component debitify = Bits2Num(n);
    for(var i = 0; i < n; i++) {
        debitify.in[i] <== XOR() ([bitify[0].out[i], bitify[1].out[i]]);
    }
    
    out <== debitify.out;
}