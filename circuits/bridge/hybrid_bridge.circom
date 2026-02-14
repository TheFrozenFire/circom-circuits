pragma circom 2.2.2;

include "search/commit.circom";
include "bridge/uhf.circom";

/// Proves private data matches both a Poseidon commitment and a polynomial
/// UHF evaluation, bridging in-circuit Poseidon with cheap on-chain
/// verification via an external commitment scheme (Keccak, KZG, etc.).
///
/// Public inputs: poseidonCommit, uhfValue, challenge.
/// The external commitment is verified on-chain, not in-circuit.
///
/// Constraints: VectorCommit(n, chunkSize) + (n-1).
template HybridBridge(n, chunkSize) {
    signal input data[n];
    signal input poseidonCommit;
    signal input uhfValue;
    signal input challenge;

    // 1. Verify Poseidon commitment
    component vc = VectorCommit(n, chunkSize);
    for (var i = 0; i < n; i++) {
        vc.v[i] <== data[i];
    }
    vc.out === poseidonCommit;

    // 2. Verify UHF evaluation
    component uhf = PolyUHF(n);
    uhf.r <== challenge;
    for (var i = 0; i < n; i++) {
        uhf.x[i] <== data[i];
    }
    uhf.out === uhfValue;
}
