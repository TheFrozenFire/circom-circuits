pragma circom 2.2.2;

include "hash/poseidon.circom";

/// Hashes an n-element vector into a single field element using
/// chunked Poseidon hashing with binary tree reduction.
///
/// For n=384, chunkSize=12: 32 chunks hashed with Poseidon(12),
/// reduced via a 5-level binary tree of Poseidon(2).
template VectorCommit(n, chunkSize) {
    signal input v[n];
    signal output out;

    var nChunks = n / chunkSize;

    // Chunk hashing: each group of chunkSize elements → Poseidon(chunkSize)
    component chunkHash[nChunks];
    for (var i = 0; i < nChunks; i++) {
        chunkHash[i] = Poseidon(chunkSize);
        for (var j = 0; j < chunkSize; j++) {
            chunkHash[i].inputs[j] <== v[i * chunkSize + j];
        }
    }

    // Binary tree reduction using Poseidon(2).
    // Uses heap layout: root at index 0, children of node i at 2i+1 and 2i+2.
    // Leaves (chunk hashes) at indices nChunks-1 through 2*nChunks-2.
    signal nodes[2 * nChunks - 1];
    for (var i = 0; i < nChunks; i++) {
        nodes[nChunks - 1 + i] <== chunkHash[i].out;
    }

    component treeHash[nChunks - 1];
    for (var i = nChunks - 2; i >= 0; i--) {
        treeHash[i] = Poseidon(2);
        treeHash[i].inputs[0] <== nodes[2 * i + 1];
        treeHash[i].inputs[1] <== nodes[2 * i + 2];
        nodes[i] <== treeHash[i].out;
    }

    out <== nodes[0];
}
