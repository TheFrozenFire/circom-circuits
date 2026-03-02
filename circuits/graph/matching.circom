pragma circom 2.2.2;

include "core/comparators.circom";
include "graph/lookup.circom";

/// Verify a maximum bipartite matching via König's theorem.
///
/// Graph: bipartite with nLeft left-nodes and nRight right-nodes.
/// Edges connect left to right nodes (indices are per-side).
///
/// Witness:
///   - matchMask[nEdges]: binary, 1 if edge is in matching
///   - coverLeft[nLeft]: binary, 1 if left node is in vertex cover
///   - coverRight[nRight]: binary, 1 if right node is in vertex cover
///
/// Checks:
///   1. Binary: matchMask, coverLeft, coverRight all {0,1}
///   2. Matching: no node incident to >1 matching edge
///   3. Cover: every edge has at least one endpoint in cover
///   4. König: |matching| = |cover| (proves both optimal)
///
/// O(nEdges × (nLeft + nRight)).
template Graph_BipartiteMatching(nLeft, nRight, nEdges, nBits) {
    signal input leftNode[nEdges];
    signal input rightNode[nEdges];

    // Witness
    signal input matchMask[nEdges];
    signal input coverLeft[nLeft];
    signal input coverRight[nRight];

    signal output matchingSize;

    // 1. Binary constraints
    signal matchBinary[nEdges];
    for (var e = 0; e < nEdges; e++) {
        matchBinary[e] <== matchMask[e] * (matchMask[e] - 1);
        matchBinary[e] === 0;
    }
    signal coverLeftBinary[nLeft];
    for (var i = 0; i < nLeft; i++) {
        coverLeftBinary[i] <== coverLeft[i] * (coverLeft[i] - 1);
        coverLeftBinary[i] === 0;
    }
    signal coverRightBinary[nRight];
    for (var i = 0; i < nRight; i++) {
        coverRightBinary[i] <== coverRight[i] * (coverRight[i] - 1);
        coverRightBinary[i] === 0;
    }

    // 2. Matching validity: at most 1 matching edge per node
    // Left nodes
    component leftEq[nLeft][nEdges];
    signal leftMatchInc[nLeft][nEdges];
    signal leftMatchCount[nLeft];
    signal leftCountCheck[nLeft];

    for (var i = 0; i < nLeft; i++) {
        var count = 0;
        for (var e = 0; e < nEdges; e++) {
            leftEq[i][e] = IsEqual();
            leftEq[i][e].in[0] <== leftNode[e];
            leftEq[i][e].in[1] <== i;
            leftMatchInc[i][e] <== leftEq[i][e].out * matchMask[e];
            count += leftMatchInc[i][e];
        }
        leftMatchCount[i] <== count;
        // count ∈ {0,1}: count * (count - 1) = 0
        leftCountCheck[i] <== leftMatchCount[i] * (leftMatchCount[i] - 1);
        leftCountCheck[i] === 0;
    }

    // Right nodes
    component rightEq[nRight][nEdges];
    signal rightMatchInc[nRight][nEdges];
    signal rightMatchCount[nRight];
    signal rightCountCheck[nRight];

    for (var i = 0; i < nRight; i++) {
        var count = 0;
        for (var e = 0; e < nEdges; e++) {
            rightEq[i][e] = IsEqual();
            rightEq[i][e].in[0] <== rightNode[e];
            rightEq[i][e].in[1] <== i;
            rightMatchInc[i][e] <== rightEq[i][e].out * matchMask[e];
            count += rightMatchInc[i][e];
        }
        rightMatchCount[i] <== count;
        rightCountCheck[i] <== rightMatchCount[i] * (rightMatchCount[i] - 1);
        rightCountCheck[i] === 0;
    }

    // 3. Cover validity: every edge has at least one endpoint in cover
    component leftCoverLookup[nEdges];
    component rightCoverLookup[nEdges];
    signal coverSum[nEdges];
    component coverNonzero[nEdges];

    for (var e = 0; e < nEdges; e++) {
        leftCoverLookup[e] = Lookup(nLeft);
        leftCoverLookup[e].sel <== leftNode[e];
        for (var i = 0; i < nLeft; i++) {
            leftCoverLookup[e].in[i] <== coverLeft[i];
        }

        rightCoverLookup[e] = Lookup(nRight);
        rightCoverLookup[e].sel <== rightNode[e];
        for (var i = 0; i < nRight; i++) {
            rightCoverLookup[e].in[i] <== coverRight[i];
        }

        coverSum[e] <== leftCoverLookup[e].out + rightCoverLookup[e].out;
        coverNonzero[e] = IsZero();
        coverNonzero[e].in <== coverSum[e];
        coverNonzero[e].out === 0;
    }

    // 4. König: |matching| = |cover|
    var mSize = 0;
    for (var e = 0; e < nEdges; e++) {
        mSize += matchMask[e];
    }
    var cSize = 0;
    for (var i = 0; i < nLeft; i++) {
        cSize += coverLeft[i];
    }
    for (var i = 0; i < nRight; i++) {
        cSize += coverRight[i];
    }

    signal mSizeSignal <== mSize;
    signal cSizeSignal <== cSize;
    mSizeSignal === cSizeSignal;

    matchingSize <== mSizeSignal;
}
