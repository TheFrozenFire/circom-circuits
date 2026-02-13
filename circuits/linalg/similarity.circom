pragma circom 2.2.2;

include "comparators.circom";
include "packing/bitify.circom";

/// Proves cos(a,b) >= t without division or sqrt.
/// Rewrites as: (a·b)^2 >= threshold_sq * ||a||^2 * ||b||^2
/// Also checks a·b >= 0 (rejects anti-parallel vectors).
/// Constraint-only template (no outputs).
template CosineSimilarityCheck(n, bits) {
    signal input a[n];
    signal input b[n];
    signal input threshold_sq;

    // Compute dot product a·b
    signal dotProducts[n];
    var dotSum = 0;
    for (var i = 0; i < n; i++) {
        dotProducts[i] <== a[i] * b[i];
        dotSum += dotProducts[i];
    }
    signal dotAB;
    dotAB <== dotSum;

    // Compute ||a||^2
    signal sqA[n];
    var normSumA = 0;
    for (var i = 0; i < n; i++) {
        sqA[i] <== a[i] * a[i];
        normSumA += sqA[i];
    }
    signal normSqA;
    normSqA <== normSumA;

    // Compute ||b||^2
    signal sqB[n];
    var normSumB = 0;
    for (var i = 0; i < n; i++) {
        sqB[i] <== b[i] * b[i];
        normSumB += sqB[i];
    }
    signal normSqB;
    normSqB <== normSumB;

    // lhs = dotAB^2
    signal lhs;
    lhs <== dotAB * dotAB;

    // rhs = threshold_sq * normSqA * normSqB
    signal normProd;
    normProd <== normSqA * normSqB;
    signal rhs;
    rhs <== threshold_sq * normProd;

    // Verify lhs >= rhs (i.e., NOT lhs < rhs)
    component lt = LessThan(bits);
    lt.in[0] <== lhs;
    lt.in[1] <== rhs;
    lt.out === 0;

    // Sign check: dotAB must be non-negative (fits in bits)
    component signCheck = Num2Bits(bits);
    signCheck.in <== dotAB;
}

/// Proves the claimed index is the nearest neighbor among k candidates.
/// Constraint-only template (no outputs).
template NearestNeighborCheck(n, k, bits) {
    signal input query[n];
    signal input candidates[k][n];
    signal input claimedIdx;

    // Compute squared distances for all candidates
    signal diff[k][n];
    signal sq[k][n];
    signal dist[k];

    for (var c = 0; c < k; c++) {
        var sum = 0;
        for (var i = 0; i < n; i++) {
            diff[c][i] <== query[i] - candidates[c][i];
            sq[c][i] <== diff[c][i] * diff[c][i];
            sum += sq[c][i];
        }
        dist[c] <== sum;
    }

    // Extract dist[claimedIdx] via IsEqual indicator mux
    component isIdx[k];
    signal terms[k];
    var claimedDistSum = 0;
    for (var c = 0; c < k; c++) {
        isIdx[c] = IsEqual();
        isIdx[c].in[0] <== claimedIdx;
        isIdx[c].in[1] <== c;
        terms[c] <== isIdx[c].out * dist[c];
        claimedDistSum += terms[c];
    }
    signal claimedDist;
    claimedDist <== claimedDistSum;

    // Verify claimedDist <= dist[c] for all c (i.e., NOT dist[c] < claimedDist)
    component lt[k];
    for (var c = 0; c < k; c++) {
        lt[c] = LessThan(bits);
        lt[c].in[0] <== dist[c];
        lt[c].in[1] <== claimedDist;
        lt[c].out === 0;
    }
}
