pragma circom 2.2.2;

include "core/comparators.circom";
include "graph/lookup.circom";

/// Verify a node sequence is a valid path in the graph.
/// For each consecutive pair (path[i], path[i+1]), checks that at least one edge matches.
/// O(nSteps × nEdges) IsEqual checks.
template Graph_VerifyPath(nNodes, nEdges, nSteps) {
    signal input edges[nEdges][2];
    signal input path[nSteps + 1];

    component srcEq[nSteps][nEdges];
    component dstEq[nSteps][nEdges];
    signal srcDstMatch[nSteps][nEdges];
    signal stepMatchCount[nSteps];
    component nonzero[nSteps];

    for (var i = 0; i < nSteps; i++) {
        var matchSum = 0;
        for (var j = 0; j < nEdges; j++) {
            srcEq[i][j] = IsEqual();
            srcEq[i][j].in[0] <== path[i];
            srcEq[i][j].in[1] <== edges[j][0];

            dstEq[i][j] = IsEqual();
            dstEq[i][j].in[0] <== path[i + 1];
            dstEq[i][j].in[1] <== edges[j][1];

            // Both src and dst must match for this edge to be the path step
            srcDstMatch[i][j] <== srcEq[i][j].out * dstEq[i][j].out;
            matchSum += srcDstMatch[i][j];
        }
        // At least one edge must match each step
        stepMatchCount[i] <== matchSum;

        nonzero[i] = IsZero();
        nonzero[i].in <== stepMatchCount[i];
        nonzero[i].out === 0;  // matchCount != 0
    }
}

/// Compute the cost of a path given edge properties.
/// Witness: edgeIndices[nSteps] tells which edge is used at each step.
/// Verifies edge matches path step, accumulates cost from edgeProps.
/// O(nSteps × nEdges) for lookups.
template Graph_PathCost(nNodes, nEdges, nEdgeProps, nSteps, costPropIdx) {
    signal input edges[nEdges][2];
    signal input edgeProps[nEdges][nEdgeProps];
    signal input path[nSteps + 1];
    signal input edgeIndices[nSteps];
    signal output totalCost;

    component edgeSrcLookup[nSteps];
    component edgeDstLookup[nSteps];
    component costLookup[nSteps];
    component srcCheck[nSteps];
    component dstCheck[nSteps];

    signal stepCost[nSteps];
    var costSum = 0;

    for (var i = 0; i < nSteps; i++) {
        // Lookup edge src, dst, and cost by edgeIndex
        // For src values of all edges
        edgeSrcLookup[i] = Lookup(nEdges);
        edgeSrcLookup[i].sel <== edgeIndices[i];
        for (var j = 0; j < nEdges; j++) {
            edgeSrcLookup[i].in[j] <== edges[j][0];
        }

        edgeDstLookup[i] = Lookup(nEdges);
        edgeDstLookup[i].sel <== edgeIndices[i];
        for (var j = 0; j < nEdges; j++) {
            edgeDstLookup[i].in[j] <== edges[j][1];
        }

        costLookup[i] = Lookup(nEdges);
        costLookup[i].sel <== edgeIndices[i];
        for (var j = 0; j < nEdges; j++) {
            costLookup[i].in[j] <== edgeProps[j][costPropIdx];
        }

        // Verify the looked-up edge matches the path step
        srcCheck[i] = IsEqual();
        srcCheck[i].in[0] <== edgeSrcLookup[i].out;
        srcCheck[i].in[1] <== path[i];
        srcCheck[i].out === 1;

        dstCheck[i] = IsEqual();
        dstCheck[i].in[0] <== edgeDstLookup[i].out;
        dstCheck[i].in[1] <== path[i + 1];
        dstCheck[i].out === 1;

        stepCost[i] <== costLookup[i].out;
        costSum += stepCost[i];
    }

    totalCost <== costSum;
}
