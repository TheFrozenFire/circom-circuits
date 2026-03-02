pragma circom 2.2.2;

include "core/comparators.circom";
include "packing/bitify.circom";
include "graph/lookup.circom";

/// Bellman-Ford shortest path certificate verifier.
///
/// "Verify, don't compute": the prover runs Bellman-Ford off-chain and provides:
///   - dist[nNodes]: distance labels
///   - path[nSteps+1]: the shortest path nodes
///   - edgeIndices[nSteps]: which edge is used at each path step
///
/// The circuit verifies:
///   1. dist[source] = 0
///   2. Dual feasibility: ∀ edges (u,v,w): dist[v] ≤ dist[u] + w
///      (triangle inequality — proves no path can beat dist[target])
///   3. Primal feasibility: path is valid, each step uses correct edge, cost = dist[target]
///
/// O(nEdges × nNodes) for dual + O(nSteps × nEdges) for path verification.
template Graph_ShortestPath(nNodes, nEdges, nSteps, nBits, costPropIdx) {
    signal input edges[nEdges][2];
    signal input edgeProps[nEdges];  // cost per edge (single property: cost)
    signal input source;
    signal input target;

    // Witness: distance labels, path, and edge indices
    signal input dist[nNodes];
    signal input path[nSteps + 1];
    signal input edgeIndices[nSteps];

    signal output shortestDist;

    // 1. dist[source] = 0
    component srcDistLookup = Lookup(nNodes);
    srcDistLookup.sel <== source;
    for (var i = 0; i < nNodes; i++) {
        srcDistLookup.in[i] <== dist[i];
    }
    srcDistLookup.out === 0;

    // 2. Dual feasibility: for every edge (u,v), dist[v] <= dist[u] + edgeProps[e]
    //    Equivalently: dist[u] + edgeProps[e] - dist[v] >= 0, range-checked via Num2Bits
    component edgeSrcDist[nEdges];
    component edgeDstDist[nEdges];
    signal slack[nEdges];
    component slackRange[nEdges];
    signal _slackBits[nEdges][nBits];

    for (var i = 0; i < nEdges; i++) {
        edgeSrcDist[i] = Lookup(nNodes);
        edgeSrcDist[i].sel <== edges[i][0];
        for (var j = 0; j < nNodes; j++) {
            edgeSrcDist[i].in[j] <== dist[j];
        }

        edgeDstDist[i] = Lookup(nNodes);
        edgeDstDist[i].sel <== edges[i][1];
        for (var j = 0; j < nNodes; j++) {
            edgeDstDist[i].in[j] <== dist[j];
        }

        // slack = dist[u] + w - dist[v] >= 0
        slack[i] <== edgeSrcDist[i].out + edgeProps[i] - edgeDstDist[i].out;
        // Range-check: slack fits in nBits bits (proves non-negative)
        slackRange[i] = Num2Bits(nBits);
        slackRange[i].in <== slack[i];
        for (var b = 0; b < nBits; b++) {
            _slackBits[i][b] <== slackRange[i].out[b];
        }
    }

    // 3. Primal feasibility: verify path and compute cost
    //    path[0] = source, path[nSteps] = target
    component pathStartCheck = IsEqual();
    pathStartCheck.in[0] <== path[0];
    pathStartCheck.in[1] <== source;
    pathStartCheck.out === 1;

    component pathEndCheck = IsEqual();
    pathEndCheck.in[0] <== path[nSteps];
    pathEndCheck.in[1] <== target;
    pathEndCheck.out === 1;

    // Verify each path step uses the correct edge and accumulate cost
    component stepSrcLookup[nSteps];
    component stepDstLookup[nSteps];
    component stepCostLookup[nSteps];
    component stepSrcCheck[nSteps];
    component stepDstCheck[nSteps];
    signal stepCost[nSteps];
    var totalCost = 0;

    for (var i = 0; i < nSteps; i++) {
        // Lookup edge src by edgeIndex
        stepSrcLookup[i] = Lookup(nEdges);
        stepSrcLookup[i].sel <== edgeIndices[i];
        for (var j = 0; j < nEdges; j++) {
            stepSrcLookup[i].in[j] <== edges[j][0];
        }

        // Lookup edge dst by edgeIndex
        stepDstLookup[i] = Lookup(nEdges);
        stepDstLookup[i].sel <== edgeIndices[i];
        for (var j = 0; j < nEdges; j++) {
            stepDstLookup[i].in[j] <== edges[j][1];
        }

        // Lookup edge cost by edgeIndex
        stepCostLookup[i] = Lookup(nEdges);
        stepCostLookup[i].sel <== edgeIndices[i];
        for (var j = 0; j < nEdges; j++) {
            stepCostLookup[i].in[j] <== edgeProps[j];
        }

        // Verify edge matches path step
        stepSrcCheck[i] = IsEqual();
        stepSrcCheck[i].in[0] <== stepSrcLookup[i].out;
        stepSrcCheck[i].in[1] <== path[i];
        stepSrcCheck[i].out === 1;

        stepDstCheck[i] = IsEqual();
        stepDstCheck[i].in[0] <== stepDstLookup[i].out;
        stepDstCheck[i].in[1] <== path[i + 1];
        stepDstCheck[i].out === 1;

        stepCost[i] <== stepCostLookup[i].out;
        totalCost += stepCost[i];
    }

    // 4. Strong duality: path cost = dist[target]
    component tgtDistLookup = Lookup(nNodes);
    tgtDistLookup.sel <== target;
    for (var i = 0; i < nNodes; i++) {
        tgtDistLookup.in[i] <== dist[i];
    }

    signal pathCost <== totalCost;
    pathCost === tgtDistLookup.out;

    shortestDist <== tgtDistLookup.out;
}
