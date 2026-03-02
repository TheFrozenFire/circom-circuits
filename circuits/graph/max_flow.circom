pragma circom 2.2.2;

include "core/comparators.circom";
include "packing/bitify.circom";
include "graph/lookup.circom";

/// Max-flow/min-cut LP duality certificate verifier.
///
/// Witness:
///   - flow[nEdges]: flow on each edge
///   - cutLabel[nNodes]: 0 = S-side, 1 = T-side (binary partition)
///
/// Verifies:
///   1. Capacity: 0 ≤ flow[e] ≤ capacity[e]
///   2. Conservation: ∀ intermediate nodes, flow_in = flow_out
///   3. Cut validity: source in S (label=0), target in T (label=1)
///   4. Strong duality: flow value = cut capacity
///
/// O(nNodes × nEdges) for conservation checks.
template Graph_MaxFlowMinCut(nNodes, nEdges, nBits) {
    signal input edges[nEdges][2];
    signal input capacity[nEdges];
    signal input source;
    signal input target;

    // Witness
    signal input flow[nEdges];
    signal input cutLabel[nNodes];

    signal output maxFlow;

    // 1. Capacity constraints: 0 <= flow[e] <= capacity[e]
    //    Range-check flow[e] (non-negative) and capacity[e] - flow[e] (non-negative)
    component flowRange[nEdges];
    signal flowBits[nEdges][nBits];
    component slackRange[nEdges];
    signal capSlack[nEdges];
    signal slackBits[nEdges][nBits];

    for (var i = 0; i < nEdges; i++) {
        flowRange[i] = Num2Bits(nBits);
        flowRange[i].in <== flow[i];
        for (var b = 0; b < nBits; b++) {
            flowBits[i][b] <== flowRange[i].out[b];
        }

        capSlack[i] <== capacity[i] - flow[i];
        slackRange[i] = Num2Bits(nBits);
        slackRange[i].in <== capSlack[i];
        for (var b = 0; b < nBits; b++) {
            slackBits[i][b] <== slackRange[i].out[b];
        }
    }

    // 2. Flow conservation: for each non-source, non-target node,
    //    sum of incoming flow = sum of outgoing flow.
    //    Uses compile-time node index matching against edge endpoints.
    component isSrc[nNodes];
    component isTgt[nNodes];
    signal isIntermediate[nNodes];
    signal nodeFlowBalance[nNodes];

    for (var n = 0; n < nNodes; n++) {
        isSrc[n] = IsEqual();
        isSrc[n].in[0] <== n;
        isSrc[n].in[1] <== source;

        isTgt[n] = IsEqual();
        isTgt[n].in[0] <== n;
        isTgt[n].in[1] <== target;

        // isIntermediate = 1 if not source and not target
        isIntermediate[n] <== (1 - isSrc[n].out) * (1 - isTgt[n].out);
    }

    // Flow conservation: for each node, compute flow_in - flow_out
    component edgeSrcEq[nNodes][nEdges];
    component edgeDstEq[nNodes][nEdges];
    signal srcMatch[nNodes][nEdges];
    signal dstMatch[nNodes][nEdges];
    signal outFlow[nNodes][nEdges];
    signal inFlow[nNodes][nEdges];
    signal balance[nNodes];
    signal balanceCheck[nNodes];

    for (var n = 0; n < nNodes; n++) {
        var balanceSum = 0;
        for (var e = 0; e < nEdges; e++) {
            edgeSrcEq[n][e] = IsEqual();
            edgeSrcEq[n][e].in[0] <== edges[e][0];
            edgeSrcEq[n][e].in[1] <== n;

            edgeDstEq[n][e] = IsEqual();
            edgeDstEq[n][e].in[0] <== edges[e][1];
            edgeDstEq[n][e].in[1] <== n;

            outFlow[n][e] <== edgeSrcEq[n][e].out * flow[e];
            inFlow[n][e] <== edgeDstEq[n][e].out * flow[e];

            balanceSum += inFlow[n][e] - outFlow[n][e];
        }
        balance[n] <== balanceSum;

        // If intermediate, balance must be 0
        // balance * isIntermediate = 0
        balanceCheck[n] <== balance[n] * isIntermediate[n];
        balanceCheck[n] === 0;
    }

    // Compute flow value = net flow out of source
    // flowValue = sum of outgoing flow from source - sum of incoming flow to source
    // We already have balance[source] which is inFlow - outFlow, so flowValue = -balance[source]
    // But source is dynamic, so use Lookup
    component flowValueLookup = Lookup(nNodes);
    flowValueLookup.sel <== source;
    for (var n = 0; n < nNodes; n++) {
        flowValueLookup.in[n] <== balance[n];
    }
    // flowValue = -(balance at source) = outflow - inflow at source
    // balance = inflow - outflow, so negate
    // In field: negate by subtracting from 0
    signal flowValue <== 0 - flowValueLookup.out;

    // 3. Cut validity: cutLabel is binary, source in S (0), target in T (1)
    signal cutBinary[nNodes];
    for (var n = 0; n < nNodes; n++) {
        cutBinary[n] <== cutLabel[n] * (cutLabel[n] - 1);
        cutBinary[n] === 0;  // binary constraint
    }

    component srcCutLookup = Lookup(nNodes);
    srcCutLookup.sel <== source;
    for (var n = 0; n < nNodes; n++) {
        srcCutLookup.in[n] <== cutLabel[n];
    }
    srcCutLookup.out === 0;  // source in S

    component tgtCutLookup = Lookup(nNodes);
    tgtCutLookup.sel <== target;
    for (var n = 0; n < nNodes; n++) {
        tgtCutLookup.in[n] <== cutLabel[n];
    }
    tgtCutLookup.out === 1;  // target in T

    // Compute cut capacity: sum of capacity[e] where src in S and dst in T
    // crossCut[e] = (1 - cutLabel[src]) * cutLabel[dst]
    component cutSrcLookup[nEdges];
    component cutDstLookup[nEdges];
    signal srcInS[nEdges];
    signal dstInT[nEdges];
    signal crossCut[nEdges];
    signal cutEdgeCapacity[nEdges];
    var cutCapSum = 0;

    for (var e = 0; e < nEdges; e++) {
        cutSrcLookup[e] = Lookup(nNodes);
        cutSrcLookup[e].sel <== edges[e][0];
        for (var n = 0; n < nNodes; n++) {
            cutSrcLookup[e].in[n] <== cutLabel[n];
        }

        cutDstLookup[e] = Lookup(nNodes);
        cutDstLookup[e].sel <== edges[e][1];
        for (var n = 0; n < nNodes; n++) {
            cutDstLookup[e].in[n] <== cutLabel[n];
        }

        srcInS[e] <== 1 - cutSrcLookup[e].out;
        dstInT[e] <== cutDstLookup[e].out;
        crossCut[e] <== srcInS[e] * dstInT[e];
        cutEdgeCapacity[e] <== crossCut[e] * capacity[e];
        cutCapSum += cutEdgeCapacity[e];
    }

    signal cutCapacity <== cutCapSum;

    // 4. Strong duality: flow value = cut capacity
    flowValue === cutCapacity;

    maxFlow <== flowValue;
}
