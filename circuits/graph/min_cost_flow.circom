pragma circom 2.2.2;

include "core/comparators.circom";
include "packing/bitify.circom";
include "graph/lookup.circom";

/// Verify a minimum-cost flow via reduced cost optimality.
///
/// Witness:
///   - flow[nEdges]: flow on each edge
///   - potential[nNodes]: node potentials (dual variables)
///   - rcPlus[nEdges]: positive part of reduced cost (≥ 0)
///   - rcMinus[nEdges]: negative part of reduced cost (≥ 0)
///
/// Checks:
///   1. Capacity: 0 ≤ flow[e] ≤ capacity[e]
///   2. Conservation: flow_in - flow_out = demand[n] for all nodes
///   3. Reduced cost decomposition:
///      rc[e] = cost[e] + potential[src] - potential[dst]
///      rc[e] = rcPlus[e] - rcMinus[e]
///      Range-check rcPlus, rcMinus ≥ 0
///   4. Complementary slackness:
///      flow[e] × rcPlus[e] = 0    (if flow > 0 then rc ≤ 0)
///      capSlack[e] × rcMinus[e] = 0 (if slack > 0 then rc ≥ 0)
///
/// O(nNodes × nEdges) for conservation + O(nEdges × nNodes) for potential lookups.
template Graph_MinCostFlow(nNodes, nEdges, nBits) {
    signal input edges[nEdges][2];
    signal input capacity[nEdges];
    signal input cost[nEdges];
    signal input demand[nNodes];

    // Witness
    signal input flow[nEdges];
    signal input potential[nNodes];
    signal input rcPlus[nEdges];
    signal input rcMinus[nEdges];

    signal output totalCost;

    // 1. Capacity constraints: 0 ≤ flow[e] ≤ capacity[e]
    component flowRange[nEdges];
    signal flowBits[nEdges][nBits];
    signal capSlack[nEdges];
    component slackRange[nEdges];
    signal slackBits[nEdges][nBits];

    for (var e = 0; e < nEdges; e++) {
        flowRange[e] = Num2Bits(nBits);
        flowRange[e].in <== flow[e];
        for (var b = 0; b < nBits; b++) {
            flowBits[e][b] <== flowRange[e].out[b];
        }

        capSlack[e] <== capacity[e] - flow[e];
        slackRange[e] = Num2Bits(nBits);
        slackRange[e].in <== capSlack[e];
        for (var b = 0; b < nBits; b++) {
            slackBits[e][b] <== slackRange[e].out[b];
        }
    }

    // 2. Flow conservation: flow_in - flow_out = demand[n]
    component edgeSrcEq[nNodes][nEdges];
    component edgeDstEq[nNodes][nEdges];
    signal outFlow[nNodes][nEdges];
    signal inFlow[nNodes][nEdges];
    signal balance[nNodes];

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
        balance[n] === demand[n];
    }

    // 3. Reduced cost decomposition
    //    rc[e] = cost[e] + potential[src] - potential[dst]
    //    rc[e] === rcPlus[e] - rcMinus[e]
    component potSrcLookup[nEdges];
    component potDstLookup[nEdges];
    signal reducedCost[nEdges];
    signal rcReconstruct[nEdges];

    component rcPlusRange[nEdges];
    signal rcPlusBits[nEdges][nBits];
    component rcMinusRange[nEdges];
    signal rcMinusBits[nEdges][nBits];

    for (var e = 0; e < nEdges; e++) {
        potSrcLookup[e] = Lookup(nNodes);
        potSrcLookup[e].sel <== edges[e][0];
        for (var n = 0; n < nNodes; n++) {
            potSrcLookup[e].in[n] <== potential[n];
        }

        potDstLookup[e] = Lookup(nNodes);
        potDstLookup[e].sel <== edges[e][1];
        for (var n = 0; n < nNodes; n++) {
            potDstLookup[e].in[n] <== potential[n];
        }

        reducedCost[e] <== cost[e] + potSrcLookup[e].out - potDstLookup[e].out;

        // Decompose: rc = rcPlus - rcMinus
        rcReconstruct[e] <== rcPlus[e] - rcMinus[e];
        reducedCost[e] === rcReconstruct[e];

        // Range-check rcPlus and rcMinus (non-negative)
        rcPlusRange[e] = Num2Bits(nBits);
        rcPlusRange[e].in <== rcPlus[e];
        for (var b = 0; b < nBits; b++) {
            rcPlusBits[e][b] <== rcPlusRange[e].out[b];
        }

        rcMinusRange[e] = Num2Bits(nBits);
        rcMinusRange[e].in <== rcMinus[e];
        for (var b = 0; b < nBits; b++) {
            rcMinusBits[e][b] <== rcMinusRange[e].out[b];
        }
    }

    // 4. Complementary slackness
    signal csFlow[nEdges];
    signal csSlack[nEdges];

    for (var e = 0; e < nEdges; e++) {
        // If flow > 0, then rcPlus must be 0 (rc ≤ 0)
        csFlow[e] <== flow[e] * rcPlus[e];
        csFlow[e] === 0;

        // If capacity slack > 0, then rcMinus must be 0 (rc ≥ 0)
        csSlack[e] <== capSlack[e] * rcMinus[e];
        csSlack[e] === 0;
    }

    // 5. Total cost
    signal edgeCostContrib[nEdges];
    var costSum = 0;
    for (var e = 0; e < nEdges; e++) {
        edgeCostContrib[e] <== cost[e] * flow[e];
        costSum += edgeCostContrib[e];
    }
    totalCost <== costSum;
}
