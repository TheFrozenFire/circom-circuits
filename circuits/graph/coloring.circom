pragma circom 2.2.2;

include "core/comparators.circom";
include "graph/lookup.circom";

/// Verify a k-coloring of a graph: no adjacent nodes share a color.
/// O(nEdges × nNodes) Lookup + O(nNodes × nBits) range checks.
template Graph_Coloring(nNodes, nEdges, nColors, nBits) {
    signal input edges[nEdges][2];
    signal input colors[nNodes];

    // 1. Range-check: 0 <= colors[i] < nColors
    component colorRange[nNodes];
    for (var i = 0; i < nNodes; i++) {
        colorRange[i] = LessThan(nBits);
        colorRange[i].in[0] <== colors[i];
        colorRange[i].in[1] <== nColors;
        colorRange[i].out === 1;
    }

    // 2. For each edge, lookup endpoint colors and check they differ
    component srcColor[nEdges];
    component dstColor[nEdges];
    component colorEq[nEdges];

    for (var i = 0; i < nEdges; i++) {
        srcColor[i] = Lookup(nNodes);
        srcColor[i].sel <== edges[i][0];
        for (var j = 0; j < nNodes; j++) {
            srcColor[i].in[j] <== colors[j];
        }

        dstColor[i] = Lookup(nNodes);
        dstColor[i].sel <== edges[i][1];
        for (var j = 0; j < nNodes; j++) {
            dstColor[i].in[j] <== colors[j];
        }

        colorEq[i] = IsEqual();
        colorEq[i].in[0] <== srcColor[i].out;
        colorEq[i].in[1] <== dstColor[i].out;
        colorEq[i].out === 0;
    }
}
