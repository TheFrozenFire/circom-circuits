pragma circom 2.2.2;

include "core/comparators.circom";
include "graph/lookup.circom";

/// Extract property values for a subset of nodes.
/// Looks up nodeProps[subset[i]][propIdx] for each node in the subset.
template Graph_SubsetAggregate(nNodes, nNodeProps, nSubset, propIdx) {
    signal input nodeProps[nNodes][nNodeProps];
    signal input subset[nSubset];
    signal output out[nSubset];

    component propLookup[nSubset];

    for (var i = 0; i < nSubset; i++) {
        // Build 1D array of propIdx values for all nodes
        propLookup[i] = Lookup(nNodes);
        propLookup[i].sel <== subset[i];
        for (var j = 0; j < nNodes; j++) {
            propLookup[i].in[j] <== nodeProps[j][propIdx];
        }
        out[i] <== propLookup[i].out;
    }
}

/// Range-check a property for each node in a subset: lo <= prop < hi.
/// nSubset Lookup + 2×nSubset LessThan.
template Graph_SubsetPropertyCheck(nNodes, nNodeProps, nSubset, propIdx, nBits) {
    signal input nodeProps[nNodes][nNodeProps];
    signal input subset[nSubset];
    signal input lo;
    signal input hi;

    component propLookup[nSubset];
    component geLo[nSubset];
    component ltHi[nSubset];

    for (var i = 0; i < nSubset; i++) {
        propLookup[i] = Lookup(nNodes);
        propLookup[i].sel <== subset[i];
        for (var j = 0; j < nNodes; j++) {
            propLookup[i].in[j] <== nodeProps[j][propIdx];
        }

        // lo <= prop: !(prop < lo)
        geLo[i] = LessThan(nBits);
        geLo[i].in[0] <== propLookup[i].out;
        geLo[i].in[1] <== lo;
        geLo[i].out === 0;

        // prop < hi
        ltHi[i] = LessThan(nBits);
        ltHi[i].in[0] <== propLookup[i].out;
        ltHi[i].in[1] <== hi;
        ltHi[i].out === 1;
    }
}
