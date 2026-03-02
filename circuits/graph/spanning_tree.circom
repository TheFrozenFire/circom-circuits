pragma circom 2.2.2;

include "core/comparators.circom";
include "packing/bitify.circom";
include "graph/lookup.circom";

/// Verify a spanning tree of an undirected graph via parent-pointer certificate.
///
/// Witness:
///   - root: the root node
///   - parent[nNodes]: parent of each node (root has parent = root)
///   - depth[nNodes]: depth of each node (root has depth = 0)
///
/// Checks:
///   1. Root: depth[root] = 0, parent[root] = root
///   2. Range: depth[i] < nNodes, parent[i] < nNodes
///   3. Tree structure: for non-root i, depth[i] = depth[parent[i]] + 1
///   4. Edge membership: for non-root i, (i, parent[i]) or (parent[i], i) is a graph edge
///
/// O(nNodes × nEdges) for edge membership (dominant term).
template Graph_SpanningTree(nNodes, nEdges, nBits) {
    signal input edges[nEdges][2];
    signal input root;
    signal input parent[nNodes];
    signal input depth[nNodes];

    // --- Root checks ---
    component rootDepthLookup = Lookup(nNodes);
    rootDepthLookup.sel <== root;
    for (var j = 0; j < nNodes; j++) {
        rootDepthLookup.in[j] <== depth[j];
    }
    rootDepthLookup.out === 0;

    component rootParentLookup = Lookup(nNodes);
    rootParentLookup.sel <== root;
    for (var j = 0; j < nNodes; j++) {
        rootParentLookup.in[j] <== parent[j];
    }
    component rootSelfCheck = IsEqual();
    rootSelfCheck.in[0] <== rootParentLookup.out;
    rootSelfCheck.in[1] <== root;
    rootSelfCheck.out === 1;

    // --- Range checks ---
    component depthRange[nNodes];
    component parentRange[nNodes];
    for (var i = 0; i < nNodes; i++) {
        depthRange[i] = LessThan(nBits);
        depthRange[i].in[0] <== depth[i];
        depthRange[i].in[1] <== nNodes;
        depthRange[i].out === 1;

        parentRange[i] = LessThan(nBits);
        parentRange[i].in[0] <== parent[i];
        parentRange[i].in[1] <== nNodes;
        parentRange[i].out === 1;
    }

    // --- Tree structure: depth consistency ---
    component isRoot[nNodes];
    component parentDepthLookup[nNodes];
    signal depthDiff[nNodes];
    signal depthCheck[nNodes];

    for (var i = 0; i < nNodes; i++) {
        isRoot[i] = IsEqual();
        isRoot[i].in[0] <== i;
        isRoot[i].in[1] <== root;

        parentDepthLookup[i] = Lookup(nNodes);
        parentDepthLookup[i].sel <== parent[i];
        for (var j = 0; j < nNodes; j++) {
            parentDepthLookup[i].in[j] <== depth[j];
        }

        // For non-root: depth[i] - depth[parent[i]] - 1 = 0
        // For root: multiply by 0 to skip
        depthDiff[i] <== depth[i] - parentDepthLookup[i].out - 1;
        depthCheck[i] <== depthDiff[i] * (1 - isRoot[i].out);
        depthCheck[i] === 0;
    }

    // --- Edge membership: (i, parent[i]) or (parent[i], i) must be in edges ---
    component srcEqI[nNodes][nEdges];
    component dstEqP[nNodes][nEdges];
    component srcEqP[nNodes][nEdges];
    component dstEqI[nNodes][nEdges];
    signal fwdMatch[nNodes][nEdges];
    signal revMatch[nNodes][nEdges];
    signal edgeMatchCount[nNodes];
    component edgeCountZero[nNodes];
    signal membershipCheck[nNodes];

    for (var i = 0; i < nNodes; i++) {
        var matchSum = 0;
        for (var e = 0; e < nEdges; e++) {
            // Forward: edge = (i, parent[i])
            srcEqI[i][e] = IsEqual();
            srcEqI[i][e].in[0] <== edges[e][0];
            srcEqI[i][e].in[1] <== i;

            dstEqP[i][e] = IsEqual();
            dstEqP[i][e].in[0] <== edges[e][1];
            dstEqP[i][e].in[1] <== parent[i];

            fwdMatch[i][e] <== srcEqI[i][e].out * dstEqP[i][e].out;

            // Reverse: edge = (parent[i], i)
            srcEqP[i][e] = IsEqual();
            srcEqP[i][e].in[0] <== edges[e][0];
            srcEqP[i][e].in[1] <== parent[i];

            dstEqI[i][e] = IsEqual();
            dstEqI[i][e].in[0] <== edges[e][1];
            dstEqI[i][e].in[1] <== i;

            revMatch[i][e] <== srcEqP[i][e].out * dstEqI[i][e].out;

            matchSum += fwdMatch[i][e] + revMatch[i][e];
        }
        edgeMatchCount[i] <== matchSum;

        // Non-root must have at least one matching edge
        edgeCountZero[i] = IsZero();
        edgeCountZero[i].in <== edgeMatchCount[i];
        // isZero * (1 - isRoot) must be 0
        membershipCheck[i] <== edgeCountZero[i].out * (1 - isRoot[i].out);
        membershipCheck[i] === 0;
    }
}

/// Verify a minimum spanning tree via spanning tree + cut property.
///
/// Extends Graph_SpanningTree with weight optimality: for each non-tree edge,
/// its weight must be >= the maximum tree-path edge weight between its endpoints.
///
/// Witness (in addition to spanning tree witness):
///   - treeEdgeMask[nEdges]: binary, 1 if edge is in tree
///   - maxPathWeight[nEdges]: for non-tree edges, max weight on tree path (0 for tree edges)
///
/// IMPORTANT: maxPathWeight is prover-supplied. Full soundness requires verifying
/// the max weight claim via tree path enumeration. This template trusts the claim.
///
/// O(nNodes × nEdges) for spanning tree + O(nEdges) for optimality.
template Graph_MST(nNodes, nEdges, nBits) {
    signal input edges[nEdges][2];
    signal input weights[nEdges];

    // Spanning tree witness
    signal input root;
    signal input parent[nNodes];
    signal input depth[nNodes];

    // MST-specific witness
    signal input treeEdgeMask[nEdges];
    signal input maxPathWeight[nEdges];

    signal output totalWeight;

    // 1. Verify spanning tree properties
    component tree = Graph_SpanningTree(nNodes, nEdges, nBits);
    for (var e = 0; e < nEdges; e++) {
        tree.edges[e][0] <== edges[e][0];
        tree.edges[e][1] <== edges[e][1];
    }
    tree.root <== root;
    for (var i = 0; i < nNodes; i++) {
        tree.parent[i] <== parent[i];
        tree.depth[i] <== depth[i];
    }

    // 2. treeEdgeMask is binary
    signal maskBinary[nEdges];
    for (var e = 0; e < nEdges; e++) {
        maskBinary[e] <== treeEdgeMask[e] * (treeEdgeMask[e] - 1);
        maskBinary[e] === 0;
    }

    // 3. treeEdgeMask sums to nNodes - 1
    signal maskCountSignal;
    var maskCount = 0;
    for (var e = 0; e < nEdges; e++) {
        maskCount += treeEdgeMask[e];
    }
    maskCountSignal <== maskCount;
    maskCountSignal === nNodes - 1;

    // 4. Consistency: each non-root node's parent edge is marked in treeEdgeMask
    //    For each non-root node i, the edge connecting i to parent[i] must have mask=1
    //    We scan edges to find which one matches and check its mask
    component isRootMST[nNodes];
    component mstSrcEqI[nNodes][nEdges];
    component mstDstEqP[nNodes][nEdges];
    component mstSrcEqP[nNodes][nEdges];
    component mstDstEqI[nNodes][nEdges];
    signal mstFwdMatch[nNodes][nEdges];
    signal mstRevMatch[nNodes][nEdges];
    signal mstEdgeMatch[nNodes][nEdges];
    signal mstMaskedMatch[nNodes][nEdges];
    signal mstMaskedSum[nNodes];
    component mstMaskedZero[nNodes];
    signal mstConsistencyCheck[nNodes];

    for (var i = 0; i < nNodes; i++) {
        isRootMST[i] = IsEqual();
        isRootMST[i].in[0] <== i;
        isRootMST[i].in[1] <== root;

        var maskedMatchSum = 0;
        for (var e = 0; e < nEdges; e++) {
            mstSrcEqI[i][e] = IsEqual();
            mstSrcEqI[i][e].in[0] <== edges[e][0];
            mstSrcEqI[i][e].in[1] <== i;

            mstDstEqP[i][e] = IsEqual();
            mstDstEqP[i][e].in[0] <== edges[e][1];
            mstDstEqP[i][e].in[1] <== parent[i];

            mstFwdMatch[i][e] <== mstSrcEqI[i][e].out * mstDstEqP[i][e].out;

            mstSrcEqP[i][e] = IsEqual();
            mstSrcEqP[i][e].in[0] <== edges[e][0];
            mstSrcEqP[i][e].in[1] <== parent[i];

            mstDstEqI[i][e] = IsEqual();
            mstDstEqI[i][e].in[0] <== edges[e][1];
            mstDstEqI[i][e].in[1] <== i;

            mstRevMatch[i][e] <== mstSrcEqP[i][e].out * mstDstEqI[i][e].out;

            // Does this edge connect i to parent[i]?
            mstEdgeMatch[i][e] <== mstFwdMatch[i][e] + mstRevMatch[i][e];
            // Is this edge also marked as a tree edge?
            mstMaskedMatch[i][e] <== mstEdgeMatch[i][e] * treeEdgeMask[e];
            maskedMatchSum += mstMaskedMatch[i][e];
        }
        mstMaskedSum[i] <== maskedMatchSum;

        // Non-root must have at least one masked match
        mstMaskedZero[i] = IsZero();
        mstMaskedZero[i].in <== mstMaskedSum[i];
        mstConsistencyCheck[i] <== mstMaskedZero[i].out * (1 - isRootMST[i].out);
        mstConsistencyCheck[i] === 0;
    }

    // 5. Compute total weight
    signal edgeWeightContrib[nEdges];
    var weightSum = 0;
    for (var e = 0; e < nEdges; e++) {
        edgeWeightContrib[e] <== weights[e] * treeEdgeMask[e];
        weightSum += edgeWeightContrib[e];
    }
    totalWeight <== weightSum;

    // 6. Cut property: for each non-tree edge, weight >= maxPathWeight
    //    (1 - treeEdgeMask[e]) * (weight[e] - maxPathWeight[e]) >= 0
    //    For tree edges, skip check (treeEdgeMask=1 makes it 0).
    //    For non-tree edges, check weight[e] >= maxPathWeight[e] via range check.
    signal cutSlack[nEdges];
    component cutSlackRange[nEdges];
    signal cutSlackBits[nEdges][nBits];
    signal cutCheck[nEdges];

    for (var e = 0; e < nEdges; e++) {
        cutSlack[e] <== weights[e] - maxPathWeight[e];
        // For non-tree edges: cutSlack must be non-negative
        // For tree edges: cutSlack can be anything (masked out)
        // Trick: range-check cutSlack + treeEdgeMask[e] * (1 << nBits)
        // When tree edge: adds 2^nBits which always fits in nBits+1 bits
        // When non-tree: just checks cutSlack fits in nBits bits (non-negative)
        // Simpler: provide maxPathWeight=0 for tree edges, then cutSlack = weight >= 0 always
        // The prover must set maxPathWeight[e]=0 for tree edges.
        // Just range-check cutSlack directly — it must be non-negative for all edges.
        cutSlackRange[e] = Num2Bits(nBits);
        cutSlackRange[e].in <== cutSlack[e];
        for (var b = 0; b < nBits; b++) {
            cutSlackBits[e][b] <== cutSlackRange[e].out[b];
        }
    }

    // 7. maxPathWeight for tree edges must be 0 (consistency)
    signal maxPathTreeCheck[nEdges];
    for (var e = 0; e < nEdges; e++) {
        maxPathTreeCheck[e] <== maxPathWeight[e] * treeEdgeMask[e];
        maxPathTreeCheck[e] === 0;
    }
}
