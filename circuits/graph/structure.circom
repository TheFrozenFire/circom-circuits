pragma circom 2.2.2;

include "core/comparators.circom";
include "graph/lookup.circom";

/// Verify all edge endpoints are in [0, nNodes) with no self-loops.
/// 2×nEdges LessThan + nEdges IsEqual.
template Graph_ValidEdges(nNodes, nEdges, nBits) {
    signal input edges[nEdges][2];

    component ltSrc[nEdges];
    component ltDst[nEdges];
    component noSelfLoop[nEdges];

    for (var i = 0; i < nEdges; i++) {
        // src < nNodes
        ltSrc[i] = LessThan(nBits);
        ltSrc[i].in[0] <== edges[i][0];
        ltSrc[i].in[1] <== nNodes;
        ltSrc[i].out === 1;

        // dst < nNodes
        ltDst[i] = LessThan(nBits);
        ltDst[i].in[0] <== edges[i][1];
        ltDst[i].in[1] <== nNodes;
        ltDst[i].out === 1;

        // src != dst
        noSelfLoop[i] = IsEqual();
        noSelfLoop[i].in[0] <== edges[i][0];
        noSelfLoop[i].in[1] <== edges[i][1];
        noSelfLoop[i].out === 0;
    }
}

/// Verify DAG via topological ordering certificate.
/// Witness: levels[nNodes] assigns a topological level to each node.
/// Checks: levels in [0, nNodes), and for every edge (u,v): levels[u] < levels[v].
/// O(nEdges × nNodes) dominated by Lookup.
template Graph_DAG(nNodes, nEdges, nBits) {
    signal input edges[nEdges][2];
    signal input levels[nNodes];

    // Range-check all levels: 0 <= levels[i] < nNodes
    component levelRange[nNodes];
    for (var i = 0; i < nNodes; i++) {
        levelRange[i] = LessThan(nBits);
        levelRange[i].in[0] <== levels[i];
        levelRange[i].in[1] <== nNodes;
        levelRange[i].out === 1;
    }

    // For each edge, lookup src and dst levels and check src_level < dst_level
    component srcLevel[nEdges];
    component dstLevel[nEdges];
    component levelLt[nEdges];

    for (var i = 0; i < nEdges; i++) {
        srcLevel[i] = Lookup(nNodes);
        srcLevel[i].sel <== edges[i][0];
        for (var j = 0; j < nNodes; j++) {
            srcLevel[i].in[j] <== levels[j];
        }

        dstLevel[i] = Lookup(nNodes);
        dstLevel[i].sel <== edges[i][1];
        for (var j = 0; j < nNodes; j++) {
            dstLevel[i].in[j] <== levels[j];
        }

        levelLt[i] = LessThan(nBits);
        levelLt[i].in[0] <== srcLevel[i].out;
        levelLt[i].in[1] <== dstLevel[i].out;
        levelLt[i].out === 1;
    }
}

/// Verify that specified nodes have out-degree 0 (are sinks).
/// For each sink, check no edge has it as source.
/// O(nSinks × nEdges) IsEqual checks.
template Graph_SinkCheck(nNodes, nEdges, nSinks) {
    signal input edges[nEdges][2];
    signal input sinks[nSinks];

    component isSrc[nSinks][nEdges];
    signal sinkMatchCount[nSinks];

    for (var i = 0; i < nSinks; i++) {
        var matchCount = 0;
        for (var j = 0; j < nEdges; j++) {
            isSrc[i][j] = IsEqual();
            isSrc[i][j].in[0] <== sinks[i];
            isSrc[i][j].in[1] <== edges[j][0];
            matchCount += isSrc[i][j].out;
        }
        // matchCount must be 0 — no edge has this sink as source
        sinkMatchCount[i] <== matchCount;
        sinkMatchCount[i] === 0;
    }
}

/// Combined well-formedness check: valid edges + DAG + sink verification.
template Graph_WellFormedDAG(nNodes, nEdges, nSinks, nBits) {
    signal input edges[nEdges][2];
    signal input levels[nNodes];
    signal input sinks[nSinks];

    component validEdges = Graph_ValidEdges(nNodes, nEdges, nBits);
    for (var i = 0; i < nEdges; i++) {
        validEdges.edges[i][0] <== edges[i][0];
        validEdges.edges[i][1] <== edges[i][1];
    }

    component dag = Graph_DAG(nNodes, nEdges, nBits);
    for (var i = 0; i < nEdges; i++) {
        dag.edges[i][0] <== edges[i][0];
        dag.edges[i][1] <== edges[i][1];
    }
    for (var i = 0; i < nNodes; i++) {
        dag.levels[i] <== levels[i];
    }

    component sinkCheck = Graph_SinkCheck(nNodes, nEdges, nSinks);
    for (var i = 0; i < nEdges; i++) {
        sinkCheck.edges[i][0] <== edges[i][0];
        sinkCheck.edges[i][1] <== edges[i][1];
    }
    for (var i = 0; i < nSinks; i++) {
        sinkCheck.sinks[i] <== sinks[i];
    }
}
