pragma circom 2.2.2;

/// Compute ceil(log2(n)). Returns number of bits needed to represent n.
function num_bits(n) {
    var bits = 0;
    var val = n;
    while (val > 0) {
        bits++;
        val = val >> 1;
    }
    return bits;
}

/// Bellman-Ford shortest path (witness computation).
/// Returns dist[nNodes] where dist[i] is the shortest distance from source to node i.
/// Uses nNodes-1 relaxation rounds. Unreachable nodes get dist = maxVal.
function bellman_ford(nNodes, nEdges, edges, edgeCosts, source, maxVal) {
    var dist[nNodes];

    // Initialize distances
    for (var i = 0; i < nNodes; i++) {
        dist[i] = maxVal;
    }
    dist[source] = 0;

    // Relax edges nNodes-1 times
    for (var round = 0; round < nNodes - 1; round++) {
        for (var e = 0; e < nEdges; e++) {
            var u = edges[e][0];
            var v = edges[e][1];
            var w = edgeCosts[e];
            if (dist[u] + w < dist[v]) {
                dist[v] = dist[u] + w;
            }
        }
    }

    return dist;
}
