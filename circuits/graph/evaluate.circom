pragma circom 2.2.2;

include "core/comparators.circom";
include "graph/lookup.circom";

/// Linear expression over edge endpoints.
/// For each edge (u,v): out[i] = Σ(coeff[p] × srcProp[p]) + Σ(coeff[nNodeProps+p] × dstProp[p]) + constant
/// 2×nEdges LookupRow + 2×nEdges×nNodeProps quadratic constraints.
template Graph_EvalLinear(nNodes, nEdges, nNodeProps) {
    signal input edges[nEdges][2];
    signal input nodeProps[nNodes][nNodeProps];
    signal input coeff[2 * nNodeProps];
    signal input constant;
    signal output out[nEdges];

    component srcRow[nEdges];
    component dstRow[nEdges];
    signal srcTerms[nEdges][nNodeProps];
    signal dstTerms[nEdges][nNodeProps];

    for (var i = 0; i < nEdges; i++) {
        srcRow[i] = LookupRow(nNodes, nNodeProps);
        srcRow[i].sel <== edges[i][0];
        for (var j = 0; j < nNodes; j++) {
            for (var p = 0; p < nNodeProps; p++) {
                srcRow[i].props[j][p] <== nodeProps[j][p];
            }
        }

        dstRow[i] = LookupRow(nNodes, nNodeProps);
        dstRow[i].sel <== edges[i][1];
        for (var j = 0; j < nNodes; j++) {
            for (var p = 0; p < nNodeProps; p++) {
                dstRow[i].props[j][p] <== nodeProps[j][p];
            }
        }

        var sum = constant;
        for (var p = 0; p < nNodeProps; p++) {
            srcTerms[i][p] <== coeff[p] * srcRow[i].out[p];
            sum += srcTerms[i][p];
            dstTerms[i][p] <== coeff[nNodeProps + p] * dstRow[i].out[p];
            sum += dstTerms[i][p];
        }
        out[i] <== sum;
    }
}

/// Quadratic form over edge endpoints.
/// For each edge (u,v): out[i] = Σ Q[p][q] × srcProp[p] × dstProp[q]
///                              + Σ linCoeff[p] × srcProp[p]
///                              + Σ linCoeff[nNodeProps+p] × dstProp[p]
///                              + constant
/// 2×nEdges LookupRow + nEdges×nNodeProps² cross-products + 2×nEdges×nNodeProps linear.
template Graph_EvalQuadratic(nNodes, nEdges, nNodeProps) {
    signal input edges[nEdges][2];
    signal input nodeProps[nNodes][nNodeProps];
    signal input Q[nNodeProps][nNodeProps];
    signal input linCoeff[2 * nNodeProps];
    signal input constant;
    signal output out[nEdges];

    component srcRow[nEdges];
    component dstRow[nEdges];
    signal crossProducts[nEdges][nNodeProps][nNodeProps];
    signal weightedCross[nEdges][nNodeProps][nNodeProps];
    signal srcLinTerms[nEdges][nNodeProps];
    signal dstLinTerms[nEdges][nNodeProps];

    for (var i = 0; i < nEdges; i++) {
        srcRow[i] = LookupRow(nNodes, nNodeProps);
        srcRow[i].sel <== edges[i][0];
        for (var j = 0; j < nNodes; j++) {
            for (var p = 0; p < nNodeProps; p++) {
                srcRow[i].props[j][p] <== nodeProps[j][p];
            }
        }

        dstRow[i] = LookupRow(nNodes, nNodeProps);
        dstRow[i].sel <== edges[i][1];
        for (var j = 0; j < nNodes; j++) {
            for (var p = 0; p < nNodeProps; p++) {
                dstRow[i].props[j][p] <== nodeProps[j][p];
            }
        }

        var sum = constant;

        // Cross-products: Q[p][q] × srcProp[p] × dstProp[q]
        for (var p = 0; p < nNodeProps; p++) {
            for (var q = 0; q < nNodeProps; q++) {
                crossProducts[i][p][q] <== srcRow[i].out[p] * dstRow[i].out[q];
                weightedCross[i][p][q] <== Q[p][q] * crossProducts[i][p][q];
                sum += weightedCross[i][p][q];
            }
        }

        // Linear terms
        for (var p = 0; p < nNodeProps; p++) {
            srcLinTerms[i][p] <== linCoeff[p] * srcRow[i].out[p];
            sum += srcLinTerms[i][p];
            dstLinTerms[i][p] <== linCoeff[nNodeProps + p] * dstRow[i].out[p];
            sum += dstLinTerms[i][p];
        }

        out[i] <== sum;
    }
}

/// Symmetric-Q quadratic form over edge endpoints.
/// Exploits Q[p][q] == Q[q][p] to reduce cross-product constraints by ~25%.
///
/// For each edge (u,v): out[i] = Σ Q[p][p] × srcProp[p] × dstProp[p]              (diagonal)
///                              + Σ_{p<q} Q[p][q] × (src[p]×dst[q] + src[q]×dst[p]) (upper triangle)
///                              + linear terms + constant
///
/// Cross-product constraints per edge:
///   Full:      2×nNodeProps²
///   Symmetric: 2×nNodeProps + 3×nNodeProps×(nNodeProps-1)/2
///   Savings:   nNodeProps×(nNodeProps-1)/2 constraints per edge
///
/// IMPORTANT: Caller must ensure Q is symmetric. If Q is not symmetric,
/// only the upper triangle (including diagonal) is used.
template Graph_EvalQuadraticSym(nNodes, nEdges, nNodeProps) {
    var nPairs = nNodeProps * (nNodeProps - 1) / 2;

    signal input edges[nEdges][2];
    signal input nodeProps[nNodes][nNodeProps];
    signal input Q[nNodeProps][nNodeProps];
    signal input linCoeff[2 * nNodeProps];
    signal input constant;
    signal output out[nEdges];

    component srcRow[nEdges];
    component dstRow[nEdges];

    // Diagonal: src[p] * dst[p], then Q[p][p] * that
    signal diagCross[nEdges][nNodeProps];
    signal diagWeighted[nEdges][nNodeProps];

    // Upper triangle pairs (p < q): src[p]*dst[q], src[q]*dst[p], Q[p][q]*(sum)
    signal pairCrossA[nEdges][nPairs];
    signal pairCrossB[nEdges][nPairs];
    signal pairWeighted[nEdges][nPairs];

    // Linear terms
    signal srcLinTerms[nEdges][nNodeProps];
    signal dstLinTerms[nEdges][nNodeProps];

    for (var i = 0; i < nEdges; i++) {
        srcRow[i] = LookupRow(nNodes, nNodeProps);
        srcRow[i].sel <== edges[i][0];
        for (var j = 0; j < nNodes; j++) {
            for (var p = 0; p < nNodeProps; p++) {
                srcRow[i].props[j][p] <== nodeProps[j][p];
            }
        }

        dstRow[i] = LookupRow(nNodes, nNodeProps);
        dstRow[i].sel <== edges[i][1];
        for (var j = 0; j < nNodes; j++) {
            for (var p = 0; p < nNodeProps; p++) {
                dstRow[i].props[j][p] <== nodeProps[j][p];
            }
        }

        var sum = constant;

        // Diagonal terms: Q[p][p] × src[p] × dst[p]
        for (var p = 0; p < nNodeProps; p++) {
            diagCross[i][p] <== srcRow[i].out[p] * dstRow[i].out[p];
            diagWeighted[i][p] <== Q[p][p] * diagCross[i][p];
            sum += diagWeighted[i][p];
        }

        // Upper triangle: Q[p][q] × (src[p]×dst[q] + src[q]×dst[p]) for p < q
        var idx = 0;
        for (var p = 0; p < nNodeProps; p++) {
            for (var q = p + 1; q < nNodeProps; q++) {
                pairCrossA[i][idx] <== srcRow[i].out[p] * dstRow[i].out[q];
                pairCrossB[i][idx] <== srcRow[i].out[q] * dstRow[i].out[p];
                pairWeighted[i][idx] <== Q[p][q] * (pairCrossA[i][idx] + pairCrossB[i][idx]);
                sum += pairWeighted[i][idx];
                idx++;
            }
        }

        // Linear terms
        for (var p = 0; p < nNodeProps; p++) {
            srcLinTerms[i][p] <== linCoeff[p] * srcRow[i].out[p];
            sum += srcLinTerms[i][p];
            dstLinTerms[i][p] <== linCoeff[nNodeProps + p] * dstRow[i].out[p];
            sum += dstLinTerms[i][p];
        }

        out[i] <== sum;
    }
}

/// Evaluate and compare on edge properties.
/// comparisonType: 0=equal, 1=less-than, 2=greater-than
/// For each edge, evaluates: edgeProps[i][propIdx1] {op} edgeProps[i][propIdx2]
template Graph_EvalEdgeExpr(nEdges, nEdgeProps, nBits, comparisonType) {
    signal input edgeProps[nEdges][nEdgeProps];
    signal input propIdx1;
    signal input propIdx2;
    signal output results[nEdges];

    component lhsLookup[nEdges];
    component rhsLookup[nEdges];

    for (var i = 0; i < nEdges; i++) {
        lhsLookup[i] = Lookup(nEdgeProps);
        lhsLookup[i].sel <== propIdx1;
        for (var p = 0; p < nEdgeProps; p++) {
            lhsLookup[i].in[p] <== edgeProps[i][p];
        }

        rhsLookup[i] = Lookup(nEdgeProps);
        rhsLookup[i].sel <== propIdx2;
        for (var p = 0; p < nEdgeProps; p++) {
            rhsLookup[i].in[p] <== edgeProps[i][p];
        }
    }

    if (comparisonType == 0) {
        // Equal
        component eq[nEdges];
        for (var i = 0; i < nEdges; i++) {
            eq[i] = IsEqual();
            eq[i].in[0] <== lhsLookup[i].out;
            eq[i].in[1] <== rhsLookup[i].out;
            results[i] <== eq[i].out;
        }
    }
    if (comparisonType == 1) {
        // Less-than
        component lt[nEdges];
        for (var i = 0; i < nEdges; i++) {
            lt[i] = LessThan(nBits);
            lt[i].in[0] <== lhsLookup[i].out;
            lt[i].in[1] <== rhsLookup[i].out;
            results[i] <== lt[i].out;
        }
    }
    if (comparisonType == 2) {
        // Greater-than (swap operands of LessThan)
        component gt[nEdges];
        for (var i = 0; i < nEdges; i++) {
            gt[i] = LessThan(nBits);
            gt[i].in[0] <== rhsLookup[i].out;
            gt[i].in[1] <== lhsLookup[i].out;
            results[i] <== gt[i].out;
        }
    }
}
