import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { Poseidon } from "@iden3/js-crypto";

function hash2(left: bigint, right: bigint): bigint {
    return Poseidon.hash([left, right]);
}

describe_circuit("MerkleTreeInclusionProof", {
    merkle: { path: "hash/merkle.circom", template: "MerkleTreeInclusionProof", params: [3] },
}, (calculators) => {
    it("computes correct root for known tree", async () => {
        // Build a simple 3-level tree (8 leaves)
        const leaves = [1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n];
        const l1: bigint[] = [];
        for (let i = 0; i < 4; i++) {
            l1.push(hash2(leaves[i * 2], leaves[i * 2 + 1]));
        }
        const l2 = [hash2(l1[0], l1[1]), hash2(l1[2], l1[3])];
        const root = hash2(l2[0], l2[1]);

        // Prove inclusion of leaf 0 (path = left, left, left = [0,0,0])
        const w = await calculators.merkle.calculate({
            leaf: leaves[0],
            pathIndices: [0, 0, 0],
            siblings: [leaves[1], l1[1], l2[1]],
        });
        assert.equal(w.value("main.out"), root);
    });

    it("proves inclusion of a right-side leaf", async () => {
        const leaves = [1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n];
        const l1: bigint[] = [];
        for (let i = 0; i < 4; i++) {
            l1.push(hash2(leaves[i * 2], leaves[i * 2 + 1]));
        }
        const l2 = [hash2(l1[0], l1[1]), hash2(l1[2], l1[3])];
        const root = hash2(l2[0], l2[1]);

        // Prove inclusion of leaf 7 (path = right, right, right = [1,1,1])
        const w = await calculators.merkle.calculate({
            leaf: leaves[7],
            pathIndices: [1, 1, 1],
            siblings: [leaves[6], l1[2], l2[0]],
        });
        assert.equal(w.value("main.out"), root);
    });

    it("rejects wrong sibling", async () => {
        const leaves = [1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n];
        const l1: bigint[] = [];
        for (let i = 0; i < 4; i++) {
            l1.push(hash2(leaves[i * 2], leaves[i * 2 + 1]));
        }
        const l2 = [hash2(l1[0], l1[1]), hash2(l1[2], l1[3])];
        const root = hash2(l2[0], l2[1]);

        // Use wrong sibling — root will differ
        const w = await calculators.merkle.calculate({
            leaf: leaves[0],
            pathIndices: [0, 0, 0],
            siblings: [99n, l1[1], l2[1]], // wrong sibling
        });
        assert.notEqual(w.value("main.out"), root);
    });

    it("rejects non-binary pathIndex", async () => {
        try {
            await calculators.merkle.calculate({
                leaf: 1,
                pathIndices: [2, 0, 0], // invalid: not 0 or 1
                siblings: [2, 3, 4],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });
});
