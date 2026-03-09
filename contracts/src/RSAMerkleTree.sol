// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// @title RSAMerkleTree — Gas spike test for RSA-based Merkle tree
/// @notice Uses H(L,R) = L³ + 2·R³ mod N as the compression function.
///         All 2048-bit values are stored as 8 big-endian uint256 limbs.
contract RSAMerkleTree {
    uint256 public constant DEPTH = 20;
    uint256 public constant LIMBS = 8;

    /// @dev 2048-bit RSA modulus (big-endian: index 0 = most significant limb)
    uint256[8] public N;

    /// @dev Next available leaf index
    uint256 public nextIndex;

    /// @dev Left-side hashes at each tree level (incremental Merkle tree)
    uint256[8][DEPTH] internal filledSubtrees;

    /// @dev Current Merkle root
    uint256[8] internal _currentRoot;

    /// @notice Returns the full current Merkle root.
    function currentRoot() external view returns (uint256[8] memory) {
        return _currentRoot;
    }

    constructor(uint256[8] memory _N) {
        N = _N;
        // H(0,0) = 0³ + 2·0³ = 0, so zero hashes propagate.
        // filledSubtrees and currentRoot default to zero.
    }

    // ─── Public API ──────────────────────────────────────────────

    /// @notice Insert a commitment leaf and update the Merkle root.
    function deposit(uint256[8] calldata commitment) external {
        uint256 idx = nextIndex;
        require(idx < (1 << DEPTH), "Tree full");

        // Reject zero commitment
        {
            bool allZero = true;
            for (uint256 i = 0; i < LIMBS; i++) {
                if (commitment[i] != 0) { allZero = false; break; }
            }
            require(!allZero, "Zero commitment");
        }

        // Load modulus into memory once
        uint256[8] memory mod_ = N;
        uint256[8] memory zero;
        uint256[8] memory current;
        for (uint256 i = 0; i < LIMBS; i++) current[i] = commitment[i];

        for (uint256 level = 0; level < DEPTH; level++) {
            if (idx & 1 == 0) {
                // New node is left child — store it, hash with zero right sibling
                filledSubtrees[level] = current;
                current = _rsaMerkleHash(current, zero, mod_);
            } else {
                // New node is right child — hash stored left sibling with it
                current = _rsaMerkleHash(filledSubtrees[level], current, mod_);
            }
            idx >>= 1;
        }

        _currentRoot = current;
        nextIndex++;
    }

    /// @notice Compute H(L, R) = L³ + 2·R³ mod N (exposed for benchmarking)
    function rsaMerkleHash(uint256[8] calldata L, uint256[8] calldata R)
        external view returns (uint256[8] memory)
    {
        uint256[8] memory mod_ = N;
        uint256[8] memory mL;
        uint256[8] memory mR;
        for (uint256 i = 0; i < LIMBS; i++) {
            mL[i] = L[i];
            mR[i] = R[i];
        }
        return _rsaMerkleHash(mL, mR, mod_);
    }

    /// @notice Compute base³ mod N (exposed for benchmarking)
    function cube(uint256[8] calldata base) external view returns (uint256[8] memory) {
        uint256[8] memory mod_ = N;
        uint256[8] memory mBase;
        for (uint256 i = 0; i < LIMBS; i++) mBase[i] = base[i];
        return _cube(mBase, mod_);
    }

    // ─── Core: compression function ──────────────────────────────

    /// @dev H(L, R) = L³ + 2·R³ mod N
    function _rsaMerkleHash(
        uint256[8] memory L,
        uint256[8] memory R,
        uint256[8] memory mod_
    ) internal view returns (uint256[8] memory) {
        uint256[8] memory L3 = _cube(L, mod_);
        uint256[8] memory R3 = _cube(R, mod_);
        // 2·R³ = R³ + R³
        uint256[8] memory twoR3 = _addMod(R3, R3, mod_);
        return _addMod(L3, twoR3, mod_);
    }

    // ─── Modexp precompile ───────────────────────────────────────

    /// @dev Computes base³ mod N via the modexp precompile (address 0x05).
    ///      Uses exp_length=32 (padded) for word alignment. Gas cost is identical
    ///      to exp_length=1 because iteration_count depends on bit_length(3)=2, not padding.
    function _cube(uint256[8] memory base, uint256[8] memory mod_)
        internal view returns (uint256[8] memory result)
    {
        // Input layout (all word-aligned):
        //   [0x000] base_length  = 256 (0x100)
        //   [0x020] exp_length   = 32  (0x20)
        //   [0x040] mod_length   = 256 (0x100)
        //   [0x060] base         (256 bytes = 8 words)
        //   [0x160] exponent     (32 bytes, value = 3)
        //   [0x180] modulus      (256 bytes = 8 words)
        //   Total input: 0x280 = 640 bytes
        //   Output: 256 bytes written to result
        assembly {
            let ptr := mload(0x40)

            // Lengths
            mstore(ptr, 0x100)
            mstore(add(ptr, 0x20), 0x20)
            mstore(add(ptr, 0x40), 0x100)

            // Base (8 limbs)
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                mstore(
                    add(add(ptr, 0x60), mul(i, 0x20)),
                    mload(add(base, mul(i, 0x20)))
                )
            }

            // Exponent = 3
            mstore(add(ptr, 0x160), 3)

            // Modulus (8 limbs)
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                mstore(
                    add(add(ptr, 0x180), mul(i, 0x20)),
                    mload(add(mod_, mul(i, 0x20)))
                )
            }

            // staticcall modexp precompile; write output to ptr (reuse buffer)
            let success := staticcall(gas(), 0x05, ptr, 0x280, ptr, 0x100)
            if iszero(success) { revert(0, 0) }

            // Copy 256-byte result into return value
            for { let i := 0 } lt(i, 8) { i := add(i, 1) } {
                mstore(
                    add(result, mul(i, 0x20)),
                    mload(add(ptr, mul(i, 0x20)))
                )
            }
        }
    }

    // ─── 2048-bit arithmetic ─────────────────────────────────────

    /// @dev (a + b) mod N, where a, b ∈ [0, N)
    function _addMod(
        uint256[8] memory a,
        uint256[8] memory b,
        uint256[8] memory mod_
    ) internal pure returns (uint256[8] memory result) {
        uint256 carry;

        // Add with carry, processing from LSB (index 7) to MSB (index 0)
        unchecked {
            for (uint256 i = 8; i > 0;) {
                --i;
                uint256 ai = a[i];
                uint256 sum = ai + b[i];
                uint256 c1 = sum < ai ? 1 : 0;
                uint256 sum2 = sum + carry;
                uint256 c2 = sum2 < sum ? 1 : 0;
                result[i] = sum2;
                carry = c1 + c2;
            }
        }

        // Reduce: if carry or result >= mod_, subtract mod_
        if (carry > 0 || _gte(result, mod_)) {
            result = _sub(result, mod_);
        }
    }

    /// @dev a >= b (big-endian comparison)
    function _gte(uint256[8] memory a, uint256[8] memory b)
        internal pure returns (bool)
    {
        for (uint256 i = 0; i < 8; i++) {
            if (a[i] > b[i]) return true;
            if (a[i] < b[i]) return false;
        }
        return true; // equal
    }

    /// @dev a - b, assuming a >= b (big-endian, unchecked)
    function _sub(uint256[8] memory a, uint256[8] memory b)
        internal pure returns (uint256[8] memory result)
    {
        unchecked {
            uint256 borrow;
            for (uint256 i = 8; i > 0;) {
                --i;
                uint256 ai = a[i];
                uint256 bi = b[i] + borrow;
                // Overflow of b[i]+borrow means b[i]=max and borrow=1 → must borrow again
                borrow = (bi < b[i] || ai < bi) ? 1 : 0;
                result[i] = ai - bi;
            }
        }
    }
}
