// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

/// @title RSAMerkleTree1024 — Gas spike test for 1024-bit RSA Merkle tree
/// @notice Uses H(L,R) = L³ + 2·R³ mod N as the compression function.
///         All 1024-bit values are stored as 4 big-endian uint256 limbs.
contract RSAMerkleTree1024 {
    uint256 public constant DEPTH = 20;
    uint256 public constant LIMBS = 4;

    /// @dev 1024-bit RSA modulus (big-endian: index 0 = most significant limb)
    uint256[4] public N;

    /// @dev Next available leaf index
    uint256 public nextIndex;

    /// @dev Left-side hashes at each tree level (incremental Merkle tree)
    uint256[4][DEPTH] internal filledSubtrees;

    /// @dev Current Merkle root
    uint256[4] internal _currentRoot;

    /// @notice Returns the full current Merkle root.
    function currentRoot() external view returns (uint256[4] memory) {
        return _currentRoot;
    }

    constructor(uint256[4] memory _N) {
        N = _N;
    }

    // ─── Public API ──────────────────────────────────────────────

    /// @notice Insert a commitment leaf and update the Merkle root.
    function deposit(uint256[4] calldata commitment) external {
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
        uint256[4] memory mod_ = N;
        uint256[4] memory zero;
        uint256[4] memory current;
        for (uint256 i = 0; i < LIMBS; i++) current[i] = commitment[i];

        for (uint256 level = 0; level < DEPTH; level++) {
            if (idx & 1 == 0) {
                filledSubtrees[level] = current;
                current = _rsaMerkleHash(current, zero, mod_);
            } else {
                current = _rsaMerkleHash(filledSubtrees[level], current, mod_);
            }
            idx >>= 1;
        }

        _currentRoot = current;
        nextIndex++;
    }

    /// @notice Compute H(L, R) = L³ + 2·R³ mod N (exposed for benchmarking)
    function rsaMerkleHash(uint256[4] calldata L, uint256[4] calldata R)
        external view returns (uint256[4] memory)
    {
        uint256[4] memory mod_ = N;
        uint256[4] memory mL;
        uint256[4] memory mR;
        for (uint256 i = 0; i < LIMBS; i++) {
            mL[i] = L[i];
            mR[i] = R[i];
        }
        return _rsaMerkleHash(mL, mR, mod_);
    }

    /// @notice Compute base³ mod N (exposed for benchmarking)
    function cube(uint256[4] calldata base) external view returns (uint256[4] memory) {
        uint256[4] memory mod_ = N;
        uint256[4] memory mBase;
        for (uint256 i = 0; i < LIMBS; i++) mBase[i] = base[i];
        return _cube(mBase, mod_);
    }

    // ─── Core: compression function ──────────────────────────────

    /// @dev H(L, R) = L³ + 2·R³ mod N
    function _rsaMerkleHash(
        uint256[4] memory L,
        uint256[4] memory R,
        uint256[4] memory mod_
    ) internal view returns (uint256[4] memory) {
        uint256[4] memory L3 = _cube(L, mod_);
        uint256[4] memory R3 = _cube(R, mod_);
        uint256[4] memory twoR3 = _addMod(R3, R3, mod_);
        return _addMod(L3, twoR3, mod_);
    }

    // ─── Modexp precompile ───────────────────────────────────────

    /// @dev Computes base³ mod N via the modexp precompile (address 0x05).
    ///      1024-bit base/modulus = 128 bytes = 4 limbs.
    function _cube(uint256[4] memory base, uint256[4] memory mod_)
        internal view returns (uint256[4] memory result)
    {
        // Input layout (all word-aligned):
        //   [0x000] base_length  = 128 (0x80)
        //   [0x020] exp_length   = 32  (0x20)
        //   [0x040] mod_length   = 128 (0x80)
        //   [0x060] base         (128 bytes = 4 words)
        //   [0x0E0] exponent     (32 bytes, value = 3)
        //   [0x100] modulus      (128 bytes = 4 words)
        //   Total input: 0x180 = 384 bytes
        //   Output: 128 bytes
        assembly {
            let ptr := mload(0x40)

            // Lengths
            mstore(ptr, 0x80)
            mstore(add(ptr, 0x20), 0x20)
            mstore(add(ptr, 0x40), 0x80)

            // Base (4 limbs)
            for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                mstore(
                    add(add(ptr, 0x60), mul(i, 0x20)),
                    mload(add(base, mul(i, 0x20)))
                )
            }

            // Exponent = 3
            mstore(add(ptr, 0x0E0), 3)

            // Modulus (4 limbs)
            for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                mstore(
                    add(add(ptr, 0x100), mul(i, 0x20)),
                    mload(add(mod_, mul(i, 0x20)))
                )
            }

            // staticcall modexp precompile; write 128-byte output to ptr
            let success := staticcall(gas(), 0x05, ptr, 0x180, ptr, 0x80)
            if iszero(success) { revert(0, 0) }

            // Copy result
            for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                mstore(
                    add(result, mul(i, 0x20)),
                    mload(add(ptr, mul(i, 0x20)))
                )
            }
        }
    }

    // ─── 1024-bit arithmetic ─────────────────────────────────────

    /// @dev (a + b) mod N, where a, b ∈ [0, N)
    function _addMod(
        uint256[4] memory a,
        uint256[4] memory b,
        uint256[4] memory mod_
    ) internal pure returns (uint256[4] memory result) {
        uint256 carry;

        unchecked {
            for (uint256 i = 4; i > 0;) {
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

        if (carry > 0 || _gte(result, mod_)) {
            result = _sub(result, mod_);
        }
    }

    /// @dev a >= b (big-endian comparison)
    function _gte(uint256[4] memory a, uint256[4] memory b)
        internal pure returns (bool)
    {
        for (uint256 i = 0; i < 4; i++) {
            if (a[i] > b[i]) return true;
            if (a[i] < b[i]) return false;
        }
        return true;
    }

    /// @dev a - b, assuming a >= b (big-endian, unchecked)
    function _sub(uint256[4] memory a, uint256[4] memory b)
        internal pure returns (uint256[4] memory result)
    {
        unchecked {
            uint256 borrow;
            for (uint256 i = 4; i > 0;) {
                --i;
                uint256 ai = a[i];
                uint256 bi = b[i] + borrow;
                borrow = (bi < b[i] || ai < bi) ? 1 : 0;
                result[i] = ai - bi;
            }
        }
    }
}
