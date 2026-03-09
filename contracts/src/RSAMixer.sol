// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

interface IGroth16Verifier {
    function verifyProof(
        uint[2] calldata _pA,
        uint[2][2] calldata _pB,
        uint[2] calldata _pC,
        uint[66] calldata _pubSignals
    ) external view returns (bool);
}

/// @title RSAMixer — 1024-bit RSA Merkle mixer with Groth16 withdrawal proofs
/// @notice Deposits commitments into an incremental RSA Merkle tree (depth 4).
///         Withdrawals require a Groth16 proof of leaf knowledge + Merkle inclusion.
///         All 1024-bit values use big-endian uint256[4] representation.
///         Circuit uses n=32, k=32 (32-bit limbs × 32 = 1024-bit).
contract RSAMixer {
    uint256 public constant DEPTH = 4;
    uint256 public constant LIMBS = 4;

    /// @dev 1024-bit RSA modulus (big-endian: index 0 = most significant limb)
    uint256[4] public N;

    /// @dev Next available leaf index
    uint256 public nextIndex;

    /// @dev Left-side hashes at each tree level (incremental Merkle tree)
    uint256[4][DEPTH] internal filledSubtrees;

    /// @dev Current Merkle root
    uint256[4] internal _currentRoot;

    /// @dev Historical roots: keccak256(root) → known
    mapping(uint256 => bool) public knownRoots;

    /// @dev Spent nullifier hashes
    mapping(uint256 => bool) public nullifierHashes;

    /// @dev Groth16 verifier contract
    address public verifier;

    event Deposit(uint256[4] commitment, uint256 leafIndex, uint256[4] root);
    event Withdrawal(address recipient, uint256 nullifierHash);

    constructor(uint256[4] memory _N, address _verifier) {
        N = _N;
        verifier = _verifier;
        knownRoots[_rootKey(_currentRoot)] = true;
    }

    function currentRoot() external view returns (uint256[4] memory) {
        return _currentRoot;
    }

    // ─── Deposit ───────────────────────────────────────────────

    function deposit(uint256[4] calldata commitment) external {
        uint256 idx = nextIndex;
        require(idx < (1 << DEPTH), "Tree full");

        {
            bool allZero = true;
            for (uint256 i = 0; i < LIMBS; i++) {
                if (commitment[i] != 0) { allZero = false; break; }
            }
            require(!allZero, "Zero commitment");
        }

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
        knownRoots[_rootKey(current)] = true;
        nextIndex++;

        emit Deposit(commitment, nextIndex - 1, current);
    }

    // ─── Withdraw ──────────────────────────────────────────────

    /// @notice Withdraw by providing a valid Groth16 proof.
    /// @dev Public signals layout (66 total, n=32, k=32):
    ///   [0..31]  root (32 LE 32-bit limbs)
    ///   [32]     nullifierHash
    ///   [33..64] N (32 LE 32-bit limbs)
    ///   [65]     recipient
    function withdraw(
        uint[2] calldata pA,
        uint[2][2] calldata pB,
        uint[2] calldata pC,
        uint[66] calldata pubSignals
    ) external {
        // 1. Pack root limbs → uint256[4] BE
        uint256[4] memory root = _packLimbs32(pubSignals, 0);

        // 2. Verify root is known
        require(knownRoots[_rootKey(root)], "Unknown root");

        // 3. Check nullifier not spent
        uint256 nullifierHash = pubSignals[32];
        require(!nullifierHashes[nullifierHash], "Already spent");

        // 4. Pack N limbs → uint256[4] BE, verify matches stored N
        uint256[4] memory proofN = _packLimbs32(pubSignals, 33);
        for (uint256 i = 0; i < LIMBS; i++) {
            require(proofN[i] == N[i], "N mismatch");
        }

        // 5. Verify Groth16 proof
        require(
            IGroth16Verifier(verifier).verifyProof(pA, pB, pC, pubSignals),
            "Invalid proof"
        );

        // 6. Mark nullifier spent
        nullifierHashes[nullifierHash] = true;

        // 7. Emit event
        address recipient = address(uint160(pubSignals[65]));
        emit Withdrawal(recipient, nullifierHash);
    }

    // ─── Core: compression function ────────────────────────────

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

    // ─── Modexp precompile ─────────────────────────────────────

    /// @dev Computes base³ mod N via the modexp precompile (address 0x05).
    function _cube(uint256[4] memory base, uint256[4] memory mod_)
        internal view returns (uint256[4] memory result)
    {
        assembly {
            let ptr := mload(0x40)

            mstore(ptr, 0x80)
            mstore(add(ptr, 0x20), 0x20)
            mstore(add(ptr, 0x40), 0x80)

            for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                mstore(
                    add(add(ptr, 0x60), mul(i, 0x20)),
                    mload(add(base, mul(i, 0x20)))
                )
            }

            mstore(add(ptr, 0x0E0), 3)

            for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                mstore(
                    add(add(ptr, 0x100), mul(i, 0x20)),
                    mload(add(mod_, mul(i, 0x20)))
                )
            }

            let success := staticcall(gas(), 0x05, ptr, 0x180, ptr, 0x80)
            if iszero(success) { revert(0, 0) }

            for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
                mstore(
                    add(result, mul(i, 0x20)),
                    mload(add(ptr, mul(i, 0x20)))
                )
            }
        }
    }

    // ─── 1024-bit arithmetic ───────────────────────────────────

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

    // ─── Limb packing ──────────────────────────────────────────

    /// @dev Pack 32 LE 32-bit limbs from pubSignals[offset..offset+31]
    ///      into 4 BE uint256 words. Each uint256 word = 8 × 32-bit limbs.
    ///
    ///   word[3] = limb[0] | (limb[1]<<32) | ... | (limb[7]<<224)
    ///   word[2] = limb[8] | (limb[9]<<32) | ... | (limb[15]<<224)
    ///   word[1] = limb[16] | (limb[17]<<32) | ... | (limb[23]<<224)
    ///   word[0] = limb[24] | (limb[25]<<32) | ... | (limb[31]<<224)
    function _packLimbs32(
        uint[66] calldata pubSignals,
        uint256 offset
    ) internal pure returns (uint256[4] memory result) {
        for (uint256 w = 0; w < 4; w++) {
            uint256 wordIdx = 3 - w; // BE: word[3] gets the lowest limbs
            uint256 val;
            for (uint256 j = 0; j < 8; j++) {
                val |= pubSignals[offset + w * 8 + j] << (j * 32);
            }
            result[wordIdx] = val;
        }
    }

    /// @dev keccak256 of a 1024-bit root for use as mapping key
    function _rootKey(uint256[4] memory r) internal pure returns (uint256) {
        return uint256(keccak256(abi.encodePacked(r[0], r[1], r[2], r[3])));
    }
}
