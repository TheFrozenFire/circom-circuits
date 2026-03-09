// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/RSAMerkleTree.sol";

contract RSAMerkleTreeTest is Test {
    RSAMerkleTree tree;

    // Arbitrary 2048-bit odd modulus for gas benchmarking.
    // Security properties don't matter here — only gas measurement.
    uint256[8] N = [
        0xD1B0EDCF29BFC0B5EC2D0E6F5B3A4C8D7E1F2A3B4C5D6E7F8091A2B3C4D5E6,
        0xF7E8D9CABC0D1E2F3A4B5C6D7E8F90A1B2C3D4E5F6071829A3B4C5D6E7F8091,
        0xA2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F70819,
        0xD5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4,
        0xE6F70819A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5,
        0xF70819A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5E6,
        0x0819A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F7,
        0x19A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F701
    ];

    // Test base value (smaller than N)
    uint256[8] testBase = [
        0x1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF,
        0x2345678901BCDEF02345678901BCDEF02345678901BCDEF02345678901BCDEF0,
        0x3456789012CDEF013456789012CDEF013456789012CDEF013456789012CDEF01,
        0x456789012CDEF0134456789012CDEF0134456789012CDEF0134456789012CDEF,
        0x56789012CDEF013456789012CDEF013456789012CDEF013456789012CDEF0134,
        0x6789012CDEF0134566789012CDEF0134566789012CDEF0134566789012CDEF01,
        0x789012CDEF01345678789012CDEF01345678789012CDEF01345678789012CDEF,
        0x89012CDEF0134567089012CDEF0134567089012CDEF0134567089012CDEF0134
    ];

    function setUp() public {
        tree = new RSAMerkleTree(N);
    }

    // ─── Correctness ─────────────────────────────────────────────

    /// @notice Cubing zero should return zero.
    function test_cubeZero() public view {
        uint256[8] memory zero;
        uint256[8] memory result = tree.cube(zero);
        for (uint256 i = 0; i < 8; i++) {
            assertEq(result[i], 0, "cube(0) must be 0");
        }
    }

    /// @notice Cubing 1 should return 1.
    function test_cubeOne() public view {
        uint256[8] memory one;
        one[7] = 1; // least significant limb
        uint256[8] memory result = tree.cube(one);
        for (uint256 i = 0; i < 7; i++) {
            assertEq(result[i], 0, "cube(1) upper limbs must be 0");
        }
        assertEq(result[7], 1, "cube(1) must be 1");
    }

    /// @notice Cubing 2 should return 8.
    function test_cubeTwo() public view {
        uint256[8] memory two;
        two[7] = 2;
        uint256[8] memory result = tree.cube(two);
        for (uint256 i = 0; i < 7; i++) {
            assertEq(result[i], 0, "cube(2) upper limbs must be 0");
        }
        assertEq(result[7], 8, "cube(2) must be 8");
    }

    /// @notice H(0, 0) should be 0 (zero propagation for empty tree).
    function test_hashZeroZero() public view {
        uint256[8] memory zero;
        uint256[8] memory result = tree.rsaMerkleHash(zero, zero);
        for (uint256 i = 0; i < 8; i++) {
            assertEq(result[i], 0, "H(0,0) must be 0");
        }
    }

    /// @notice H(L, R) != H(R, L) for L != R (asymmetry from the constant 2).
    function test_hashAsymmetry() public view {
        uint256[8] memory a;
        uint256[8] memory b;
        a[7] = 3;
        b[7] = 5;

        uint256[8] memory h1 = tree.rsaMerkleHash(a, b);
        uint256[8] memory h2 = tree.rsaMerkleHash(b, a);

        bool differ = false;
        for (uint256 i = 0; i < 8; i++) {
            if (h1[i] != h2[i]) { differ = true; break; }
        }
        assertTrue(differ, "H(L,R) must differ from H(R,L)");
    }

    /// @notice Empty tree root should be zero.
    function test_emptyRoot() public view {
        uint256[8] memory root = tree.currentRoot();
        for (uint256 i = 0; i < 8; i++) {
            assertEq(root[i], 0, "Empty root must be 0");
        }
    }

    /// @notice Root changes after deposit.
    function test_depositChangesRoot() public {
        tree.deposit(testBase);

        uint256[8] memory root = tree.currentRoot();
        bool nonZero = false;
        for (uint256 i = 0; i < 8; i++) {
            if (root[i] != 0) { nonZero = true; break; }
        }
        assertTrue(nonZero, "Root must be non-zero after deposit");
    }

    /// @notice Zero commitment is rejected.
    function test_revertZeroCommitment() public {
        uint256[8] memory zero;
        vm.expectRevert("Zero commitment");
        tree.deposit(zero);
    }

    // ─── Gas benchmarks ──────────────────────────────────────────

    /// @notice Benchmark: single modexp cube.
    function test_gasCube() public view {
        tree.cube(testBase);
    }

    /// @notice Benchmark: single Merkle hash (2 cubes + 3 additions).
    function test_gasMerkleHash() public view {
        uint256[8] memory other;
        other[7] = 42;
        tree.rsaMerkleHash(testBase, other);
    }

    /// @notice Benchmark: first deposit (all cold storage).
    function test_gasDeposit1() public {
        tree.deposit(testBase);
    }

    /// @notice Benchmark: second deposit (some warm storage).
    function test_gasDeposit2() public {
        tree.deposit(testBase);

        uint256[8] memory leaf2 = testBase;
        leaf2[7] += 1;
        tree.deposit(leaf2);
    }

    /// @notice Benchmark: third deposit.
    function test_gasDeposit3() public {
        tree.deposit(testBase);

        uint256[8] memory leaf2 = testBase;
        leaf2[7] += 1;
        tree.deposit(leaf2);

        uint256[8] memory leaf3 = testBase;
        leaf3[7] += 2;
        tree.deposit(leaf3);
    }

}
