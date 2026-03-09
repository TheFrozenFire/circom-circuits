// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/RSAMerkleTree1024.sol";

contract RSAMerkleTree1024Test is Test {
    RSAMerkleTree1024 tree;

    // Arbitrary 1024-bit odd modulus for gas benchmarking.
    uint256[4] N = [
        0xD1B0EDCF29BFC0B5EC2D0E6F5B3A4C8D7E1F2A3B4C5D6E7F8091A2B3C4D5E6,
        0xF7E8D9CABC0D1E2F3A4B5C6D7E8F90A1B2C3D4E5F6071829A3B4C5D6E7F8091,
        0xA2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F70819,
        0xD5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C4D5E6F70819A2B3C5
    ];

    uint256[4] testBase = [
        0x1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF1234567890ABCDEF,
        0x2345678901BCDEF02345678901BCDEF02345678901BCDEF02345678901BCDEF0,
        0x3456789012CDEF013456789012CDEF013456789012CDEF013456789012CDEF01,
        0x456789012CDEF0134456789012CDEF0134456789012CDEF0134456789012CDEF
    ];

    function setUp() public {
        tree = new RSAMerkleTree1024(N);
    }

    // ─── Correctness ─────────────────────────────────────────────

    function test_cubeZero() public view {
        uint256[4] memory zero;
        uint256[4] memory result = tree.cube(zero);
        for (uint256 i = 0; i < 4; i++) {
            assertEq(result[i], 0, "cube(0) must be 0");
        }
    }

    function test_cubeOne() public view {
        uint256[4] memory one;
        one[3] = 1;
        uint256[4] memory result = tree.cube(one);
        for (uint256 i = 0; i < 3; i++) {
            assertEq(result[i], 0, "cube(1) upper limbs must be 0");
        }
        assertEq(result[3], 1, "cube(1) must be 1");
    }

    function test_cubeTwo() public view {
        uint256[4] memory two;
        two[3] = 2;
        uint256[4] memory result = tree.cube(two);
        for (uint256 i = 0; i < 3; i++) {
            assertEq(result[i], 0, "cube(2) upper limbs must be 0");
        }
        assertEq(result[3], 8, "cube(2) must be 8");
    }

    function test_hashZeroZero() public view {
        uint256[4] memory zero;
        uint256[4] memory result = tree.rsaMerkleHash(zero, zero);
        for (uint256 i = 0; i < 4; i++) {
            assertEq(result[i], 0, "H(0,0) must be 0");
        }
    }

    function test_hashAsymmetry() public view {
        uint256[4] memory a;
        uint256[4] memory b;
        a[3] = 3;
        b[3] = 5;

        uint256[4] memory h1 = tree.rsaMerkleHash(a, b);
        uint256[4] memory h2 = tree.rsaMerkleHash(b, a);

        bool differ = false;
        for (uint256 i = 0; i < 4; i++) {
            if (h1[i] != h2[i]) { differ = true; break; }
        }
        assertTrue(differ, "H(L,R) must differ from H(R,L)");
    }

    function test_depositChangesRoot() public {
        tree.deposit(testBase);

        uint256[4] memory root = tree.currentRoot();
        bool nonZero = false;
        for (uint256 i = 0; i < 4; i++) {
            if (root[i] != 0) { nonZero = true; break; }
        }
        assertTrue(nonZero, "Root must be non-zero after deposit");
    }

    function test_revertZeroCommitment() public {
        uint256[4] memory zero;
        vm.expectRevert("Zero commitment");
        tree.deposit(zero);
    }

    // ─── Gas benchmarks ──────────────────────────────────────────

    function test_gasCube() public view {
        tree.cube(testBase);
    }

    function test_gasMerkleHash() public view {
        uint256[4] memory other;
        other[3] = 42;
        tree.rsaMerkleHash(testBase, other);
    }

    function test_gasDeposit1() public {
        tree.deposit(testBase);
    }

    function test_gasDeposit2() public {
        tree.deposit(testBase);

        uint256[4] memory leaf2 = testBase;
        leaf2[3] += 1;
        tree.deposit(leaf2);
    }

    function test_gasDeposit3() public {
        tree.deposit(testBase);

        uint256[4] memory leaf2 = testBase;
        leaf2[3] += 1;
        tree.deposit(leaf2);

        uint256[4] memory leaf3 = testBase;
        leaf3[3] += 2;
        tree.deposit(leaf3);
    }
}
