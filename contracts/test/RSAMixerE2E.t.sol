// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import "forge-std/Test.sol";
import "../src/RSAMixer.sol";
import "../src/Groth16Verifier.sol";
import "./ProofFixture.sol";

contract RSAMixerE2E is Test {
    RSAMixer mixer;
    Groth16Verifier groth16Verifier;

    function setUp() public {
        groth16Verifier = new Groth16Verifier();
        uint256[4] memory mod_ = ProofFixture.modulus();
        mixer = new RSAMixer(mod_, address(groth16Verifier));
    }

    function test_e2e_depositAndWithdraw() public {
        // 1. Deposit all 4 leaves (same order as TS)
        uint256[4][4] memory deps = ProofFixture.deposits();
        for (uint256 i = 0; i < 4; i++) {
            mixer.deposit(deps[i]);
        }

        // 2. Verify proof on-chain
        (
            uint256[2] memory pA,
            uint256[2][2] memory pB,
            uint256[2] memory pC,
            uint256[66] memory pubSignals
        ) = ProofFixture.proof();

        mixer.withdraw(pA, pB, pC, pubSignals);

        // 3. Assert nullifier marked spent
        uint256 nullifierHash = pubSignals[32];
        assertTrue(mixer.nullifierHashes(nullifierHash), "Nullifier should be spent");
    }

    function test_e2e_doubleWithdrawReverts() public {
        uint256[4][4] memory deps = ProofFixture.deposits();
        for (uint256 i = 0; i < 4; i++) {
            mixer.deposit(deps[i]);
        }

        (
            uint256[2] memory pA,
            uint256[2][2] memory pB,
            uint256[2] memory pC,
            uint256[66] memory pubSignals
        ) = ProofFixture.proof();

        mixer.withdraw(pA, pB, pC, pubSignals);

        vm.expectRevert("Already spent");
        mixer.withdraw(pA, pB, pC, pubSignals);
    }

    function test_e2e_wrongRootReverts() public {
        // Do NOT deposit — root is empty tree root only

        (
            uint256[2] memory pA,
            uint256[2][2] memory pB,
            uint256[2] memory pC,
            uint256[66] memory pubSignals
        ) = ProofFixture.proof();

        vm.expectRevert("Unknown root");
        mixer.withdraw(pA, pB, pC, pubSignals);
    }
}
