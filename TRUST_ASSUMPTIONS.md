# Trust Assumptions

This document describes what the Rocq formal proofs in this repository verify, what they do *not* verify, and the trust assumptions that sit above, below, and adjacent to the proof boundary.

## What the Proofs Verify

The 49 Rocq proof files (~4,800 lines) verify **constraint soundness over the integers (Z)**: if a witness satisfies all R1CS constraints emitted by a circuit template, then the stated mathematical property holds over unbounded integers.

Each proof hand-models the constraint semantics of a circom template and proves the corresponding soundness theorem. There are zero `Admitted` axioms; every theorem is machine-checked.

**Coverage spans the full circuit library:**

| Domain | Modules |
|---|---|
| Core primitives | Num2Bits, Bits2Num, bit decomposition |
| Comparators | IsZero, IsEqual, LessThan, GreaterThan, bounds checking |
| Bitwise operations | AND, OR, XOR, NOT, shifting |
| Packing | Field-to-byte and byte-to-field conversions |
| Arithmetic | BigAdd, BigSub, multi-limb addition/subtraction |
| Hashing | SHA-256 (rounds, schedule, padding), Poseidon, Merkle trees, Ascon |
| Linear algebra | Dot product, matrix-vector multiply |
| Curve arithmetic | BabyJubjub point addition/doubling, Montgomery form, scalar multiplication |
| Cryptographic protocols | ElGamal encryption/decryption, Schnorr signatures, RSA blinding |
| Collections & search | Arrays, binary search, embedding vectors |

The 48 `.cirq` barrel files provide machine-readable proof metadata linking each proof file to its corresponding circuit.

## Trust Assumptions Below the Proofs (Infrastructure)

These assumptions concern the toolchain and infrastructure that sits beneath the proof layer.

| Assumption | Description | Formally Verifiable? |
|---|---|---|
| **Circom compiler correctness** | The compiler correctly translates `.circom` source to R1CS constraints | Theoretically yes ([Formal Land's Garden](https://formal.land/)); practically not yet done for this project |
| **Proving system soundness** | Groth16/PLONK/etc. is sound: a valid proof implies the constraints are satisfied | Proven in academic papers; implementation correctness is a separate question |
| **Trusted setup integrity** | For Groth16: the powers-of-tau ceremony was performed correctly and toxic waste was destroyed | Inherently trust-based (mitigated by MPC ceremonies) |
| **Prover/verifier implementation** | snarkjs, rapidsnark, and similar tools are free of bugs that would accept invalid proofs | Auditable but not formally verified |
| **Rocq kernel correctness** | The Rocq (Coq) proof checker itself is correct | Very high assurance: small trusted kernel (~10k lines), decades of academic use and scrutiny |

## Trust Assumptions Above the Proofs (Cryptographic)

These are standard cryptographic hardness assumptions that the *protocols* (not the proofs) rely on.

| Assumption | Used By | Type |
|---|---|---|
| **SHA-256 collision resistance** | Schnorr commitments, SHA-256 circuits | Standard model assumption |
| **Poseidon security** | Merkle trees, vector commitments | Algebraic setting assumption |
| **BabyJubjub discrete log hardness** | ElGamal, Schnorr | Computational assumption |
| **ElGamal IND-CPA security** | ElGamal encryption | DDH assumption on BabyJubjub |
| **Schnorr unforgeability** | Schnorr signatures | DL assumption + random oracle model |
| **RSA assumption** | RSA blinding | Factoring hardness |
| **BabyJubjub group law** | Curve arithmetic, scalar multiplication | Mathematically provable but not yet mechanized ([#5][i5]) |

## Trust Assumptions Adjacent to the Proofs (Verification Gaps)

These are known gaps between what the proofs cover and full end-to-end verification.

| Gap | Description | Mitigation | Issue |
|---|---|---|---|
| **Z vs F_p** | Proofs reason over unbounded integers, not the prime field F_p. Results hold only when intermediate values stay within the field modulus. | Circuits in this library use values well within 2^253 in a ~2^254 field, making overflow implausible for normal inputs. | [#4][i4] |
| **Witness generation** | The `<--` (assign-only) computations in circom are not covered by the proofs. A bug in witness generation causes proof generation to fail, not unsoundness. | 1,036 tests exercise witness generation across all circuits. | [#2][i2] |
| **Under-constraint** | There is no automated check that every signal is fully constrained by `<==` or `===`. An under-constrained signal could allow a malicious prover to forge proofs. | Test coverage, manual audit, and circuit review. | [#3][i3] |
| **Parameter correctness** | Curve constants (BabyJubjub base point, order), SHA-256 round constants, and Poseidon parameters are assumed correct. | Values are taken from published standards and reference implementations. | -- |
| **Circuit composition** | Most proofs verify individual templates in isolation, not full application-level compositions of multiple templates. | Integration tests cover composed circuits. | -- |

## What This Means for Users

**The proofs provide high confidence in constraint correctness.** If the Rocq proof for a template type-checks, then any witness satisfying the emitted constraints will have the stated mathematical property. This eliminates an entire class of bugs: accidentally writing constraints that admit invalid witnesses.

**The proofs do not guarantee protocol-level security.** Whether a circuit is *secure* as a cryptographic protocol depends on the layers above (hardness assumptions, protocol design) and below (compiler, proving system, trusted setup). The proofs sit in the middle of this stack.

**The biggest practical risk is under-constraint** ([#3][i3]). If a signal lacks a constraining equation, a malicious prover can set it to any value and still produce a valid proof. The proofs verify that the constraints *that exist* are correct, but cannot detect missing constraints.

**The Z-vs-F_p gap is low risk for typical use** ([#4][i4]). It matters most for multi-limb arithmetic circuits where intermediate sums approach the field modulus. For the vast majority of circuits in this library (comparators, hashing, curve operations with standard-size inputs), values stay far below the ~2^254 modulus.

## References

- [rocq/README.md](rocq/README.md) -- proof methodology and setup instructions
- [#2 -- Completeness proofs for witness computation][i2]
- [#3 -- Under-constraint detection or verification][i3]
- [#4 -- Bridge Z proofs to prime field arithmetic][i4]
- [#5 -- Prove BabyJubjub group law properties][i5]
- [#6 -- Document trust assumptions outside proof scope][i6]

[i2]: https://github.com/TheFrozenFire/circom-circuits/issues/2
[i3]: https://github.com/TheFrozenFire/circom-circuits/issues/3
[i4]: https://github.com/TheFrozenFire/circom-circuits/issues/4
[i5]: https://github.com/TheFrozenFire/circom-circuits/issues/5
[i6]: https://github.com/TheFrozenFire/circom-circuits/issues/6
