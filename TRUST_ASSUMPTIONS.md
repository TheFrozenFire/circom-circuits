# Trust Assumptions

This document describes what the Rocq formal proofs in this repository verify, what they do *not* verify, and the trust assumptions that sit above, below, and adjacent to the proof boundary.

## What the Proofs Verify

The 49 Rocq proof files (~5,200 lines) verify **constraint soundness over the integers (Z)**: if a witness satisfies all R1CS constraints emitted by a circuit template, then the stated mathematical property holds over unbounded integers.

Each proof hand-models the constraint semantics of a circom template and proves the corresponding soundness theorem. Soundness proofs have zero `Admitted` axioms; every soundness theorem is machine-checked.

**Completeness proofs** additionally verify that the `<--` witness computation formulas actually produce values satisfying the `===` constraints, for valid inputs. 27 templates across Tiers 1-5 have machine-checked completeness proofs. Tiers 1-3 (bitify, arithmetic, fixed-point, vector, curve, hashing) use `WitnessLemmas.v` shared infrastructure over Z. Tier 4 templates using field inversion have completeness proofs stated mod p, depending on 2 axioms for `fp_inv` (the multiplicative inverse in F_p) in `FieldBridge.v`. Tier 5 composite circuits (Max, BigMod, BigSubModP, BigMultModP, BigModInv, Sha256compression) have completeness proofs depending on additional axioms for multi-limb modular inverse (`big_mod_inv`, 3 axioms in `BigInt.v`) and SHA-256 compression (`sha256_compress`, 2 axioms in `Sha256compression.v`).

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
| **BabyJubjub group law** | Curve arithmetic, scalar multiplication | Axiomatized in `CurveParams.v`. 11 axioms state closure, associativity, commutativity, identity, inverse, scalar multiplication properties, and the connection between the Edwards addition formula and the abstract group operation. These are standard properties of twisted Edwards curves with the BabyJubjub parameters (a=168700, d=168696), verified in published literature but not machine-checked. ([#5][i5]) |
| **Field multiplicative inverse** | IsZero, IsEqual, Montgomery conversions, MontgomeryAdd/Double completeness | Axiomatized in `FieldBridge.v`. `fp_inv` is an opaque function with 2 axioms: `fp_inv_in_field` (inverse is in the field) and `fp_inv_spec` (`a * fp_inv(a) ≡ 1 mod p`). Models Fermat's little theorem (`a^(p-2) mod p`), which Circom uses for field division. |
| **Multi-limb modular inverse** | BigModInv completeness | Axiomatized in `BigInt.v`. `big_mod_inv` is an opaque function with 3 axioms: `big_mod_inv_length` (output has k limbs), `big_mod_inv_range` (each limb is in [0, 2^n)), and `big_mod_inv_spec` (`a * big_mod_inv(a,p) ≡ 1 mod p` when gcd(a,p)=1). Models the extended Euclidean algorithm over multi-limb integers. |
| **SHA-256 compression function** | Sha256compression completeness | Axiomatized in `Sha256compression.v`. `sha256_compress` is an opaque function with 2 axioms: `sha256_compress_length` (output has 256 bits) and `sha256_compress_binary` (output is all binary when inputs are binary). Models the 64-round SHA-256 compression function, a well-established NIST standard. |

## Resolved Verification Gaps

These gaps have been addressed by dedicated work items.

| Gap | Resolution | Issue |
|---|---|---|
| **Z vs F_p** | `FieldBridge.v` provides the BN128 scalar field prime and bridging lemmas. Key templates (Num2Bits, LessThan, BigAdd, BigSub, BigMult, CheckCarryToZero) have proven field-safety theorems showing that under standard parameter constraints (e.g., n <= 253 for bit widths), all intermediate constraint values stay below p, so the Z proofs apply unchanged in F_p. Templates without explicit field-safety theorems inherit safety from their components. | [#4][i4] |
| **Witness generation (Tiers 1-3)** | 15 templates have fully machine-checked completeness proofs with zero `Admitted` axioms: Num2BitsLE, TruncNumLE, BinSum, FixedPointMul/Div/DotProduct, VectorMean, BabySuborderAdd, BigAdd, BigSub, BigMult, LongToShortNoEndCarry, CheckCarryToZero. | [#2][i2] |
| **Witness generation (Tier 4)** | 6 templates using field inversion have completeness proofs depending on 2 `fp_inv` axioms: IsZero, IsEqual, Edwards2Montgomery, Montgomery2Edwards, MontgomeryAdd, MontgomeryDouble. BabyAdd completeness depends only on pre-existing `baby_add_formula` axiom (no `fp_inv`). | [#2][i2] |
| **Under-constraint** | Automated under-constraint detection suite covers all circuit templates with signal coverage and degree-of-freedom checks. | [#3][i3] |
| **Witness generation (Tier 5)** | 6 composite circuits have completeness proofs: Max (pure Z), BigMod/BigMultModP/BigSubModP (via `num_to_limbs` decomposition), BigModInv (3 `big_mod_inv` axioms), Sha256compression (2 `sha256_compress` axioms). LessThan completeness also added to support Max. | [#13][i13] |

## Remaining Verification Gaps

These are known gaps between what the proofs cover and full end-to-end verification.

| Gap | Description | Mitigation |
|---|---|---|
| **Parameter correctness** | Curve constants (BabyJubjub base point, order), SHA-256 round constants, and Poseidon parameters are assumed correct. | Values are taken from published standards and reference implementations. |
| **Circuit composition** | Most proofs verify individual templates in isolation, not full application-level compositions of multiple templates. | Integration tests cover composed circuits. |

## What This Means for Users

**The proofs provide high confidence in constraint correctness.** If the Rocq proof for a template type-checks, then any witness satisfying the emitted constraints will have the stated mathematical property. This eliminates an entire class of bugs: accidentally writing constraints that admit invalid witnesses.

**The proofs do not guarantee protocol-level security.** Whether a circuit is *secure* as a cryptographic protocol depends on the layers above (hardness assumptions, protocol design) and below (compiler, proving system, trusted setup). The proofs sit in the middle of this stack.

**Under-constraint detection is automated** ([#3][i3]). All circuit templates have signal coverage and degree-of-freedom checks to catch missing constraints.

**The Z-vs-F_p gap is bridged for key templates** ([#4][i4]). Under standard parameter constraints, the Z proofs apply unchanged in F_p.

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
[i13]: https://github.com/TheFrozenFire/circom-circuits/issues/13
