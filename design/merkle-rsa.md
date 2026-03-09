# RSA-Based Mixer with Modular Exponentiation Merkle Tree

## Motivation

Privacy-preserving mixers (Tornado.cash-style) require a commitment scheme and a Merkle tree hash that are cheap for both the **on-chain verifier** (Ethereum) and the **ZK prover** (circom/Groth16). Existing designs choose either:

- **Poseidon/MiMC**: cheap in ZK, but no Ethereum precompile — expensive or requires custom Solidity assembly
- **Keccak**: cheap on Ethereum (native opcode), but ~150K constraints per hash in a SNARK circuit

RSA with a fixed small exponent (e=3) occupies a rare sweet spot:

- **On Ethereum**: the `modexp` precompile (EIP-198 / EIP-2565) with a 1-byte exponent costs ~200–350 gas per call
- **In ZK**: cubing requires exactly 2 `BigMultModP` operations (one squaring, one multiply)

This design uses RSA modular exponentiation as the **sole** shared primitive between prover and verifier — no Poseidon, no keccak, no hash function agreement problem.

## System Parameters

| Parameter | Value | Notes |
|---|---|---|
| RSA modulus N | 2048-bit | Generated via MPC ceremony; factorization destroyed |
| Exponent e | 3 | Fixed; gcd(3, φ(N)) = 1 requires p, q ≢ 1 (mod 3) |
| Limb width n | 64 | Bits per limb in bigint representation |
| Limb count k | 32 | 2048 / 64 = 32 limbs |
| Merkle tree depth | 20 | ~1M deposit slots |
| Asymmetry constant c | 2 | For Merkle compression; must not be a perfect cube |

## Leaf Commitment Scheme

### Construction

A depositor picks a random secret `s` and nullifier `ν`, both sufficiently large, and computes:

```
m = ν ‖ s        (concatenation, encoded as an element of Z_N)
C = m³ mod N
```

The commitment C is submitted on-chain as the Merkle leaf.

### Encoding Constraint

For e=3 and a 2048-bit modulus, if m < N^(1/3) ≈ 2^683, then m³ < N and the modular reduction never fires — the cube root is trivially recoverable over the integers. Therefore:

**m must be at least 683 bits.**

With ν as 256 bits and s as 1024 bits, the concatenation m = ν ‖ s is 1280 bits, providing comfortable margin. The cube wraps around mod N, and recovering m requires factoring N.

### Security Properties

| Property | Guarantee | Assumption |
|---|---|---|
| **Binding** | Perfect (information-theoretic) | None — cubing is a permutation on Z*_N, so each C has exactly one preimage |
| **Hiding** | Computational | RSA / factoring hardness (recovering m = ν ‖ s from m³ mod N) |

Since the commitment is constructed inside the ZK circuit by the depositor, traditional RSA concerns are neutralized:

- **No padding needed**: the circuit enforces correct construction; chosen-ciphertext malleability is irrelevant
- **Homomorphic structure is harmless**: an attacker cannot exploit C₁·C₂ = (m₁·m₂)³ because the ZK proof requires knowledge of the preimage, not just a well-formed ciphertext
- **Small-exponent attacks (Coppersmith, Håstad)** don't apply: there is no scenario where the same message is cubed under multiple moduli

### ZK Circuit Cost

```
m²     = BigMultModP(n, k)(m, m, N)       // 1 BigMultModP
m³     = BigMultModP(n, k)(m², m, N)      // 1 BigMultModP
                                           // Total: 2 BigMultModP
```

## Merkle Tree Compression Function

### Construction

```
H(L, R) = L³ + 2·R³  mod N
```

where L and R are sibling node values in Z_N (2048-bit, k=32 limbs).

The constant 2 breaks symmetry (H(L,R) ≠ H(R,L) in general) and is not a perfect cube, so computing 2^(1/3) mod N is itself the RSA problem. Multiplication by 2 is implemented as addition with itself — no bigint multiplication required.

### Operations Breakdown

On Ethereum (per tree level):
1. `modexp(L, 3, N)` — precompile call → L³
2. `modexp(R, 3, N)` — precompile call → R³
3. `R³ + R³` — 2048-bit addition → 2·R³
4. `L³ + 2·R³` — 2048-bit addition
5. Conditional subtract N (at most twice) → result mod N

In ZK (per tree level):
```
L²      = BigMultModP(n, k)(L, L, N)       // 1 BigMultModP
L³      = BigMultModP(n, k)(L², L, N)      // 1 BigMultModP
R²      = BigMultModP(n, k)(R, R, N)       // 1 BigMultModP
R³      = BigMultModP(n, k)(R², R, N)      // 1 BigMultModP
2·R³    = BigAdd(n, k)(R³, R³)             // BigAdd (cheap)
L³+2R³  = BigAdd(n, k)(L³, 2·R³)          // BigAdd (cheap)
result  = BigMod(n, k)(L³+2R³, N)          // or conditional subtract
                                            // Total: 4 BigMultModP + 2 BigAdd + reduction
```

### Cost Summary

| Component | ZK (BigMultModP calls) | Ethereum (modexp calls) | Ethereum (other) |
|---|---|---|---|
| Leaf commitment | 2 | 0 (off-chain) | — |
| Per Merkle level | 4 | 2 | 2048-bit add × 2, cond. subtract |
| Depth-20 tree path | 80 | 40 | 40 adds, 20 cond. subtracts |
| **Total (withdrawal proof)** | **82** | — | — |
| **Total (on-chain tree update)** | — | **40** | light bigint arithmetic |

### Collision Resistance

**Claim**: finding (L, R) ≠ (L', R') such that L³ + 2R³ ≡ L'³ + 2R'³ (mod N) is hard under the factoring assumption.

**Argument sketch**: The collision equation is L³ + 2R³ = L'³ + 2R'³ mod N.

- **Fix three, solve for fourth**: e.g., given L, L', R, solving for R' requires R'³ ≡ (L³ - L'³ + 2R³)·2⁻¹ (mod N) — a cube root mod N. This is the RSA problem.

- **Fix one pair equal**: if R = R', then L³ = L'³, forcing L = L' (cubing is a permutation). Similarly for L = L'.

- **Algebraic parameterization**: setting L' = L + a, R' = R + b for nonzero a, b yields:

  ```
  3a·L² + 3a²·L + (a³ - 6R²b - 6Rb² - 2b³) ≡ 0 (mod N)
  ```

  For fixed a, b, R, this is a **quadratic** in L mod N. Solving a quadratic mod N = pq requires computing square roots mod N, which is equivalent to factoring.

**Second preimage resistance** (the property that matters for Merkle tree security): given target T and one known input L, finding R such that H(L, R) = T requires:

```
2R³ ≡ T - L³ (mod N)
R  ≡ ∛((T - L³)·2⁻¹) (mod N)
```

This is directly the RSA problem. Each level of a forged Merkle path independently requires an RSA inversion.

### Why Not Other Constructions

| Candidate | Cost | Broken? | Why |
|---|---|---|---|
| (L + R)³ | 1 cube | Yes | (L+1, R-1) always collides — linear combination before cubing |
| (L³ + R)³ | 2 cubes | Yes | Outer cube is permutation; L³ + R = L'³ + R' is linear in R |
| L³ + R³ | 2 cubes | Yes | Symmetric — H(L,R) = H(R,L) for all L ≠ R |
| L³ + 8·R³ | 2 cubes | Yes | 8 = 2³ is a perfect cube; (L,R) → (2R, L/2) collides |
| **L³ + 2·R³** | **2 cubes** | **No (conjectured)** | **Collision requires cube root or square root mod N** |

## Nullifier Derivation

The nullifier is revealed publicly on withdrawal to prevent double-spending. It is derived inside the ZK circuit from the committed nullifier value ν.

The nullifier hash does **not** need to use RSA — it is a public output of the ZK circuit, verified by the SNARK verifier, not recomputed on-chain. A SNARK-friendly hash (Poseidon) is appropriate here since only the prover computes it:

```
nullifier_hash = Poseidon(ν)      // public output of the circuit
```

This is the one place where Poseidon appears — but it's only inside the ZK circuit, never on-chain. The contract only stores and checks the revealed nullifier_hash against a spent-nullifiers set.

## Protocol Flow

### Deposit

1. **User** (off-chain): picks random ν (256 bits), s (1024 bits); computes m = ν ‖ s; computes C = m³ mod N
2. **User** → **Contract**: submits C (2048-bit value)
3. **Contract**: inserts C as next leaf in on-chain Merkle tree; computes updated root using H(L, R) = L³ + 2R³ mod N via modexp precompile

### Withdrawal

1. **User** (off-chain): computes Merkle path from their leaf C to current root R
2. **User** generates ZK proof π with:
   - **Public inputs**: root R, nullifier_hash, recipient address
   - **Private inputs**: ν, s, Merkle path (siblings + path indices)
3. **Circuit** verifies:
   - m = ν ‖ s (encoding check / range constraints)
   - C = m³ mod N (2 BigMultModP)
   - Merkle path from C to R is valid (80 BigMultModP for depth 20)
   - nullifier_hash = Poseidon(ν)
4. **User** → **Contract**: submits π, nullifier_hash, recipient
5. **Contract**: verifies SNARK proof, checks nullifier_hash not in spent set, sends funds

## Trust Assumptions

| Assumption | Impact if Broken | Mitigation |
|---|---|---|
| **Factoring hardness** (N = pq) | Attacker can recover depositor secrets (breaks hiding), forge Merkle paths (breaks second preimage), find hash collisions | Use 2048-bit modulus; standard assumption |
| **RSA modulus integrity** | If factorization of N is known, all security collapses — attacker can forge membership proofs and steal funds | MPC ceremony to generate N; multiple participants ensure no single party learns p, q |
| **Groth16 soundness** | Invalid proofs could be accepted | Standard assumption; separate from RSA |
| **Groth16 trusted setup** | Prover could forge proofs | Powers-of-tau MPC ceremony |
| **p, q ≢ 1 (mod 3)** | Cubing must be a permutation on Z*_N; if 3 ∣ (p-1) or 3 ∣ (q-1), cubing is 3-to-1 on some elements, breaking perfect binding | Enforce during modulus generation |

## Circuit Architecture

```
┌─────────────────────────────────────────────────────┐
│  RSAMixerWithdraw(n=64, k=32, depth=20)             │
│                                                     │
│  Private inputs:                                    │
│    nullifier[k], secret[k],                         │
│    pathIndices[depth], siblings[depth][k]            │
│                                                     │
│  Public inputs:                                     │
│    root[k], nullifierHash, N[k], recipient          │
│                                                     │
│  ┌───────────────────────────────────┐              │
│  │ 1. Encode message                 │              │
│  │    m = ν ‖ s  (range checks)      │              │
│  └───────────┬───────────────────────┘              │
│              ▼                                      │
│  ┌───────────────────────────────────┐              │
│  │ 2. RSA commitment (2 BigMultModP) │              │
│  │    m² = BigMultModP(m, m, N)      │              │
│  │    C  = BigMultModP(m², m, N)     │              │
│  └───────────┬───────────────────────┘              │
│              ▼                                      │
│  ┌───────────────────────────────────┐              │
│  │ 3. RSA Merkle inclusion proof     │              │
│  │    (4 BigMultModP + adds per lvl) │              │
│  │                                   │              │
│  │    for each level:                │              │
│  │      (L, R) = mux(hash, sibling) │              │
│  │      L³ = BigMultModP(L², L, N)   │              │
│  │      R³ = BigMultModP(R², R, N)   │              │
│  │      hash = L³ + 2·R³ mod N       │              │
│  └───────────┬───────────────────────┘              │
│              ▼                                      │
│  ┌───────────────────────────────────┐              │
│  │ 4. Root check                     │              │
│  │    hash == root (BigIsEqual)      │              │
│  └───────────────────────────────────┘              │
│                                                     │
│  ┌───────────────────────────────────┐              │
│  │ 5. Nullifier derivation           │              │
│  │    nullifierHash == Poseidon(ν)   │              │
│  └───────────────────────────────────┘              │
└─────────────────────────────────────────────────────┘
```

## New Circuit Templates Required

| Template | Inputs | Outputs | Description |
|---|---|---|---|
| `RSACube(n, k)` | `m[k]`, `N[k]` | `out[k]` | Computes m³ mod N via 2 BigMultModP |
| `RSAMerkleHash(n, k)` | `L[k]`, `R[k]`, `N[k]` | `out[k]` | Computes L³ + 2·R³ mod N |
| `RSAMerkleTreeInclusionProof(n, k, depth)` | `leaf[k]`, `pathIndices[depth]`, `siblings[depth][k]`, `N[k]` | `root[k]` | Full Merkle path verification using RSAMerkleHash |
| `RSAMixerWithdraw(n, k, depth)` | (see architecture above) | — | Top-level withdrawal circuit |

## Existing Templates Used

From `circuits/arithmetic/bigint.circom`:
- `BigMultModP(n, k)` — modular multiplication (core building block)
- `BigAdd(n, k)` — limb-wise addition with carry
- `BigMod(n, k)` — modular reduction
- `BigIsEqual(k)` — equality check for multi-limb values
- `BigLessThan(n, k)` — comparison (for range checks)

From `circuits/hash/poseidon.circom`:
- `Poseidon(2)` — nullifier hashing only (not shared with on-chain)

From `circuits/core/mux.circom`:
- `MultiMux1(k)` — left/right child selection at each Merkle level (operates per-limb)

## On-Chain Contracts

### MerkleTree Storage

The contract maintains a sparse Merkle tree of 2048-bit leaves. Each node is a 2048-bit value stored as a `uint256[8]` (or bytes). On each deposit:

1. Insert leaf at next available index
2. Recompute path from leaf to root:
   ```solidity
   // Per level (pseudocode):
   L3 = modexp(L, 3, N)    // precompile call
   R3 = modexp(R, 3, N)    // precompile call
   parent = addmod(L3, addmod(R3, R3, N), N)
   ```
   Note: `addmod` is an EVM opcode but operates on 256-bit values. For 2048-bit arithmetic, implement as 8-word addition with carry in assembly, or use a helper library.

### Verifier

Standard Groth16 verifier generated by snarkjs. Public inputs include the Merkle root (as k field elements), nullifier hash, and recipient.

## Open Questions

1. **Formal security reduction**: the collision resistance argument is informal. A tight reduction from factoring to collision-finding in H(L,R) = L³ + 2R³ mod N would strengthen confidence. The structure resembles representation problems studied in algebraic number theory (norm forms over Z[∛2]).

2. **Constraint count estimation**: need to benchmark BigMultModP(64, 32) constraint count to produce concrete circuit size estimates. The total circuit cost is dominated by 82 BigMultModP calls.

3. **Modulus generation ceremony**: the MPC protocol for generating N without any party learning p, q is well-studied but adds operational complexity. The p ≢ 1 (mod 3) and q ≢ 1 (mod 3) constraints must be enforced during generation.

4. **On-chain 2048-bit arithmetic library**: need optimized Solidity assembly for 2048-bit addition, comparison, and conditional subtraction mod N. This is straightforward but must be gas-optimized and audited.

5. **BigMultModP for multi-limb mux**: the existing `MultiMux1(2)` selects between two field elements. For RSA Merkle levels, we need to mux between two k-limb arrays based on pathIndex. This requires a `MultiMux1(k)` or a per-limb loop over `Mux1`.

6. **Zero leaf handling**: H(0, 0) = 0. The empty tree hashes to zero at every level. The contract should reject C = 0 as a valid deposit commitment.

7. **Poseidon for nullifier**: Poseidon is used only inside the circuit for nullifier derivation. If eliminating Poseidon entirely is desired, the nullifier hash could also use RSA cubing: nullifier_hash = ν³ mod N. This adds 2 BigMultModP to the circuit but removes the Poseidon dependency. The tradeoff: the nullifier hash becomes a 2048-bit value (larger on-chain storage in the spent-set).
