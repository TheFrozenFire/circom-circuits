pragma circom 2.2.2;

include "arithmetic/bigint_crt.circom";

/// Computes base³ mod p via two modular multiplications.
/// Both steps use nocanon CRT verification (no BigLessThan on output).
///
/// Output satisfies out ≡ base³ (mod p) with 0 ≤ out[i] < 2^n,
/// but out is NOT guaranteed < p. This is safe because:
///   - Cubing is mod p, so any consumer that reduces mod p gets the
///     correct canonical result regardless (x ≡ x + c·p).
///   - RSAMerkleHash applies BigMod at the end of each level,
///     which canonicalizes the final hash output.
///   - Saves one BigLessThan(n, k) per cube (~1104 constraints at n=64, k=16).
///
/// Cost: 2 BigMultModP_CRT_nocanon
template RSACube(n, k) {
    signal input base[k];
    signal input p[k];
    signal output out[k];

    // base² mod p (no canonical check — intermediate value)
    signal sq[k] <== BigMultModP_CRT_nocanon(n, k)(base, base, p);

    // base³ = base² · base mod p (nocanon: canonicalization deferred to consumer)
    out <== BigMultModP_CRT_nocanon(n, k)(sq, base, p);
}
