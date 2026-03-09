pragma circom 2.2.2;

include "arithmetic/bigint_crt.circom";

/// Computes base³ mod p via two modular multiplications.
/// Uses CRT verification: nocanon for the intermediate squaring,
/// canonical for the final multiply (guarantees out < p).
///
/// Cost: 1 BigMultModP_CRT_nocanon + 1 BigMultModP_CRT
template RSACube(n, k) {
    signal input base[k];
    signal input p[k];
    signal output out[k];

    // base² mod p (no canonical check — intermediate value)
    signal sq[k] <== BigMultModP_CRT_nocanon(n, k)(base, base, p);

    // base³ = base² · base mod p (canonical: out < p)
    out <== BigMultModP_CRT(n, k)(sq, base, p);
}
