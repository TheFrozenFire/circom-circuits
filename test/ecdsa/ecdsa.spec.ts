import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { secp256k1 } from "@noble/curves/secp256k1.js";

const Point = secp256k1.Point;
const CURVE_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141n;
const n = 32;
const k = 8;

function toLimbs32(val: bigint): bigint[] {
    const mask = (1n << 32n) - 1n;
    return Array.from({ length: 8 }, (_, i) => (val >> (BigInt(i) * 32n)) & mask);
}

function bytesToBigInt(bytes: Uint8Array): bigint {
    let result = 0n;
    for (const b of bytes) result = (result << 8n) | BigInt(b);
    return result;
}

function modInv(a: bigint, m: bigint): bigint {
    let [old_r, r] = [a % m, m];
    let [old_s, s] = [1n, 0n];
    while (r !== 0n) {
        const q = old_r / r;
        [old_r, r] = [r, old_r - q * r];
        [old_s, s] = [s, old_s - q * s];
    }
    return ((old_s % m) + m) % m;
}

/// Compute u2pub_hint = [u2]·pubkey for the hinted ECDSA template.
function computeU2PubHint(r: bigint, s: bigint, pubkey: { x: bigint; y: bigint }) {
    const sinv = modInv(s, CURVE_ORDER);
    const u2 = (r * sinv) % CURVE_ORDER;
    const pubPoint = Point.fromAffine(pubkey);
    const result = pubPoint.multiply(u2).toAffine();
    return { x: result.x, y: result.y };
}

// Generate a test ECDSA signature using noble-secp256k1
function generateTestVector() {
    // Known private key (deterministic for reproducibility)
    const privkey = 0xdeadbeefcafebabedeadbeefcafebabedeadbeefcafebabedeadbeefcafebaben;
    const pubkeyPoint = Point.BASE.multiply(privkey).toAffine();

    // Message hash (just a known value for testing)
    const msghash = 0xabcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789n;

    // Sign using noble-secp256k1
    const msgBytes = new Uint8Array(32);
    for (let i = 0; i < 32; i++) {
        msgBytes[31 - i] = Number((msghash >> BigInt(i * 8)) & 0xFFn);
    }
    const privBytes = new Uint8Array(32);
    let pk = privkey;
    for (let i = 0; i < 32; i++) {
        privBytes[31 - i] = Number(pk & 0xFFn);
        pk >>= 8n;
    }

    // noble-curves v2: prehash=false means msgBytes is already a hash (don't SHA-256 again)
    const sigBytes = secp256k1.sign(msgBytes, privBytes, { prehash: false });
    const r = bytesToBigInt(sigBytes.slice(0, 32));
    const s = bytesToBigInt(sigBytes.slice(32, 64));

    return {
        r,
        s,
        msghash,
        pubkey: { x: pubkeyPoint.x, y: pubkeyPoint.y },
    };
}

describe_circuit("ECDSAVerifyNoPubkeyCheck", {
    verify: { path: "ecdsa/ecdsa.circom", template: "ECDSAVerifyNoPubkeyCheck", params: [n, k] },
}, (calculators) => {

    it("verifies a valid ECDSA signature (result = 1)", async () => {
        const tv = generateTestVector();
        const hint = computeU2PubHint(tv.r, tv.s, tv.pubkey);

        const w = await calculators.verify.calculate({
            r: toLimbs32(tv.r),
            s: toLimbs32(tv.s),
            msghash: toLimbs32(tv.msghash),
            pubkey: [toLimbs32(tv.pubkey.x), toLimbs32(tv.pubkey.y)],
            u2pub_hint: [toLimbs32(hint.x), toLimbs32(hint.y)],
        });

        const result = w.value("main.result");
        assert.equal(result, 1n, "Valid signature should return result=1");
    });

    it("rejects a signature with wrong r (result = 0)", async () => {
        const tv = generateTestVector();
        // Modify r to make it invalid — recompute hint with bad r
        const badR = tv.r ^ 1n;
        const hint = computeU2PubHint(badR, tv.s, tv.pubkey);

        const w = await calculators.verify.calculate({
            r: toLimbs32(badR),
            s: toLimbs32(tv.s),
            msghash: toLimbs32(tv.msghash),
            pubkey: [toLimbs32(tv.pubkey.x), toLimbs32(tv.pubkey.y)],
            u2pub_hint: [toLimbs32(hint.x), toLimbs32(hint.y)],
        });

        const result = w.value("main.result");
        assert.equal(result, 0n, "Invalid signature should return result=0");
    });
});
