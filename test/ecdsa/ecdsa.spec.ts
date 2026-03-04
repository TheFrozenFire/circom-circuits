import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { secp256k1 } from "@noble/curves/secp256k1.js";

const Point = secp256k1.Point;
const n = 64;
const k = 4;

function toLimbs64(val: bigint): bigint[] {
    const mask = (1n << 64n) - 1n;
    return Array.from({ length: 4 }, (_, i) => (val >> (BigInt(i) * 64n)) & mask);
}

function bytesToBigInt(bytes: Uint8Array): bigint {
    let result = 0n;
    for (const b of bytes) result = (result << 8n) | BigInt(b);
    return result;
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

        const w = await calculators.verify.calculate({
            r: toLimbs64(tv.r),
            s: toLimbs64(tv.s),
            msghash: toLimbs64(tv.msghash),
            pubkey: [toLimbs64(tv.pubkey.x), toLimbs64(tv.pubkey.y)],
        });

        const result = w.value("main.result");
        assert.equal(result, 1n, "Valid signature should return result=1");
    });

    it("rejects a signature with wrong r (result = 0)", async () => {
        const tv = generateTestVector();
        // Modify r to make it invalid
        const badR = tv.r ^ 1n;

        const w = await calculators.verify.calculate({
            r: toLimbs64(badR),
            s: toLimbs64(tv.s),
            msghash: toLimbs64(tv.msghash),
            pubkey: [toLimbs64(tv.pubkey.x), toLimbs64(tv.pubkey.y)],
        });

        const result = w.value("main.result");
        assert.equal(result, 0n, "Invalid signature should return result=0");
    });
});
