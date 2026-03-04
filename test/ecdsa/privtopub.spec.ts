import { assert } from "chai";
import { describe_circuit } from "../helpers.js";
import { secp256k1 } from "@noble/curves/secp256k1.js";

const Point = secp256k1.Point;
const n = 32;
const k = 8;

function toLimbs32(val: bigint): bigint[] {
    const mask = (1n << 32n) - 1n;
    return Array.from({ length: 8 }, (_, i) => (val >> (BigInt(i) * 32n)) & mask);
}

function fromLimbs32(limbs: bigint[]): bigint {
    let result = 0n;
    for (let i = limbs.length - 1; i >= 0; i--) {
        result = (result << 32n) + limbs[i];
    }
    return result;
}

describe_circuit("Secp256k1PrivToPub", {
    ptop: { path: "ecdsa/scalarmul.circom", template: "Secp256k1PrivToPub", params: [n, k] },
}, (calculators) => {

    it("computes pubkey for privkey=1 (generator)", async () => {
        const expected = Point.BASE.toAffine();

        const w = await calculators.ptop.calculate({
            privkey: toLimbs32(1n),
        });

        const outX = fromLimbs32(w.array("main.pubkey[0]"));
        const outY = fromLimbs32(w.array("main.pubkey[1]"));
        assert.equal(outX, expected.x);
        assert.equal(outY, expected.y);
    });

    it("computes pubkey for a 256-bit private key", async () => {
        const privkey = 0xdeadbeefcafebabedeadbeefcafebabedeadbeefcafebabedeadbeefcafebaben;
        const expected = Point.BASE.multiply(privkey).toAffine();

        const w = await calculators.ptop.calculate({
            privkey: toLimbs32(privkey),
        });

        const outX = fromLimbs32(w.array("main.pubkey[0]"));
        const outY = fromLimbs32(w.array("main.pubkey[1]"));
        assert.equal(outX, expected.x);
        assert.equal(outY, expected.y);
    });
});
