import { assert } from "chai";
import { describe_circuit, COMPILE_TIMEOUT_MS } from "../helpers.js";
import { secp256k1 } from "@noble/curves/secp256k1.js";

const Point = secp256k1.Point;
const n = 64;
const k = 4;

function toLimbs64(val: bigint): bigint[] {
    const mask = (1n << 64n) - 1n;
    return Array.from({ length: 4 }, (_, i) => (val >> (BigInt(i) * 64n)) & mask);
}

function fromLimbs64(limbs: bigint[]): bigint {
    let result = 0n;
    for (let i = limbs.length - 1; i >= 0; i--) {
        result = (result << 64n) + limbs[i];
    }
    return result;
}

describe_circuit("Secp256k1AddUnequal", {
    add: { path: "ecdsa/point.circom", template: "Secp256k1AddUnequal", params: [n, k] },
}, (calculators) => {

    it("adds two known points: G + 2G = 3G", async () => {
        const G = Point.BASE;
        const twoG = G.multiply(2n);
        const threeG = G.multiply(3n);
        const gAff = G.toAffine();
        const twoGAff = twoG.toAffine();
        const threeGAff = threeG.toAffine();

        const w = await calculators.add.calculate({
            a: [toLimbs64(gAff.x), toLimbs64(gAff.y)],
            b: [toLimbs64(twoGAff.x), toLimbs64(twoGAff.y)],
        });

        const outX = w.array("main.out[0]");
        const outY = w.array("main.out[1]");
        assert.equal(fromLimbs64(outX), threeGAff.x);
        assert.equal(fromLimbs64(outY), threeGAff.y);
    });

    it("adds 5G + 7G = 12G", async () => {
        const fiveG = Point.BASE.multiply(5n).toAffine();
        const sevenG = Point.BASE.multiply(7n).toAffine();
        const twelveG = Point.BASE.multiply(12n).toAffine();

        const w = await calculators.add.calculate({
            a: [toLimbs64(fiveG.x), toLimbs64(fiveG.y)],
            b: [toLimbs64(sevenG.x), toLimbs64(sevenG.y)],
        });

        const outX = w.array("main.out[0]");
        const outY = w.array("main.out[1]");
        assert.equal(fromLimbs64(outX), twelveG.x);
        assert.equal(fromLimbs64(outY), twelveG.y);
    });
});

describe_circuit("Secp256k1Double", {
    dbl: { path: "ecdsa/point.circom", template: "Secp256k1Double", params: [n, k] },
}, (calculators) => {

    it("doubles G: 2 * G", async () => {
        const G = Point.BASE.toAffine();
        const twoG = Point.BASE.multiply(2n).toAffine();

        const w = await calculators.dbl.calculate({
            in: [toLimbs64(G.x), toLimbs64(G.y)],
        });

        const outX = w.array("main.out[0]");
        const outY = w.array("main.out[1]");
        assert.equal(fromLimbs64(outX), twoG.x);
        assert.equal(fromLimbs64(outY), twoG.y);
    });

    it("doubles 3G: 2 * 3G = 6G", async () => {
        const threeG = Point.BASE.multiply(3n).toAffine();
        const sixG = Point.BASE.multiply(6n).toAffine();

        const w = await calculators.dbl.calculate({
            in: [toLimbs64(threeG.x), toLimbs64(threeG.y)],
        });

        const outX = w.array("main.out[0]");
        const outY = w.array("main.out[1]");
        assert.equal(fromLimbs64(outX), sixG.x);
        assert.equal(fromLimbs64(outY), sixG.y);
    });
});
