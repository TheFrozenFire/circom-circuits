// BN128 field modulus
export const p = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

export const BABYJUB_A = 168700n;
export const BABYJUB_D = 168696n;
export const SUBORDER = 2736030358979909402780800718157159386076813972158567259200215660948447373041n;
export const BASE8_X = 5299619240641551281634865583518297030282874472190772894086521144482721001553n;
export const BASE8_Y = 16950150798460657717958625567821834550301663161624707787222815936182638968203n;

export function mod(a: bigint): bigint {
    return ((a % p) + p) % p;
}

export function modPow(base: bigint, exp: bigint): bigint {
    let result = 1n;
    base = mod(base);
    while (exp > 0n) {
        if (exp & 1n) result = mod(result * base);
        exp >>= 1n;
        base = mod(base * base);
    }
    return result;
}

export function modInv(a: bigint): bigint {
    return modPow(a, p - 2n);
}

export function babyAdd(x1: bigint, y1: bigint, x2: bigint, y2: bigint): [bigint, bigint] {
    const x1x2 = mod(x1 * x2);
    const y1y2 = mod(y1 * y2);
    const x1y2 = mod(x1 * y2);
    const y1x2 = mod(y1 * x2);
    const dx1x2y1y2 = mod(BABYJUB_D * mod(x1x2 * y1y2));

    const xnum = mod(x1y2 + y1x2);
    const xden = mod(1n + dx1x2y1y2);
    const xout = mod(xnum * modInv(xden));

    const ynum = mod(y1y2 + p - mod(BABYJUB_A * x1x2));
    const yden = mod(1n + p - dx1x2y1y2);
    const yout = mod(ynum * modInv(yden));

    return [xout, yout];
}

export function scalarMul(scalar: bigint, px: bigint, py: bigint): [bigint, bigint] {
    let rx = 0n;
    let ry = 1n; // identity point
    let qx = px;
    let qy = py;
    let s = scalar;
    while (s > 0n) {
        if (s & 1n) {
            [rx, ry] = babyAdd(rx, ry, qx, qy);
        }
        [qx, qy] = babyAdd(qx, qy, qx, qy);
        s >>= 1n;
    }
    return [rx, ry];
}
