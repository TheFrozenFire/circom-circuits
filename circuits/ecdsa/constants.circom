pragma circom 2.2.2;

/// secp256k1 field prime: p = 2^256 - 2^32 - 977.
/// Supports n=32, k=8 (8 × 32-bit limbs, little-endian).
function SECP256K1_PRIME(n, k) {
    assert(n == 32 && k == 8);
    var p[8];
    p[0] = 4294966319;  // 0xFFFFFC2F
    p[1] = 4294967294;  // 0xFFFFFFFE
    p[2] = 4294967295;  // 0xFFFFFFFF
    p[3] = 4294967295;
    p[4] = 4294967295;
    p[5] = 4294967295;
    p[6] = 4294967295;
    p[7] = 4294967295;
    return p;
}

/// secp256k1 curve group order.
function SECP256K1_ORDER(n, k) {
    assert(n == 32 && k == 8);
    var order[8];
    order[0] = 3493216577;  // 0xD0364141
    order[1] = 3218235020;  // 0xBFD25E8C
    order[2] = 2940772411;  // 0xAF48A03B
    order[3] = 3132021990;  // 0xBAAEDCE6
    order[4] = 4294967294;  // 0xFFFFFFFE
    order[5] = 4294967295;  // 0xFFFFFFFF
    order[6] = 4294967295;
    order[7] = 4294967295;
    return order;
}

/// secp256k1 generator x-coordinate.
function SECP256K1_GX(n, k) {
    assert(n == 32 && k == 8);
    var gx[8];
    gx[0] = 385357720;   // 0x16F81798
    gx[1] = 1509065051;  // 0x59F2815B
    gx[2] = 768485593;   // 0x2DCE28D9
    gx[3] = 43777243;    // 0x029BFCDB
    gx[4] = 3464956679;  // 0xCE870B07
    gx[5] = 1436574357;  // 0x55A06295
    gx[6] = 4191992748;  // 0xF9DCBBAC
    gx[7] = 2042521214;  // 0x79BE667E
    return gx;
}

/// secp256k1 generator y-coordinate.
function SECP256K1_GY(n, k) {
    assert(n == 32 && k == 8);
    var gy[8];
    gy[0] = 4212184248;  // 0xFB10D4B8
    gy[1] = 2621952143;  // 0x9C47D08F
    gy[2] = 2793755673;  // 0xA6855419
    gy[3] = 4246189128;  // 0xFD17B448
    gy[4] = 235997352;   // 0x0E1108A8
    gy[5] = 1571093500;  // 0x5DA4FBFC
    gy[6] = 648266853;   // 0x26A3C465
    gy[7] = 1211816567;  // 0x483ADA77
    return gy;
}

/// secp256k1 endomorphism constant beta: cube root of unity in GF(p).
/// beta^3 = 1 mod p. The endomorphism phi(x,y) = (beta*x, y) satisfies phi(P) = lambda*P.
function SECP256K1_BETA(n, k) {
    assert(n == 32 && k == 8);
    var beta[8];
    beta[0] = 1905590766;  // 0x719501EE
    beta[1] = 3241765928;  // 0xC1396C28
    beta[2] = 318081429;   // 0x12F58995
    beta[3] = 2632993141;  // 0x9CF04975
    beta[4] = 2889102569;  // 0xAC3434E9
    beta[5] = 1852065694;  // 0x6E64479E
    beta[6] = 1702627088;  // 0x657C0710
    beta[7] = 2062117419;  // 0x7AE96A2B
    return beta;
}

/// Dummy point: G * 2^255. Used for zero-selection muxing in PrivToPub
/// and as offset point in HintedGLVScalarMult.
function SECP256K1_DUMMY(n, k) {
    assert(n == 32 && k == 8);
    var dummy[2][8];
    dummy[0][0] = 1066132356;
    dummy[0][1] = 3904713220;
    dummy[0][2] = 2736633539;
    dummy[0][3] = 1911294637;
    dummy[0][4] = 1340010610;
    dummy[0][5] = 622515913;
    dummy[0][6] = 736509467;
    dummy[0][7] = 2989985956;
    dummy[1][0] = 3944318990;
    dummy[1][1] = 3507111741;
    dummy[1][2] = 345951064;
    dummy[1][3] = 401605876;
    dummy[1][4] = 2860644677;
    dummy[1][5] = 3906277256;
    dummy[1][6] = 433413851;
    dummy[1][7] = 4234897737;
    return dummy;
}

/// Offset-shifted dummy: [2^64] * SECP256K1_DUMMY = [2^319] * G.
/// Precomputed for MSM(4,64) identity verification in HintedGLVScalarMult.
function SECP256K1_DUMMY_SHIFTED_64(n, k) {
    assert(n == 32 && k == 8);
    var pt[2][8];
    pt[0][0] = 138163804;
    pt[0][1] = 2198444321;
    pt[0][2] = 4141075811;
    pt[0][3] = 30146289;
    pt[0][4] = 37751690;
    pt[0][5] = 1519377485;
    pt[0][6] = 4068463413;
    pt[0][7] = 4181030494;
    pt[1][0] = 2185145513;
    pt[1][1] = 3850043800;
    pt[1][2] = 2080116452;
    pt[1][3] = 818659888;
    pt[1][4] = 454401409;
    pt[1][5] = 727488522;
    pt[1][6] = 690395099;
    pt[1][7] = 598108695;
    return pt;
}
