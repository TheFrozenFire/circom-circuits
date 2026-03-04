pragma circom 2.2.2;

/// secp256k1 field prime: p = 2^256 - 2^32 - 977.
/// Supports n=64, k=4 (4 × 64-bit limbs, little-endian).
function SECP256K1_PRIME(n, k) {
    assert(n == 64 && k == 4);
    var p[4];
    p[0] = 18446744069414583343; // 0xFFFFFFFEFFFFFC2F
    p[1] = 18446744073709551615; // 0xFFFFFFFFFFFFFFFF
    p[2] = 18446744073709551615;
    p[3] = 18446744073709551615;
    return p;
}

/// secp256k1 curve group order.
function SECP256K1_ORDER(n, k) {
    assert(n == 64 && k == 4);
    var order[4];
    order[0] = 13822214165235122497; // 0xBFD25E8CD0364141
    order[1] = 13451932020343611451; // 0xBAAEDCE6AF48A03B
    order[2] = 18446744073709551614; // 0xFFFFFFFFFFFFFFFE
    order[3] = 18446744073709551615; // 0xFFFFFFFFFFFFFFFF
    return order;
}

/// secp256k1 generator x-coordinate.
function SECP256K1_GX(n, k) {
    assert(n == 64 && k == 4);
    var gx[4];
    gx[0] = 6481385041966929816;  // 0x59F2815B16F81798
    gx[1] = 188021827762530521;   // 0x029BFCDB2DCE28D9
    gx[2] = 6170039885052185351;  // 0x55A06295CE870B07
    gx[3] = 8772561819708210092;  // 0x79BE667EF9DCBBAC
    return gx;
}

/// secp256k1 generator y-coordinate.
function SECP256K1_GY(n, k) {
    assert(n == 64 && k == 4);
    var gy[4];
    gy[0] = 11261198710074299576; // 0x9C47D08FFB10D4B8
    gy[1] = 18237243440184513561; // 0xFD17B448A6855419
    gy[2] = 6747795201694173352;  // 0x5DA4FBFC0E1108A8
    gy[3] = 5204712524664259685;  // 0x483ADA7726A3C465
    return gy;
}

/// Dummy point: G * 2^255. Used for zero-selection muxing in PrivToPub.
/// This point will never appear as a legitimate partial sum.
function SECP256K1_DUMMY(n, k) {
    assert(n == 64 && k == 4);
    var dummy[2][4];
    dummy[0][0] = 16770615581224985476;
    dummy[0][1] = 8208947961671825091;
    dummy[0][2] = 2673685488914591858;
    dummy[0][3] = 12841891897255804443;
    dummy[1][0] = 15062930234956941326;
    dummy[1][1] = 1724884103647382360;
    dummy[1][2] = 16777333066489264453;
    dummy[1][3] = 18188747282752823003;
    return dummy;
}
