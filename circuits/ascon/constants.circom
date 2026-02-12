pragma circom 2.2.2;

include "ascon/functions.circom";

function ASCON_INITIAL_STATE_HASH_256() {
    return [
        word_2_bits(0x9b1e5494e934d681),
        word_2_bits(0x4bc3a01e333751d2),
        word_2_bits(0xae65396c6b34b81a),
        word_2_bits(0x3c7fd4a4d56a4db3),
        word_2_bits(0x1a5c464906c5976d)
    ];
}

function ASCON_ROUND_CONSTANT(rnd, i) {
    var round_constants[16][8] = [
        byte_2_bits(0x3c),
        byte_2_bits(0x2d),
        byte_2_bits(0x1e),
        byte_2_bits(0x0f),
        byte_2_bits(0xf0),
        byte_2_bits(0xe1),
        byte_2_bits(0xd2),
        byte_2_bits(0xc3),
        byte_2_bits(0xb4),
        byte_2_bits(0xa5),
        byte_2_bits(0x96),
        byte_2_bits(0x87),
        byte_2_bits(0x78),
        byte_2_bits(0x69),
        byte_2_bits(0x5a),
        byte_2_bits(0x4b)
    ];
    return round_constants[16 - rnd + i];
}

function ASCON_LINEAR_DIFFUSION_DISTANCE(i) {
    var diffusion_distances[5][2] = [
        [19, 28],
        [61, 39],
        [1, 6],
        [10, 17],
        [7, 41]
    ];
    return diffusion_distances[i];
}