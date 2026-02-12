pragma circom 2.2.2;

include "packing/bitify.circom";

/// Packs flat field elements into packed elements.
/// nElements output elements, each containing itemsPerElement items of bitsPerItem bits.
/// in[nElements * itemsPerElement] → out[nElements]
template Pack_Elements(nElements, itemsPerElement, bitsPerItem) {
    var bitsPerElement = itemsPerElement * bitsPerItem;
    assert(bitsPerElement <= 253);

    var totalItems = nElements * itemsPerElement;

    signal input in[totalItems];
    signal output out[nElements];

    // Decompose each input item to bits (also range-checks each item)
    component toBits[totalItems];
    for (var i = 0; i < totalItems; i++) {
        toBits[i] = Num2BitsLE(bitsPerItem);
        toBits[i].in <== in[i];
    }

    // Concatenate bits within each element and reconstruct
    component fromBits[nElements];
    for (var e = 0; e < nElements; e++) {
        fromBits[e] = Bits2NumLE(bitsPerElement);
        for (var j = 0; j < itemsPerElement; j++) {
            var itemIdx = e * itemsPerElement + j;
            for (var b = 0; b < bitsPerItem; b++) {
                fromBits[e].in[j * bitsPerItem + b] <== toBits[itemIdx].out[b];
            }
        }
        out[e] <== fromBits[e].out;
    }
}

/// Packs pre-decomposed bit arrays into packed elements.
/// in[nElements * itemsPerElement][bitsPerItem] → out[nElements]
template Pack_Elements_FromBits(nElements, itemsPerElement, bitsPerItem) {
    var bitsPerElement = itemsPerElement * bitsPerItem;
    assert(bitsPerElement <= 253);

    var totalItems = nElements * itemsPerElement;

    signal input in[totalItems][bitsPerItem];
    signal output out[nElements];

    component fromBits[nElements];
    for (var e = 0; e < nElements; e++) {
        fromBits[e] = Bits2NumLE(bitsPerElement);
        for (var j = 0; j < itemsPerElement; j++) {
            var itemIdx = e * itemsPerElement + j;
            for (var b = 0; b < bitsPerItem; b++) {
                fromBits[e].in[j * bitsPerItem + b] <== in[itemIdx][b];
            }
        }
        out[e] <== fromBits[e].out;
    }
}

/// Unpacks packed elements into individual field elements.
/// in[nElements] → out[nElements * itemsPerElement]
template Unpack_Elements(nElements, itemsPerElement, bitsPerItem) {
    var bitsPerElement = itemsPerElement * bitsPerItem;
    assert(bitsPerElement <= 253);

    var totalItems = nElements * itemsPerElement;

    signal input in[nElements];
    signal output out[totalItems];

    component toBits[nElements];
    component fromBits[totalItems];

    for (var e = 0; e < nElements; e++) {
        toBits[e] = Num2BitsLE(bitsPerElement);
        toBits[e].in <== in[e];

        for (var j = 0; j < itemsPerElement; j++) {
            var itemIdx = e * itemsPerElement + j;
            fromBits[itemIdx] = Bits2NumLE(bitsPerItem);
            for (var b = 0; b < bitsPerItem; b++) {
                fromBits[itemIdx].in[b] <== toBits[e].out[j * bitsPerItem + b];
            }
            out[itemIdx] <== fromBits[itemIdx].out;
        }
    }
}
