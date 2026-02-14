pragma circom 2.2.2;

include "core/comparators.circom";

/// Table lookup by index. Selects rows from in[rows][cells] where in[j][0] == index[i].
/// Missing index yields a row of zeros. rows * count IsEqual + rows * count * cells quadratic.
template IndexSelector(rows, cells, count) {
    signal input in[rows][cells];
    signal input index[count];
    signal output out[count][cells];

    component eq[count][rows];
    signal products[count][rows][cells];

    for (var i = 0; i < count; i++) {
        for (var j = 0; j < rows; j++) {
            eq[i][j] = IsEqual();
            eq[i][j].in[0] <== in[j][0];
            eq[i][j].in[1] <== index[i];

            for (var k = 0; k < cells; k++) {
                products[i][j][k] <== in[j][k] * eq[i][j].out;
            }
        }

        for (var k = 0; k < cells; k++) {
            var sum = 0;
            for (var j = 0; j < rows; j++) {
                sum += products[i][j][k];
            }
            out[i][k] <== sum;
        }
    }
}
