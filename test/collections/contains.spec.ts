import { assert } from "chai";
import { describe_circuit } from "../helpers.js";

describe_circuit("Contains", {
    contains: { path: "collections/contains.circom", template: "Contains", params: [4, 2] },
}, (calculators) => {
    it("passes when right is subset of left", async () => {
        await calculators.contains.calculate({ left: [1, 2, 3, 4], right: [2, 4] });
    });

    it("skips zero values in right", async () => {
        await calculators.contains.calculate({ left: [1, 2, 3, 4], right: [2, 0] });
    });

    it("fails when right element not in left", async () => {
        try {
            await calculators.contains.calculate({ left: [1, 2, 3, 4], right: [2, 99] });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("passes when both right elements are zero", async () => {
        await calculators.contains.calculate({ left: [1, 2, 3, 4], right: [0, 0] });
    });

    it("passes with duplicate matches in left", async () => {
        await calculators.contains.calculate({ left: [5, 5, 3, 4], right: [5, 3] });
    });
});

describe_circuit("Contains_Points", {
    points: { path: "collections/contains.circom", template: "Contains_Points", params: [3, 2] },
}, (calculators) => {
    const left = [[10, 20], [30, 40], [50, 60]];

    it("passes when right points are subset of left", async () => {
        await calculators.points.calculate({
            left,
            right: [[10, 20], [50, 60]],
        });
    });

    it("skips null sentinel (0,0)", async () => {
        await calculators.points.calculate({
            left,
            right: [[30, 40], [0, 0]],
        });
    });

    it("fails when non-null point not in left", async () => {
        try {
            await calculators.points.calculate({
                left,
                right: [[10, 20], [99, 99]],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("fails when only x matches (partial match)", async () => {
        try {
            await calculators.points.calculate({
                left,
                right: [[10, 99], [30, 40]],
            });
            assert.fail("should have thrown");
        } catch (e: any) {
            assert.notEqual(e.message, "should have thrown");
        }
    });

    it("passes with all null sentinels", async () => {
        await calculators.points.calculate({
            left,
            right: [[0, 0], [0, 0]],
        });
    });
});
