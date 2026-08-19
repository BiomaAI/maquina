import { describe, expect, it } from "vitest";
import { clamp01, easeInOutCubic, rollingSpinDirection, transitionProgress } from "./motion";

describe("state transition timing", () => {
  it("clamps animation progress to a single transition", () => {
    expect(transitionProgress(50, 100, 500)).toBe(0);
    expect(transitionProgress(350, 100, 500)).toBe(0.5);
    expect(transitionProgress(900, 100, 500)).toBe(1);
  });

  it("eases from and to zero velocity while preserving the midpoint", () => {
    expect(easeInOutCubic(0)).toBe(0);
    expect(easeInOutCubic(0.25)).toBeCloseTo(0.0625);
    expect(easeInOutCubic(0.5)).toBe(0.5);
    expect(easeInOutCubic(0.75)).toBeCloseTo(0.9375);
    expect(easeInOutCubic(1)).toBe(1);
  });

  it("guards interpolation inputs outside the transition", () => {
    expect(clamp01(-2)).toBe(0);
    expect(clamp01(3)).toBe(1);
  });

  it.each([
    [{ x: 1, y: 0, z: 0 }, { x: 0, y: 1, z: 0 }, { x: 0, y: 0, z: 1 }, -1],
    [{ x: -1, y: 0, z: 0 }, { x: 0, y: 1, z: 0 }, { x: 0, y: 0, z: 1 }, 1],
    [{ x: 0, y: 0, z: 1 }, { x: 0, y: 1, z: 0 }, { x: 1, y: 0, z: 0 }, 1],
  ] as const)(
    "derives rolling spin from travel, ground, and axle orientation",
    (travel, ground, axle, expected) => {
      expect(rollingSpinDirection(travel, ground, axle)).toBe(expected);
    },
  );

  it("rejects an axle that cannot produce the declared travel", () => {
    expect(() => rollingSpinDirection(
      { x: 1, y: 0, z: 0 },
      { x: 0, y: 1, z: 0 },
      { x: 1, y: 0, z: 0 },
    )).toThrow("do not define a rolling direction");
  });
});
