export function clamp01(value: number): number {
  return Math.max(0, Math.min(1, value));
}

/** A zero-velocity start and finish keeps state changes from looking teleported. */
export function easeInOutCubic(value: number): number {
  const progress = clamp01(value);
  return progress < 0.5
    ? 4 * progress * progress * progress
    : 1 - Math.pow(-2 * progress + 2, 3) / 2;
}

export function transitionProgress(now: number, startsAt: number, duration: number): number {
  if (duration <= 0) return 1;
  return clamp01((now - startsAt) / duration);
}

interface Direction3 {
  x: number;
  y: number;
  z: number;
}

/**
 * A no-slip wheel's angular velocity follows groundNormal × travelDirection.
 * Return its sign along the wheel's declared positive axle.
 */
export function rollingSpinDirection(
  travelDirection: Direction3,
  groundNormal: Direction3,
  axleDirection: Direction3,
): -1 | 1 {
  const angularX = groundNormal.y * travelDirection.z - groundNormal.z * travelDirection.y;
  const angularY = groundNormal.z * travelDirection.x - groundNormal.x * travelDirection.z;
  const angularZ = groundNormal.x * travelDirection.y - groundNormal.y * travelDirection.x;
  const axleAlignment =
    angularX * axleDirection.x + angularY * axleDirection.y + angularZ * axleDirection.z;

  if (Math.abs(axleAlignment) <= Number.EPSILON) {
    throw new Error("travel, ground normal, and axle do not define a rolling direction");
  }
  return axleAlignment < 0 ? -1 : 1;
}
