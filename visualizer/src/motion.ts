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
