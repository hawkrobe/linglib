/-!
# Graded Numeral Roundness (k-ness Model)

Framework-agnostic infrastructure for graded numeral roundness,
following Sigurd (1988), Jansen & Pollmann (2001), and Woodin et al. (2024).

A number n has **k-ness** (for k ∈ {2, 2.5, 5, 10}) if n = m × k × 10^b
for some b ≥ 1 and 1 ≤ m ≤ 9.

The 6 properties (ordered by frequency effect, Woodin et al. 2024):
1. 10-ness (β = 4.46) — strongest predictor of frequency
2. 2.5-ness (β = 3.84)
3. 5-ness (β = 2.61)
4. 2-ness (β = 1.56)
5. Multiple of 10 (β = 0.52)
6. Multiple of 5 (β = 0.06) — weakest predictor

This module lives in Core because both Phenomena (empirical data) and
Theories (Semantics.Montague, NeoGricean, RSA) depend on the roundness
score, avoiding a cross-layer Theories→Phenomena import.

## References

- Sigurd (1988). Round numbers.
- Jansen & Pollmann (2001). On round numbers.
- Woodin, Winter & Bhatt (2024). Numeral frequency and roundness.
- Krifka (2007). Approximate interpretation of number words.
-/

namespace Core.Roundness

-- ============================================================================
-- k-ness primitives
-- ============================================================================

/-- Check if n has integer k-ness: n = m × k × 10^b for b ≥ 1, 1 ≤ m ≤ 9. -/
def hasIntKness (n : Nat) (k : Nat) : Bool :=
  if n == 0 || k == 0 then false
  else
    List.range 10 |>.any λ i =>
      let b := i + 1
      let divisor := k * 10 ^ b
      n % divisor == 0 && n / divisor ≥ 1 && n / divisor ≤ 9

/-- Check if n has 2.5-ness: n = m × 2.5 × 10^b for b ≥ 1, 1 ≤ m ≤ 9.
    Equivalent to: 2n = m × 5 × 10^b. -/
def has2_5ness (n : Nat) : Bool :=
  if n == 0 then false
  else
    List.range 10 |>.any λ i =>
      let b := i + 1
      let divisor := 5 * 10 ^ b
      (2 * n) % divisor == 0 && (2 * n) / divisor ≥ 1 && (2 * n) / divisor ≤ 9

-- ============================================================================
-- Roundness properties and score
-- ============================================================================

/--
The 6 graded roundness properties from Sigurd/Jansen & Pollmann.

Each field is an independent Boolean property. The number of true
properties predicts numeral frequency (Woodin et al. 2024) and
pragmatic behavior (Cummins 2015).
-/
structure RoundnessProperties where
  multipleOf5 : Bool
  multipleOf10 : Bool
  twoness : Bool
  twoPointFiveness : Bool
  fiveness : Bool
  tenness : Bool
  deriving Repr, DecidableEq, BEq

/-- Compute all 6 roundness properties for a natural number. -/
def roundnessProperties (n : Nat) : RoundnessProperties :=
  { multipleOf5 := n % 5 == 0
  , multipleOf10 := n % 10 == 0
  , twoness := hasIntKness n 2
  , twoPointFiveness := has2_5ness n
  , fiveness := hasIntKness n 5
  , tenness := hasIntKness n 10
  }

/-- Count of true roundness properties (0–6). Higher = rounder. -/
def roundnessScore (n : Nat) : Nat :=
  let rp := roundnessProperties n
  (if rp.multipleOf5 then 1 else 0) +
  (if rp.multipleOf10 then 1 else 0) +
  (if rp.twoness then 1 else 0) +
  (if rp.twoPointFiveness then 1 else 0) +
  (if rp.fiveness then 1 else 0) +
  (if rp.tenness then 1 else 0)

/-- Maximum possible roundness score. -/
def maxRoundnessScore : Nat := 6

-- ============================================================================
-- Roundness grade (binned score)
-- ============================================================================

/--
Binned roundness grade for use in width/tolerance functions.

Collapses the 0–6 score into 4 levels to avoid duplicating
step-function logic across Theory files.
-/
inductive RoundnessGrade where
  | high      -- score ≥ 5 (e.g., 100, 1000, 200)
  | moderate  -- score 3-4 (e.g., 50, 20)
  | low       -- score 1-2 (e.g., 110, 15)
  | none      -- score 0 (e.g., 7, 99)
  deriving Repr, DecidableEq, BEq

/-- Classify a number into a roundness grade. -/
def roundnessGrade (n : Nat) : RoundnessGrade :=
  if roundnessScore n ≥ 5 then .high
  else if roundnessScore n ≥ 3 then .moderate
  else if roundnessScore n ≥ 1 then .low
  else .none

-- ============================================================================
-- Context-sensitive roundness
-- ============================================================================

/--
Count k-ness-like properties relative to a non-standard base.

For base b, checks divisibility by b, 2b, 5b, and 10b — mirroring
the standard k-ness properties but on a different scale.

Examples:
- contextualRoundnessScore 48 12 = 2  (48 ÷ 12 = 4, 48 ÷ 24 = 2)
- contextualRoundnessScore 120 12 = 4 (divides by 12, 24, 60, 120)
-/
def contextualRoundnessScore (n : Nat) (base : Nat) : Nat :=
  if base ≤ 1 || n == 0 then 0
  else
    (if n % base == 0 then 1 else 0) +
    (if n % (base * 2) == 0 then 1 else 0) +
    (if n % (base * 5) == 0 then 1 else 0) +
    (if n % (base * 10) == 0 then 1 else 0)

/--
Context-sensitive roundness: compose default k-ness with a non-standard base.

On a base-12 (dozens) scale, 48 = 4 × 12 is "round" even though its
default k-ness score is 0. On base-60 (minutes), 120 = 2 × 60 is round.

The contextual score derives from actual divisibility properties relative
to the base (not a flat bonus), paralleling how standard k-ness derives
from divisibility by 2/2.5/5/10 × powers of 10.

Composes with `GranularityDatum` in `Phenomena.Imprecision.Numerals`.
-/
def roundnessInContext (n : Nat) (base : Nat) : Nat :=
  max (roundnessScore n) (contextualRoundnessScore n base)

-- ============================================================================
-- Per-datum verification
-- ============================================================================

-- Score verification
#guard roundnessScore 100 == 6
#guard roundnessScore 50 == 4
#guard roundnessScore 7 == 0
#guard roundnessScore 1000 == 6
#guard roundnessScore 200 == 6
#guard roundnessScore 110 == 2
#guard roundnessScore 20 == 3

-- Grade verification
#guard roundnessGrade 100 == .high
#guard roundnessGrade 50 == .moderate
#guard roundnessGrade 110 == .low
#guard roundnessGrade 7 == .none

-- Context-sensitive verification
#guard contextualRoundnessScore 48 12 == 2
#guard contextualRoundnessScore 120 12 == 4
#guard roundnessInContext 48 12 == 2     -- contextual score beats default (0)
#guard roundnessInContext 48 10 == 0     -- not round on base-10
#guard roundnessInContext 100 10 == 6    -- default score beats contextual

theorem roundness_100 : roundnessScore 100 = 6 := by native_decide
theorem roundness_7 : roundnessScore 7 = 0 := by native_decide
theorem roundness_50 : roundnessScore 50 = 4 := by native_decide
theorem roundness_1000 : roundnessScore 1000 = 6 := by native_decide

-- ============================================================================
-- Arithmetic helper: multiples of 10 have score ≥ 2
-- ============================================================================

/-- Multiples of 10 have roundness score ≥ 2 (multipleOf5 + multipleOf10 both true).
    This is the key lemma for all downstream sorry-free proofs. -/
theorem score_ge_two_of_div10 (n : Nat) (h10 : n % 10 = 0) :
    roundnessScore n ≥ 2 := by
  unfold roundnessScore roundnessProperties
  have h5 : n % 5 = 0 := by omega
  simp only [h10, h5, beq_self_eq_true, ite_true]
  omega

/-- Grade is never `.none` when score ≥ 1. -/
theorem grade_ne_none_of_score_ge_one (n : Nat) (h : roundnessScore n ≥ 1) :
    roundnessGrade n ≠ .none := by
  unfold roundnessGrade
  split
  · native_decide
  · split
    · native_decide
    · native_decide

end Core.Roundness
