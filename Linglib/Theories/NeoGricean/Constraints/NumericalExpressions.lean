import Linglib.Core.Roundness
import Linglib.Theories.NeoGricean.Core.Markedness
import Mathlib.Data.Rat.Defs

/-!
# OT Constraints for Numerical Expressions (Cummins 2015)

Optimality-Theoretic constraint system for numeral production.
Speakers choose among candidate numeral expressions by optimizing
across four ranked constraints:

1. **INFO** (informativeness): prefer smaller admitted set
2. **Granularity**: match contextual precision level
3. **QSIMP** (quantifier simplicity): prefer bare numerals
4. **NSAL** (numeral salience): prefer round/salient numerals

The key insight connecting to the k-ness model (Phenomena.Imprecision.Numerals):
NSAL violations = maxRoundnessScore - roundnessScore(n).
Rounder numbers incur fewer NSAL violations, making them preferred candidates.

## Connection to RSA

The OT constraints map onto RSA parameters:
- INFO ↔ literal semantics φ (truth-conditional informativeness)
- Granularity ↔ QUD (contextual precision level)
- QSIMP ↔ utterance cost (modifier complexity)
- NSAL ↔ utterance cost (roundness-based salience)

## Connection to C&F 2021

`enrichmentWidth` predicts pragmatic enrichment range width from roundnessScore.
100 (score 6) gets a wider enriched range than 110 (score 2), explaining why
"more than 100" has weaker argumentative strength per C&F's pragmatic reversal.

## References

- Cummins (2015). Constraints on numerical expressions. OUP.
- Cummins & Franke (2021). Rational Speech Acts for numeral enrichment.
- Jansen & Pollmann (2001). On round numbers.
-/

namespace NeoGricean.Constraints.NumericalExpressions

open Core.Roundness

-- ============================================================================
-- Numeral candidate structure
-- ============================================================================

/--
Form of the numeral expression.

Bare numerals are simplest; modified forms add complexity.
-/
inductive QuantifierForm where
  | bare        -- "100"
  | modified    -- "about 100", "approximately 100"
  | interval    -- "between 90 and 110"
  deriving Repr, DecidableEq, BEq

/--
A candidate numeral expression for OT evaluation.
-/
structure NumeralCandidate where
  /-- The numeral used -/
  numeral : Nat
  /-- Actual value being communicated -/
  actualValue : Nat
  /-- Quantifier form -/
  form : QuantifierForm
  /-- Contextual granularity level (trailing zeros in context numeral) -/
  contextGranularity : Nat
  deriving Repr

/--
Infer granularity from a numeral's trailing zeros.

100 → 2 (precision to hundreds)
110 → 1 (precision to tens)
111 → 0 (precision to units)
-/
def inferGranularity (n : Nat) : Nat :=
  if n == 0 then 0
  else if n % 1000 == 0 then 3
  else if n % 100 == 0 then 2
  else if n % 10 == 0 then 1
  else 0

-- ============================================================================
-- The four OT constraints
-- ============================================================================

/--
**INFO** (informativeness): prefer more informative expressions.

Violations = |admitted set| - 1. An expression that admits more values
is less informative and incurs more violations.
-/
def infoViolations (admittedCount : Nat) : Nat :=
  admittedCount - 1

/--
**Granularity**: match the contextual precision level.

Violations = absolute difference between context granularity and
utterance granularity. A granularity mismatch (e.g., saying "100"
when context demands unit precision) is penalized.
-/
def granularityViolations (contextGranularity uttGranularity : Nat) : Nat :=
  if contextGranularity ≥ uttGranularity
  then contextGranularity - uttGranularity
  else uttGranularity - contextGranularity

/--
**QSIMP** (quantifier simplicity): prefer bare numerals.

bare = 0, modified = 1, interval = 2
-/
def qsimpViolations : QuantifierForm → Nat
  | .bare => 0
  | .modified => 1
  | .interval => 2

/--
**NSAL** (numeral salience): prefer round/salient numerals.

Violations = maxRoundnessScore - roundnessScore(n).
Maximally round numbers (score 6) incur 0 violations.
Non-round numbers (score 0) incur 6 violations.

This is the key connection to the k-ness model: NSAL is the complement
of the graded roundness score.
-/
def nsalViolations (n : Nat) : Nat :=
  maxRoundnessScore - roundnessScore n

-- ============================================================================
-- NSAL verification
-- ============================================================================

#guard nsalViolations 100 == 0    -- maximally round → 0 violations
#guard nsalViolations 1000 == 0   -- maximally round → 0 violations
#guard nsalViolations 7 == 6      -- non-round → 6 violations
#guard nsalViolations 50 == 2     -- moderately round → 2 violations
#guard nsalViolations 110 == 4    -- slightly round → 4 violations

theorem nsal_100 : nsalViolations 100 = 0 := by native_decide
theorem nsal_7 : nsalViolations 7 = 6 := by native_decide
theorem nsal_50 : nsalViolations 50 = 2 := by native_decide

/-- NSAL violations are the complement of roundness score. -/
theorem nsal_is_complement (n : Nat) (h : roundnessScore n ≤ maxRoundnessScore) :
    nsalViolations n + roundnessScore n = maxRoundnessScore := by
  unfold nsalViolations maxRoundnessScore at *
  omega

-- ============================================================================
-- OT evaluation
-- ============================================================================

/--
An OT constraint with name, violation function, and rank.

Higher rank = more dominant in the hierarchy.
-/
structure OTConstraint where
  name : String
  rank : Nat
  deriving Repr

/-- The four constraints with default ranking (Cummins 2015). -/
def INFO : OTConstraint := { name := "INFO", rank := 4 }
def GRANULARITY : OTConstraint := { name := "Granularity", rank := 3 }
def QSIMP : OTConstraint := { name := "QSIMP", rank := 2 }
def NSAL : OTConstraint := { name := "NSAL", rank := 1 }

/-- Default ranking: INFO >> Granularity >> QSIMP >> NSAL. -/
def defaultRanking : List OTConstraint :=
  [INFO, GRANULARITY, QSIMP, NSAL]

/--
Violation profile for a candidate: one Nat per constraint, in ranking order.
-/
structure ViolationProfile where
  info : Nat
  granularity : Nat
  qsimp : Nat
  nsal : Nat
  deriving Repr, DecidableEq, BEq

/--
Compute the violation profile for a candidate.
-/
def violationProfile (c : NumeralCandidate) (admittedCount : Nat) : ViolationProfile :=
  { info := infoViolations admittedCount
  , granularity := granularityViolations c.contextGranularity (inferGranularity c.numeral)
  , qsimp := qsimpViolations c.form
  , nsal := nsalViolations c.numeral
  }

/-- Lexicographic comparison of paired violation counts.
    Returns true if the first profile wins at the first point of difference.
    Factored out for provability (e.g., transitivity of harmonic bounding). -/
def lexLessThan : List (Nat × Nat) → Bool
  | [] => false
  | (a, b) :: rest =>
    if a < b then true
    else if a > b then false
    else lexLessThan rest

/--
OT strict domination: v1 harmonically bounds v2 if at the first constraint
where they differ (in ranking order), v1 has fewer violations.
-/
def harmonicallyBounds (v1 v2 : ViolationProfile) : Bool :=
  lexLessThan [(v1.info, v2.info), (v1.granularity, v2.granularity),
               (v1.qsimp, v2.qsimp), (v1.nsal, v2.nsal)]

/--
Select the optimal candidate from a list (first candidate that is not
harmonically bounded by any other).
-/
def optimalCandidate (candidates : List (NumeralCandidate × Nat)) :
    Option NumeralCandidate :=
  let profiles := candidates.map λ (c, admitted) => (c, violationProfile c admitted)
  profiles.find? (λ (_, v1) =>
    profiles.all (λ (_, v2) => v1 == v2 || !harmonicallyBounds v2 v1))
  |>.map Prod.fst

-- ============================================================================
-- Round beats non-round under NSAL
-- ============================================================================

/-- A rounder numeral always has fewer NSAL violations. -/
theorem round_beats_nonround_nsal (n₁ n₂ : Nat)
    (h : roundnessScore n₁ > roundnessScore n₂)
    (h1 : roundnessScore n₁ ≤ maxRoundnessScore)
    (h2 : roundnessScore n₂ ≤ maxRoundnessScore) :
    nsalViolations n₁ < nsalViolations n₂ := by
  unfold nsalViolations
  omega

-- NSAL of 100 vs 110: 100 is strictly better
#guard nsalViolations 100 < nsalViolations 110

-- ============================================================================
-- Enrichment width: k-ness predicts pragmatic enrichment range
-- ============================================================================

/--
Enrichment width: predicted pragmatic enrichment range from roundnessScore.

Connects to CumminsFranke2021.lean's pragmatic enrichment model:
- 100 (score 6) → wider enrichment (±10, 20 total)
- 110 (score 2) → narrower enrichment (±5, 10 total)
- 7 (score 0) → minimal enrichment (±2, 4 total)

This explains why "more than 100" has weaker argumentative strength than
"more than 110" in C&F's pragmatic reversal: 100's wider enrichment
admits more non-goal worlds, diluting its evidential value.
-/
def enrichmentWidth (n : Nat) : Nat :=
  match roundnessGrade n with
  | .high     => 20  -- very round: ±10
  | .moderate => 15  -- moderately round: ±7.5 (rounded)
  | .low      => 10  -- slightly round: ±5
  | .none     => 4   -- non-round: ±2

#guard enrichmentWidth 100 == 20   -- wide enrichment
#guard enrichmentWidth 50 == 15    -- moderate enrichment
#guard enrichmentWidth 110 == 10   -- narrow enrichment
#guard enrichmentWidth 7 == 4      -- minimal enrichment

/-- Rounder M → wider enrichment. -/
theorem rounder_wider_enrichment :
    enrichmentWidth 100 > enrichmentWidth 110 := by native_decide

-- ============================================================================
-- NSAL as normalized RSA cost
-- ============================================================================

/--
NSAL violations as a normalized RSA cost ∈ [0, 1].

This bridges the OT constraint to the RSA cost parameter:
round numerals are "cheap" (cost ≈ 0), non-round are "expensive" (cost ≈ 1).
-/
def nsalAsRSACost (n : Nat) : ℚ :=
  nsalViolations n / maxRoundnessScore

#guard nsalAsRSACost 100 == 0      -- round → free
#guard nsalAsRSACost 7 == 1        -- non-round → maximal cost

/-- Round numerals are cheaper in RSA terms. -/
theorem round_cheaper_in_rsa :
    nsalAsRSACost 100 < nsalAsRSACost 7 := by native_decide

end NeoGricean.Constraints.NumericalExpressions
