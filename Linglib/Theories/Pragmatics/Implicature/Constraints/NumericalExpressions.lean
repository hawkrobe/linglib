import Linglib.Core.Scales.Roundness
import Linglib.Core.Order.Satisfaction
import Linglib.Core.Order.FeaturePreorder
import Linglib.Core.Constraint.Pareto
import Linglib.Theories.Pragmatics.Implicature.Core.Markedness

/-!
# OT Constraints for Numerical Expressions
@cite{cummins-2015}

Optimality-Theoretic constraint system for numeral production. Speakers
choose among candidate numeral expressions by trading off four constraints:

1. **INFO** (informativeness): prefer smaller admitted set
2. **Granularity**: match contextual precision level
3. **QSIMP** (quantifier simplicity): prefer bare numerals
4. **NSAL** (numeral salience): prefer round/salient numerals

The empirical bridge to the k-ness model is `nsalViolations`: NSAL
violations equal `maxRoundnessScore - roundnessScore(n)`, so rounder
numbers incur fewer NSAL violations.

## Architecture

A `ViolationProfile` is `Core.Constraint.Profile Nat 4` (i.e. `Fin 4 → Nat`),
matching the codebase's standard violation-profile abstraction. Profile
indices fix the constraint order: 0 = INFO, 1 = Granularity, 2 = QSIMP,
3 = NSAL.

Two preorders on profiles are exposed, both as `Core.Order.FeaturePreorder`
instances so they fit the schema established in `Core/Constraint/Pareto.lean`:

| view              | feature                          | feature-space order |
|-------------------|----------------------------------|---------------------|
| `paretoPreorder`  | `id : ViolationProfile → ViolationProfile` | pointwise `≤` |
| `qualPreorder`    | `violatedSetOf : … → Finset (Fin 4)` | subset `⊆` |

`paretoPreorder_le_implies_qualPreorder_le` is a one-line application of
`FeaturePreorder.coarsen_via_monotone` with `violatedSetOf` as the
connecting monotone map. The legacy criterion-based view via
`SatisfactionOrdering` is preserved as `cumminsOrdering`.

RSA-cost normalization (`nsalAsRSACost`) and enrichment-width predictions
(`enrichmentWidth`) live in `Phenomena/Numerals/Compare.lean` rather than
here, since they are framework bridges rather than OT constraint
definitions.
-/

namespace Implicature.Constraints.NumericalExpressions

open Core.Roundness
open Core.Constraint (Profile)
open Core.Order (FeaturePreorder SatisfactionOrdering)

-- ============================================================================
-- § 1: Numeral candidates
-- ============================================================================

/-- Form of the numeral expression. Bare numerals are simplest; modified
    forms add complexity (and pay a QSIMP cost). -/
inductive QuantifierForm where
  | bare        -- "100"
  | modified    -- "about 100", "approximately 100"
  | interval    -- "between 90 and 110"
  deriving Repr, DecidableEq

/-- A candidate numeral expression for OT evaluation. -/
structure NumeralCandidate where
  numeral : Nat
  form : QuantifierForm
  contextGranularity : Nat
  deriving Repr

/-- Infer granularity from a numeral's trailing zeros: 100 → 2, 110 → 1, 111 → 0. -/
def inferGranularity (n : Nat) : Nat :=
  if n == 0 then 0
  else if n % 1000 == 0 then 3
  else if n % 100 == 0 then 2
  else if n % 10 == 0 then 1
  else 0

-- ============================================================================
-- § 2: Per-constraint violation functions
-- ============================================================================

/-- INFO: violations = `|admittedSet| - 1`. Less informative expressions
    (which admit more values) incur more violations. -/
def infoViolations (admittedCount : Nat) : Nat :=
  admittedCount - 1

/-- Granularity: violations = `|contextGranularity − utteranceGranularity|`. -/
def granularityViolations (contextGranularity uttGranularity : Nat) : Nat :=
  if contextGranularity ≥ uttGranularity
  then contextGranularity - uttGranularity
  else uttGranularity - contextGranularity

/-- QSIMP: bare = 0, modified = 1, interval = 2. -/
def qsimpViolations : QuantifierForm → Nat
  | .bare     => 0
  | .modified => 1
  | .interval => 2

/-- NSAL: violations = `maxRoundnessScore - roundnessScore(n)`. Maximally
    round numbers (score 6) → 0; non-round (score 0) → 6. The complement
    of the graded roundness score, which is the load-bearing connection
    between the OT account and the k-ness model. -/
def nsalViolations (n : Nat) : Nat :=
  maxRoundnessScore - roundnessScore n

/-- NSAL violations are the complement of roundness score. -/
theorem nsal_is_complement (n : Nat) (h : roundnessScore n ≤ maxRoundnessScore) :
    nsalViolations n + roundnessScore n = maxRoundnessScore := by
  unfold nsalViolations maxRoundnessScore at *
  omega

/-- A rounder numeral always has fewer NSAL violations. -/
theorem round_beats_nonround_nsal (n₁ n₂ : Nat)
    (h : roundnessScore n₁ > roundnessScore n₂)
    (h1 : roundnessScore n₁ ≤ maxRoundnessScore)
    (h2 : roundnessScore n₂ ≤ maxRoundnessScore) :
    nsalViolations n₁ < nsalViolations n₂ := by
  unfold nsalViolations
  omega

#guard nsalViolations 100 == 0    -- maximally round → 0 violations
#guard nsalViolations 1000 == 0   -- maximally round → 0 violations
#guard nsalViolations 7 == 6      -- non-round → 6 violations
#guard nsalViolations 50 == 2     -- moderately round → 2 violations
#guard nsalViolations 110 == 4    -- slightly round → 4 violations

-- ============================================================================
-- § 3: ViolationProfile as Profile Nat 4
-- ============================================================================

/-- A `ViolationProfile` is a `Profile Nat 4` — a 4-vector of violation
    counts indexed by `Fin 4`. Index order: 0 = INFO, 1 = Granularity,
    2 = QSIMP, 3 = NSAL. Reusing `Core.Constraint.Profile` means the
    abstractions in `Core/Constraint/Pareto.lean` (Pareto preorder,
    qualitative coarsening, `coarsen_via_monotone`) apply directly without
    an extra projection layer. -/
abbrev ViolationProfile : Type := Profile Nat 4

/-- Compute the violation profile for a candidate. Indices: 0 = INFO,
    1 = Granularity, 2 = QSIMP, 3 = NSAL. -/
def violationProfile (c : NumeralCandidate) (admittedCount : Nat) : ViolationProfile
  | 0 => infoViolations admittedCount
  | 1 => granularityViolations c.contextGranularity (inferGranularity c.numeral)
  | 2 => qsimpViolations c.form
  | 3 => nsalViolations c.numeral

-- ============================================================================
-- § 4: Pareto + qualitative FeaturePreorders
--
--   Both are direct applications of the schema in `Core/Constraint/Pareto.lean`,
--   adapted from the `ConstraintSystem`-flavoured form to a standalone-profile
--   form (since here we order profiles directly, not candidates).
-- ============================================================================

/-- **Pointwise Pareto preorder on violation profiles** as a `FeaturePreorder`
    with the identity feature: `v ≤ v'` iff every component of `v` is `≤` the
    corresponding component of `v'`. The partial-order *backbone* that lex-OT
    extends; lex breaks ties using the constraint ranking. -/
def paretoPreorder : FeaturePreorder ViolationProfile ViolationProfile :=
  FeaturePreorder.ofFeature id (fun a a' =>
    show Decidable (∀ i, a i ≤ a' i) from inferInstance)

/-- **Qualitative coarsening as a `FeaturePreorder`**: feature is the set of
    violated constraint indices, feature-space order is `Finset.⊆`. The
    underlying preorder is identical in extension to `cumminsOrdering`'s, but
    presented as a feature pullback so the same `coarsen_via_monotone` schema
    applies. -/
def qualPreorder : FeaturePreorder ViolationProfile (Finset (Fin 4)) :=
  FeaturePreorder.ofFeature
    Core.Constraint.ConstraintSystem.violatedSetOf
    (fun _ _ => inferInstance)

/-- **Pointwise dominance ⇒ qualitative dominance.** A one-line corollary of
    `FeaturePreorder.coarsen_via_monotone` with the violated-index extractor
    as the connecting monotone map — identical in shape to
    `paretoFeaturePreorder_le_implies_qualitativeFeaturePreorder_le` in
    `Core/Constraint/Pareto.lean`. -/
theorem paretoPreorder_le_implies_qualPreorder_le
    {v v' : ViolationProfile} (h : paretoPreorder.le v v') :
    qualPreorder.le v v' :=
  FeaturePreorder.coarsen_via_monotone
    paretoPreorder qualPreorder
    Core.Constraint.ConstraintSystem.violatedSetOf
    (Core.Constraint.ConstraintSystem.violatedSetOf_monotone (fun _ => Nat.zero_le _))
    (fun _ => rfl) h

-- ============================================================================
-- § 5: Bridge to SatisfactionOrdering (legacy criterion-based view)
-- ============================================================================

/-- The four OT constraints as a criterion type. Field order matches
    `ViolationProfile` indices (info ↔ 0, …, nsal ↔ 3). -/
inductive NumeralConstraint where
  | info | granularity | qsimp | nsal
  deriving Repr, DecidableEq

/-- Coarse-grain a violation profile: a constraint is "satisfied" iff it
    has 0 violations. Bool-valued for `SatisfactionOrdering`. -/
def constraintSatisfied (v : ViolationProfile) : NumeralConstraint → Bool
  | .info        => v 0 == 0
  | .granularity => v 1 == 0
  | .qsimp       => v 2 == 0
  | .nsal        => v 3 == 0

/-- A `SatisfactionOrdering` over violation profiles using the four
    @cite{cummins-2015} constraints. Coarsens the OT system: a candidate
    "satisfies" a constraint iff it incurs 0 violations. The resulting
    ordering is weaker than lex-OT (which discriminates by violation
    degree) but captures the structural backbone: a candidate that
    satisfies a strict superset of constraints is always OT-preferred. -/
def cumminsOrdering : SatisfactionOrdering ViolationProfile NumeralConstraint :=
  SatisfactionOrdering.ofCriteria constraintSatisfied
    [.info, .granularity, .qsimp, .nsal]

/-- A candidate with zero violations everywhere is at-least-as-good as any
    other under the satisfaction ordering. -/
theorem zero_violations_best (v : ViolationProfile) :
    cumminsOrdering.le (fun _ => 0) v := by
  intro p _
  cases p <;> rfl

end Implicature.Constraints.NumericalExpressions
