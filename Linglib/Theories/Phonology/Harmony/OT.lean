import Linglib.Theories.Phonology.Harmony.Defs
import Linglib.Core.Logic.OT

/-!
# Harmony–OT Bridge
@cite{prince-smolensky-1993} @cite{rose-walker-2011}

Derives OT constraints from a `HarmonySystem`, connecting the direct
computation in `Harmony.Defs` to the OT evaluation framework in
`Core.Logic.OT` and `Phonology.Constraints`.

## Constraints

Given a `HarmonySystem sys`:

- **SPREAD**: markedness — penalizes target segments in the suffix whose
  harmony feature doesn't match the trigger value. Drives harmony.
- **IDENT-[F]**: faithfulness — penalizes input→output changes on the
  harmony feature. Resists harmony.

## Key result

`spreadSuffix_zero_spread`: the output of `spreadSuffix` incurs zero
SPREAD violations (when no blockers intervene). This connects the
algorithmic spreading in `Defs.lean` to its OT motivation: `spreadSuffix`
produces the candidate that satisfies SPREAD, at the cost of IDENT
violations. Under SPREAD ≫ IDENT, the harmonized output is optimal.
-/

namespace Phonology.Harmony

open Phonology (Segment Feature)
open Core.OT

-- ============================================================================
-- § 1: Feature BEq Helper
-- ============================================================================

/-- Feature BEq is reflexive. Needed because `Feature` derives `BEq`
    separately from `DecidableEq`, so `beq_self_eq_true` may not
    fire automatically. -/
private theorem feature_beq_self (f : Feature) : (f == f) = true := by
  cases f <;> rfl

-- ============================================================================
-- § 2: Violation Counting
-- ============================================================================

/-- SPREAD violations: count target segments whose harmony feature value
    doesn't match `triggerVal`. -/
def spreadViolations (sys : HarmonySystem) (triggerVal : Bool)
    (suffix : List Segment) : Nat :=
  suffix.filter (λ s =>
    sys.isTarget s && !((s.spec sys.feature) == some triggerVal)
  ) |>.length

/-- IDENT-[F] violations: count positions where the harmony feature
    changed between input and output. -/
def identViolations (sys : HarmonySystem)
    (input output : List Segment) : Nat :=
  (input.zip output).filter (λ (i, o) =>
    i.spec sys.feature != o.spec sys.feature
  ) |>.length

-- ============================================================================
-- § 3: VH Candidate and Named Constraints
-- ============================================================================

/-- A vowel harmony candidate for OT evaluation.

    The stem is fixed across candidates; only the suffix varies.
    For rightward harmony, GEN produces candidates that differ only in
    the feature values of suffix vowels. The stem determines the trigger
    value; the suffix is the domain of evaluation. -/
structure VHCandidate where
  /-- The stem (unchanged across candidates). -/
  stem : List Segment
  /-- The underlying (input) suffix. -/
  suffixIn : List Segment
  /-- The surface (output) suffix. -/
  suffixOut : List Segment
  deriving DecidableEq

/-- SPREAD as a `NamedConstraint`: penalizes unharmonized targets in the
    output suffix. Returns 0 when the stem has no trigger. -/
def mkSpread (sys : HarmonySystem) :
    NamedConstraint VHCandidate where
  name := "SPREAD"
  family := .markedness
  eval := λ c =>
    match triggerValue sys c.stem with
    | none => 0
    | some val => spreadViolations sys val c.suffixOut

/-- IDENT-[F] as a `NamedConstraint`: penalizes feature changes from
    underlying to surface suffix. -/
def mkIdentHarmony (sys : HarmonySystem) :
    NamedConstraint VHCandidate where
  name := "IDENT"
  family := .faithfulness
  eval := λ c => identViolations sys c.suffixIn c.suffixOut

-- ============================================================================
-- § 4: Per-Segment Properties
-- ============================================================================

/-- After harmonization, a target's harmony feature is set to `val`. -/
theorem harmonizeOne_spec_feature (sys : HarmonySystem) (val : Bool)
    (s : Segment) (ht : sys.isTarget s = true) :
    (harmonizeOne sys val s).spec sys.feature = some val := by
  simp only [harmonizeOne, ht, ↓reduceIte, feature_beq_self]

/-- `harmonizeOne` never creates SPREAD violations: the result either
    has the correct feature value (target case) or isn't a target
    (non-target case, returned unchanged). -/
private theorem harmonizeOne_no_spread (sys : HarmonySystem) (val : Bool)
    (s : Segment) :
    (sys.isTarget (harmonizeOne sys val s) &&
     !((harmonizeOne sys val s).spec sys.feature == some val)) = false := by
  unfold harmonizeOne
  by_cases ht : sys.isTarget s = true
  · simp only [ht, ↓reduceIte, feature_beq_self, beq_self_eq_true,
      Bool.not_true, Bool.and_false]
  · have hf : sys.isTarget s = false := by
      cases h : sys.isTarget s <;> simp_all
    simp only [hf, Bool.false_eq_true, ↓reduceIte, Bool.false_and]

-- ============================================================================
-- § 5: SPREAD Optimality of spreadSuffix
-- ============================================================================

/-- Cons lemma: if the head satisfies SPREAD, the violation count on a
    cons equals the count on the tail. -/
private theorem spreadViolations_cons_ok (sys : HarmonySystem) (val : Bool)
    (s : Segment) (rest : List Segment)
    (hp : (sys.isTarget s && !((s.spec sys.feature) == some val)) = false) :
    spreadViolations sys val (s :: rest) = spreadViolations sys val rest := by
  simp only [spreadViolations, List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]

/-- **`spreadSuffix` produces zero SPREAD violations** (when no blockers
    intervene).

    By induction: `harmonizeOne` fixes each target's feature value
    (§4), so no target in the output disagrees with the trigger. -/
theorem spreadSuffix_zero_spread (sys : HarmonySystem) (val : Bool)
    (suffix : List Segment)
    (h : ∀ s ∈ suffix, sys.isBlocker s = false) :
    spreadViolations sys val (spreadSuffix sys val suffix) = 0 := by
  induction suffix with
  | nil => rfl
  | cons s rest ih =>
    have hs : sys.isBlocker s = false := h s (.head _)
    simp only [spreadSuffix, hs, Bool.false_eq_true, ↓reduceIte]
    rw [spreadViolations_cons_ok sys val _ _ (harmonizeOne_no_spread sys val s)]
    exact ih (λ s' hs' => h s' (.tail _ hs'))

-- ============================================================================
-- § 6: Faithfulness Baseline
-- ============================================================================

/-- The faithful candidate (no changes) has zero IDENT violations. -/
theorem faithful_zero_ident (sys : HarmonySystem) (suffix : List Segment) :
    identViolations sys suffix suffix = 0 := by
  induction suffix with
  | nil => rfl
  | cons s rest ih =>
    unfold identViolations
    simp only [List.zip_cons_cons, List.filter_cons, bne_self_eq_false,
      Bool.false_eq_true, ↓reduceIte]
    change identViolations sys rest rest = 0
    exact ih

/-- IDENT on empty suffixes is zero. -/
theorem identViolations_nil (sys : HarmonySystem) :
    identViolations sys [] [] = 0 := rfl

-- ============================================================================
-- § 7: OT Motivation for spreadSuffix
-- ============================================================================

/-- The output of `spreadSuffix` achieves zero SPREAD violations (the
    `mkSpread` constraint) for the harmonized candidate.

    Combined with `faithful_zero_ident`, this captures the OT trade-off:

    - **Faithful candidate**: SPREAD > 0, IDENT = 0
    - **Harmonized candidate**: SPREAD = 0, IDENT ≥ 0

    Under the ranking SPREAD ≫ IDENT, the harmonized output wins. -/
theorem spreadSuffix_ot_motivation (sys : HarmonySystem)
    (stem suffix : List Segment) (val : Bool)
    (h_no_blockers : ∀ s ∈ suffix, sys.isBlocker s = false)
    (hv : triggerValue sys stem = some val) :
    (mkSpread sys).eval ⟨stem, suffix, spreadSuffix sys val suffix⟩ = 0 := by
  simp only [mkSpread, hv]
  exact spreadSuffix_zero_spread sys val suffix h_no_blockers

end Phonology.Harmony
