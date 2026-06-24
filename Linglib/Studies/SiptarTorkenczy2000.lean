import Linglib.Phonology.Subregular.Harmony
import Linglib.Phonology.OptimalityTheory.Correspondence
import Linglib.Phonology.Constraint.Defs
import Linglib.Phonology.OptimalityTheory.Optimality
import Linglib.Phonology.Constraint.System
import Linglib.Fragments.Hungarian.VowelHarmony

/-!
# Siptár & Törkenczy (2000): The Phonology of Hungarian
[siptar-torkenczy-2000] [prince-smolensky-1993] [rose-walker-2011]

End-to-end OT analysis of Hungarian vowel harmony, connecting:

1. **Segment features** (`Feature.lean`) — Hayes binary feature inventory
2. **Harmony system** (`Subregular.Harmony`) — trigger/target/transparent predicates
3. **OT constraints** (below) — SPREAD and IDENT derived from
   `System` (folded in from the former `Harmony/OT.lean`, this file's sole consumer)
4. **Tableaux** (`Constraint`) — `mkTableau` + `optimal` select winner
5. **Hungarian fragments** (`Hungarian.VowelHarmony`) — concrete
   vowel segments and `hungarianPalatalHarmony`

## Key results

- **`ház_back_optimal`**: SPREAD ≫ IDENT selects back-harmonized suffix for
  back-vowel stem *ház* 'house'. The harmonized candidate is the unique winner.
- **`papír_transparency_optimal`**: neutral /i/ in *papír* is transparent —
  `triggerValue` finds /a/, and SPREAD ≫ IDENT selects back harmony.
- **`tűz_front_optimal`**: front-vowel stem *tűz* 'fire' → front harmony.
- **`faithful_wins_reversed`**: under IDENT ≫ SPREAD, the faithful (no-change)
  candidate wins — demonstrating ranking-driven typology.
- **`factorial_two_types`**: the two constraints yield exactly 2 language types
  (harmony vs. no harmony) across all rankings.

## Architecture

Unlike prior OT study files that use enum candidate types (e.g.,
`CoetzeePater2011`), this file uses `VHCandidate` with real `Segment`
lists directly. This is possible because `DecidableEq Segment` (via
exhaustive feature comparison) enables `native_decide` on segment-level
goals. One type system, no enum wrappers.
-/

namespace SiptarTorkenczy2000

open Phonology (Segment Feature)
open Subregular.Harmony
open OptimalityTheory.Correspondence (Corr)
open Constraint OptimalityTheory Core.Optimization Core.Optimization.Evaluation
open Hungarian.VowelHarmony

-- ============================================================================
-- § 0: OT constraints derived from a `System`
--
-- SPREAD (markedness) and IDENT-[F] (faithfulness) for any `System`,
-- plus the `VHCandidate` evaluation type. Folded in from the former
-- `Phonology/Process/Harmony/OT.lean` (this file was its sole consumer).
-- ============================================================================

/-- Feature BEq is reflexive. Needed because `Feature` derives `BEq`
    separately from `DecidableEq`, so `beq_self_eq_true` may not
    fire automatically. -/
private theorem feature_beq_self (f : Feature) : (f == f) = true := by
  cases f <;> rfl

/-- SPREAD violations: count target segments whose harmony feature value
    doesn't match `triggerVal`. -/
def spreadViolations (sys : System) (triggerVal : Bool)
    (suffix : List Segment) : Nat :=
  suffix.filter (λ s =>
    sys.isTarget s && !((s.spec sys.feature) == some triggerVal)
  ) |>.length

/-- IDENT-[F] violations: count positions where the harmony feature
    changed between input and output.

    **Derived from `Corr.identViol`** on the `(false, true)` edge of a
    binary parallel-pair correspondence between the feature-projected
    tiers `input.map (·.spec sys.feature)` and
    `output.map (·.spec sys.feature)`. This structurally identifies
    IDENT-[F] as IDENT-IO of [mccarthy-prince-1995] restricted to
    the harmony feature. -/
def identViolations (sys : System)
    (input output : List Segment) : Nat :=
  (Corr.parallel
    (input.map  (·.spec sys.feature))
    (output.map (·.spec sys.feature))).identViol .lhs .rhs

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
def mkSpread (sys : System) :
    NamedConstraint VHCandidate where
  name := "SPREAD"
  family := .markedness
  eval := λ c =>
    match triggerValue sys c.stem with
    | none => 0
    | some val => spreadViolations sys val c.suffixOut

/-- IDENT-[F] as a `NamedConstraint`: penalizes feature changes from
    underlying to surface suffix. -/
def mkIdentHarmony (sys : System) :
    NamedConstraint VHCandidate where
  name := "IDENT"
  family := .faithfulness
  eval := λ c => identViolations sys c.suffixIn c.suffixOut

/-- After harmonization, a target's harmony feature is set to `val`. -/
theorem harmonizeOne_spec_feature (sys : System) (val : Bool)
    (s : Segment) (ht : sys.isTarget s) :
    (harmonizeOne sys val s).spec sys.feature = some val := by
  simp only [harmonizeOne, if_pos ht, writeFeature, feature_beq_self, if_true]

/-- `harmonizeOne` never creates SPREAD violations: the result either
    has the correct feature value (target case) or isn't a target
    (non-target case, returned unchanged). -/
private theorem harmonizeOne_no_spread (sys : System) (val : Bool)
    (s : Segment) :
    (sys.isTarget (harmonizeOne sys val s) &&
     !((harmonizeOne sys val s).spec sys.feature == some val)) = false := by
  by_cases ht : sys.isTarget s
  · rw [harmonizeOne_spec_feature sys val s ht]; simp
  · rw [harmonizeOne_nontarget ht]; simp [ht]

/-- Cons lemma: if the head satisfies SPREAD, the violation count on a
    cons equals the count on the tail. -/
private theorem spreadViolations_cons_ok (sys : System) (val : Bool)
    (s : Segment) (rest : List Segment)
    (hp : (sys.isTarget s && !((s.spec sys.feature) == some val)) = false) :
    spreadViolations sys val (s :: rest) = spreadViolations sys val rest := by
  simp only [spreadViolations, List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]

/-- **`spreadSuffix` produces zero SPREAD violations** (when no blockers
    intervene). By induction: `harmonizeOne` fixes each target's feature
    value, so no target in the output disagrees with the trigger. -/
theorem spreadSuffix_zero_spread (sys : System) (val : Bool)
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

/-- The faithful candidate (no changes) has zero IDENT violations.
    Derived from `Corr.identity_ident_zero`. -/
theorem faithful_zero_ident (sys : System) (suffix : List Segment) :
    identViolations sys suffix suffix = 0 := by
  show (Corr.identity _).identViol .lhs .rhs = 0
  exact Corr.identity_ident_zero _

/-- IDENT on empty suffixes is zero. -/
theorem identViolations_nil (sys : System) :
    identViolations sys [] [] = 0 := faithful_zero_ident sys []

/-- The output of `spreadSuffix` achieves zero SPREAD violations for the
    harmonized candidate. With `faithful_zero_ident` this captures the OT
    trade-off: the faithful candidate has SPREAD > 0, IDENT = 0; the
    harmonized candidate has SPREAD = 0, IDENT ≥ 0. Under SPREAD ≫ IDENT,
    the harmonized output wins. -/
theorem spreadSuffix_ot_motivation (sys : System)
    (stem suffix : List Segment) (val : Bool)
    (h_no_blockers : ∀ s ∈ suffix, sys.isBlocker s = false)
    (hv : triggerValue sys stem = some val) :
    (mkSpread sys).eval ⟨stem, suffix, spreadSuffix sys val suffix⟩ = 0 := by
  simp only [mkSpread, hv]
  exact spreadSuffix_zero_spread sys val suffix h_no_blockers

-- ============================================================================
-- § 1: Constraint Rankings
-- ============================================================================

/-- SPREAD ≫ IDENT: harmony applies. This is the ranking for Hungarian
    and other suffix-controlled harmony languages. -/
def spreadDominant : List (NamedConstraint VHCandidate) :=
  [mkSpread hungarianPalatalHarmony, mkIdentHarmony hungarianPalatalHarmony]

/-- IDENT ≫ SPREAD: harmony blocked. This ranking produces a language
    without vowel harmony (suffixes surface faithfully). -/
def identDominant : List (NamedConstraint VHCandidate) :=
  [mkIdentHarmony hungarianPalatalHarmony, mkSpread hungarianPalatalHarmony]

-- ============================================================================
-- § 2: Candidates — *ház* 'house' (IA-b: simple back stem)
-- ============================================================================

/-- Faithful candidate: suffix archiphoneU surfaces unchanged. -/
def ház_faithful : VHCandidate :=
  ⟨[a_vowel], [archiphoneU], [archiphoneU]⟩

/-- Back-harmonized candidate: suffix vowel set to [+back]. -/
def ház_back : VHCandidate :=
  ⟨[a_vowel], [archiphoneU], spreadSuffix hungarianPalatalHarmony true [archiphoneU]⟩

/-- Front-harmonized candidate: suffix vowel set to [−back]. -/
def ház_front : VHCandidate :=
  ⟨[a_vowel], [archiphoneU], spreadSuffix hungarianPalatalHarmony false [archiphoneU]⟩

def házCands : List VHCandidate := [ház_faithful, ház_back, ház_front]
theorem házCands_ne : házCands ≠ [] := by simp [házCands]

-- ============================================================================
-- § 3: Candidates — *tűz* 'fire' (IA-f: simple front stem)
-- ============================================================================

def tűz_faithful : VHCandidate :=
  ⟨[ü_vowel], [archiphoneU], [archiphoneU]⟩

def tűz_back : VHCandidate :=
  ⟨[ü_vowel], [archiphoneU], spreadSuffix hungarianPalatalHarmony true [archiphoneU]⟩

def tűz_front : VHCandidate :=
  ⟨[ü_vowel], [archiphoneU], spreadSuffix hungarianPalatalHarmony false [archiphoneU]⟩

def tűzCands : List VHCandidate := [tűz_faithful, tűz_back, tűz_front]
theorem tűzCands_ne : tűzCands ≠ [] := by simp [tűzCands]

-- ============================================================================
-- § 4: Candidates — *papír* 'paper' (IIB-b: transparency test)
-- ============================================================================

def papír_faithful : VHCandidate :=
  ⟨[a_vowel, i_vowel], [archiphoneU], [archiphoneU]⟩

def papír_back : VHCandidate :=
  ⟨[a_vowel, i_vowel], [archiphoneU],
   spreadSuffix hungarianPalatalHarmony true [archiphoneU]⟩

def papír_front : VHCandidate :=
  ⟨[a_vowel, i_vowel], [archiphoneU],
   spreadSuffix hungarianPalatalHarmony false [archiphoneU]⟩

def papírCands : List VHCandidate := [papír_faithful, papír_back, papír_front]
theorem papírCands_ne : papírCands ≠ [] := by simp [papírCands]

-- ============================================================================
-- § 5: Optimality — SPREAD ≫ IDENT (Hungarian ranking)
-- ============================================================================

/-- *ház*: SPREAD ≫ IDENT selects back-harmonized suffix as unique winner.
    [siptar-torkenczy-2000] §3.2.2, class IA-b. -/
theorem ház_back_optimal :
    (mkTableau házCands spreadDominant házCands_ne).optimal
      = {ház_back} := by native_decide

/-- *tűz*: SPREAD ≫ IDENT selects front-harmonized suffix as unique winner.
    [siptar-torkenczy-2000] §3.2.2, class IA-f. -/
theorem tűz_front_optimal :
    (mkTableau tűzCands spreadDominant tűzCands_ne).optimal
      = {tűz_front} := by native_decide

/-- *papír*: neutral /i/ is transparent — back harmony passes through.
    SPREAD ≫ IDENT selects back-harmonized suffix, same as *ház*.
    [siptar-torkenczy-2000] §3.2.2, class IIB-b. -/
theorem papír_transparency_optimal :
    (mkTableau papírCands spreadDominant papírCands_ne).optimal
      = {papír_back} := by native_decide

-- ============================================================================
-- § 6: Optimality — IDENT ≫ SPREAD (No-Harmony Language)
-- ============================================================================

/-- Under IDENT ≫ SPREAD, the faithful candidate wins — no harmony applies.
    This is the predicted grammar for a language without vowel harmony. -/
theorem faithful_wins_reversed :
    (mkTableau házCands identDominant házCands_ne).optimal
      = {ház_faithful} := by native_decide

-- ============================================================================
-- § 7: Factorial Typology
-- ============================================================================

/-- Two constraints produce exactly 2 distinct language types across all
    rankings: harmony (SPREAD ≫ IDENT) vs. no harmony (IDENT ≫ SPREAD).
    This matches the typological prediction: suffix harmony is either
    present or absent, with no intermediate grammars. -/
theorem factorial_two_types :
    mkFactorialTypologySize házCands
      [mkSpread hungarianPalatalHarmony, mkIdentHarmony hungarianPalatalHarmony]
      házCands_ne = 2 := by native_decide

-- ============================================================================
-- § 8: Grounding — OT Matches Direct Computation
-- ============================================================================

/-- The OT-optimal candidate for *ház* is identical to the output of
    `spreadSuffix` — the direct computation and the OT analysis agree. -/
theorem ház_ot_matches_direct :
    (mkTableau házCands spreadDominant házCands_ne).optimal
      = {⟨[a_vowel], [archiphoneU],
          spreadSuffix hungarianPalatalHarmony true [archiphoneU]⟩} := by
  native_decide

/-- The OT-optimal candidate for *papír* matches `spreadSuffix` with
    the trigger value extracted from the stem. Transparency is derived:
    `triggerValue` skips neutral /i/ and finds /a/. -/
theorem papír_ot_matches_direct :
    (mkTableau papírCands spreadDominant papírCands_ne).optimal
      = {⟨[a_vowel, i_vowel], [archiphoneU],
          spreadSuffix hungarianPalatalHarmony true [archiphoneU]⟩} := by
  native_decide

-- ============================================================================
-- § 9: Generic ConstraintSystem Predictions
-- ============================================================================

/-! Hungarian vowel harmony as a generic `ConstraintSystem` via `tableauSystem`.
The same softmax-based phonology studies in this directory and the OT studies
here both expose `predict : Cand → ℝ`; for the deterministic OT case,
`predict winner = 1` and `predict loser = 0`. -/

section PredictAPI
open Core.Optimization Constraint

/-- *ház* SPREAD ≫ IDENT tableau as a generic `ConstraintSystem`. -/
noncomputable def házSystem : ConstraintSystem VHCandidate (LexProfile Nat 2) :=
  tableauSystem (mkTableau házCands spreadDominant házCands_ne)

/-- The OT prediction lifts to a probability claim: under SPREAD ≫ IDENT,
    the back-harmonized candidate is assigned probability 1. -/
theorem házSystem_predict_back :
    házSystem.predict ház_back = 1 :=
  tableauSystem_predict_unique_winner _ _ ház_back_optimal

/-- And the faithful loser is assigned probability 0. -/
theorem házSystem_predict_faithful_zero :
    házSystem.predict ház_faithful = 0 :=
  tableauSystem_predict_loser _ _ _
    (by unfold ház_faithful ház_back; decide) ház_back_optimal

/-- *tűz* under SPREAD ≫ IDENT: front-harmonized winner gets probability 1. -/
noncomputable def tűzSystem : ConstraintSystem VHCandidate (LexProfile Nat 2) :=
  tableauSystem (mkTableau tűzCands spreadDominant tűzCands_ne)

theorem tűzSystem_predict_front :
    tűzSystem.predict tűz_front = 1 :=
  tableauSystem_predict_unique_winner _ _ tűz_front_optimal

end PredictAPI

end SiptarTorkenczy2000
