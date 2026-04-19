import Linglib.Theories.Phonology.Process.Harmony.OT
import Linglib.Core.Constraint.System
import Linglib.Fragments.Hungarian.VowelHarmony

/-!
# Siptár & Törkenczy (2000): The Phonology of Hungarian
@cite{siptar-torkenczy-2000} @cite{prince-smolensky-1993} @cite{rose-walker-2011}

End-to-end OT analysis of Hungarian vowel harmony, connecting:

1. **Segment features** (`Features.lean`) — Hayes binary feature inventory
2. **Harmony system** (`Harmony.Defs`) — trigger/target/transparent predicates
3. **OT constraints** (`Harmony.OT`) — SPREAD and IDENT derived from
   `HarmonySystem`
4. **Tableaux** (`Core.Logic.OT`) — `mkTableau` + `optimal` select winner
5. **Hungarian fragments** (`Fragments.Hungarian.VowelHarmony`) — concrete
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
open Phonology.Harmony
open Core.OT Core.ConstraintEvaluation
open Fragments.Hungarian.VowelHarmony

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
    @cite{siptar-torkenczy-2000} §3.2.2, class IA-b. -/
theorem ház_back_optimal :
    (mkTableau házCands spreadDominant házCands_ne).optimal
      = {ház_back} := by native_decide

/-- *tűz*: SPREAD ≫ IDENT selects front-harmonized suffix as unique winner.
    @cite{siptar-torkenczy-2000} §3.2.2, class IA-f. -/
theorem tűz_front_optimal :
    (mkTableau tűzCands spreadDominant tűzCands_ne).optimal
      = {tűz_front} := by native_decide

/-- *papír*: neutral /i/ is transparent — back harmony passes through.
    SPREAD ≫ IDENT selects back-harmonized suffix, same as *ház*.
    @cite{siptar-torkenczy-2000} §3.2.2, class IIB-b. -/
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
open Core.Constraint

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
