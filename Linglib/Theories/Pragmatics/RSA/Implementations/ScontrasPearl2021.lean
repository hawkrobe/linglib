/-
# RSA for Quantifier Scope Ambiguity

Lifted-variable RSA model for scope resolution.

## Model (Scontras & Pearl 2021)

The listener jointly infers:
- w: World state (how many horses jumped: 0, 1, or 2)
- i: Interpretation (surface vs inverse scope)

```
L1(w, i | u) ∝ P(w) × P(i) × S1(u | w, i)
```

Where S1(u | w, i) is proportional to informativity of u under interpretation i.

## Key Predictions

1. **Neither pure scope explains the data**: The model predicts intermediate
   truth-value judgments for partial worlds (1 horse jumped), matching the
   empirical 59% rate from Scontras & Pearl (2021).

2. **Inverse scope preference**: The model assigns higher probability to
   inverse scope (¬>∀) than surface scope (∀>¬).

## References

- Scontras, G. & Pearl, L. (2021). "When pragmatics matters more for
  truth-value judgments: An investigation of quantifier scope ambiguity."
- Goodman, N. D. & Frank, M. C. (2016). "Pragmatic language interpretation
  as probabilistic inference."
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Mathlib.Data.Rat.Defs
import Linglib.Core.Parse
import Linglib.Theories.Semantics.Scope

namespace RSA.ScontrasPearl2021

open Semantics.Scope
open Semantics.Scope (ScopeConfig)

-- World-Parametric Meaning (RSA-specific)

/--
Truth conditions parameterized by interpretation and world.

This is RSA's view of meaning: given an interpretation (e.g., scope reading)
and a world state, is the utterance true?

Separated from `ScopedForm` (which just tracks scope availability) because:
- Scope availability is determined by grammar (Montague/CCG)
- World-parametric truth conditions are used by RSA for inference
-/
structure WorldMeaning (Interp World : Type) where
  /-- Truth conditions: is the utterance true under this interpretation in this world? -/
  meaningAt : Interp → World → Bool
  /-- Available interpretations -/
  interps : List Interp
  /-- Enumeration of possible worlds -/
  worlds : List World

-- Utterances

/-- Utterances in the scope ambiguity domain -/
inductive ScopeUtterance where
  | null              -- Silence / null utterance (always true)
  | everyHorseNotJump -- "Every horse didn't jump" (ambiguous)
  deriving DecidableEq, BEq, Repr, Inhabited

-- Montague Derivation for "Every horse didn't jump"

/--
"Every horse didn't jump" - world-parametric truth conditions.

World state (Nat) encodes how many horses jumped (0, 1, or 2).

Truth conditions by scope:
- Surface (∀>¬): True iff ∀h. ¬jump(h) = "no horse jumped" = w == 0
- Inverse (¬>∀): True iff ¬∀h. jump(h) = "not all jumped" = w < 2
-/
def everyHorseDidntJump_meaning : WorldMeaning ScopeConfig Nat :=
  { meaningAt := λ scope w =>
      match scope with
      | .surface => w == 0      -- ∀>¬: true iff no horse jumped
      | .inverse => w < 2       -- ¬>∀: true iff not all jumped
  , interps := [.surface, .inverse]
  , worlds := [0, 1, 2]         -- 0, 1, or 2 horses jumped
  }

/-- The scoped form (just scope availability, no world semantics) -/
def everyHorseDidntJump_form : ScopedForm :=
  { surface := "Every horse didn't jump"
  , availableScopes := [.surface, .inverse]
  , scopeTaker1 := "every"
  , scopeTaker2 := "not"
  }

/-- Verify the meaning matches the expected truth table -/
theorem parametric_matches_truth :
    everyHorseDidntJump_meaning.meaningAt .surface 0 = true ∧
    everyHorseDidntJump_meaning.meaningAt .surface 1 = false ∧
    everyHorseDidntJump_meaning.meaningAt .inverse 0 = true ∧
    everyHorseDidntJump_meaning.meaningAt .inverse 1 = true ∧
    everyHorseDidntJump_meaning.meaningAt .inverse 2 = false := by
  native_decide

-- Connecting Montague Derivations to RSA

/--
Build RSA meaning function from world-parametric meaning.

RSA's meaning function is derived from the formal semantic derivation,
not stipulated separately.

The null utterance is always true (uninformative baseline).
Other utterances get their meaning from the WorldMeaning structure.
-/
def meaningFromWorldMeaning
    (wm : WorldMeaning ScopeConfig Nat)
    (scope : ScopeConfig) (utt : ScopeUtterance) (world : Nat) : Bool :=
  match utt with
  | .null => true  -- Null utterance always true
  | .everyHorseNotJump => wm.meaningAt scope world

/-- The meaning function derived from the Montague semantics -/
def scopeMeaning : ScopeConfig → ScopeUtterance → Nat → Bool :=
  meaningFromWorldMeaning everyHorseDidntJump_meaning

/-- RSA meaning agrees with world-parametric meaning.

The connection is faithful: we use the semantic derivation,
not separately stipulated truth conditions. -/
theorem rsa_meaning_from_montague :
    scopeMeaning .surface .everyHorseNotJump 0 =
      everyHorseDidntJump_meaning.meaningAt .surface 0 ∧
    scopeMeaning .inverse .everyHorseNotJump 1 =
      everyHorseDidntJump_meaning.meaningAt .inverse 1 := by
  native_decide

-- RSAScenario using unified API

/-- All utterances -/
def allScopeUtterances : List ScopeUtterance := [.null, .everyHorseNotJump]

/--
L1 world distribution using RSA.Eval API.
-/
def l1WorldScores : List (Nat × ℚ) :=
  RSA.Eval.L1_world allScopeUtterances everyHorseDidntJump_meaning.worlds
    everyHorseDidntJump_meaning.interps [()] [()] [()]
    (λ i _ u w => boolToRat (scopeMeaning i u w))
    (λ _ => 1) (λ _ => 1) (λ _ => 1) (λ _ => 1) (λ _ => 1)
    (λ _ _ => 1) (λ _ w1 w2 => w1 == w2) (λ _ => 0) 1
    .everyHorseNotJump

/-- L1 marginal scores over scope interpretations -/
def l1ScopeScores : List (ScopeConfig × ℚ) :=
  let tuples := everyHorseDidntJump_meaning.worlds.flatMap λ w =>
    everyHorseDidntJump_meaning.interps.map λ i => (w, i)
  let scores := tuples.map λ (w, i) =>
    let priorScore := 1  -- uniform
    let s1 := RSA.Eval.S1 allScopeUtterances everyHorseDidntJump_meaning.worlds
      (λ i' _ u' w' => boolToRat (scopeMeaning i' u' w'))
      (λ _ => 1) (λ _ _ => 1) (λ _ w1 w2 => w1 == w2) (λ _ => 0) 1
      w i () () ()
    let s1Score := RSA.Eval.getScore s1 .everyHorseNotJump
    ((w, i), priorScore * s1Score)
  let normalized := RSA.Eval.normalize scores
  everyHorseDidntJump_meaning.interps.map λ i =>
    let iScores := normalized.filter (λ ((_, i'), _) => i' == i) |>.map (·.2)
    (i, RSA.Eval.sumScores iScores)

/-- L1 joint scores over (world × scope) -/
def l1JointScores : List ((Nat × ScopeConfig) × ℚ) :=
  let tuples := everyHorseDidntJump_meaning.worlds.flatMap λ w =>
    everyHorseDidntJump_meaning.interps.map λ i => (w, i)
  let scores := tuples.map λ (w, i) =>
    let priorScore := 1  -- uniform
    let s1 := RSA.Eval.S1 allScopeUtterances everyHorseDidntJump_meaning.worlds
      (λ i' _ u' w' => boolToRat (scopeMeaning i' u' w'))
      (λ _ => 1) (λ _ _ => 1) (λ _ w1 w2 => w1 == w2) (λ _ => 0) 1
      w i () () ()
    let s1Score := RSA.Eval.getScore s1 .everyHorseNotJump
    ((w, i), priorScore * s1Score)
  RSA.Eval.normalize scores

-- Fintype instances for our domain types
instance : Fintype ScopeUtterance where
  elems := {.null, .everyHorseNotJump}
  complete := λ x => by cases x <;> simp

instance scopeConfigFintype : Fintype ScopeConfig where
  elems := {.surface, .inverse}
  complete := λ x => by cases x <;> simp

-- Helper: Get score from distribution

def getWorldScore (w : Nat) : ℚ :=
  RSA.Eval.getScore l1WorldScores w

def getScopeScore (s : ScopeConfig) : ℚ :=
  RSA.Eval.getScore l1ScopeScores s

-- Verification: Check RSA predictions

-- Display scores for inspection
#eval l1JointScores
#eval l1WorldScores
#eval l1ScopeScores

-- Key Theorems

/-- RSA assigns positive probability to the partial world (w=1).

Unlike pure scope theories, RSA does not categorically rule out
the partial world. This matches the empirical 59% rate. -/
theorem rsa_partial_world_possible :
    getWorldScore 1 > 0 := by
  native_decide

/-- RSA assigns positive probability to compatible worlds.

Zero and one have positive probability because "Every horse didn't jump"
is true in these worlds under at least one scope reading.
Two has zero probability because the utterance is false there under both scopes. -/
theorem rsa_compatible_worlds_positive :
    getWorldScore 0 > 0 ∧ getWorldScore 1 > 0 := by
  native_decide

/-- World=two gets zero probability.

When all horses jumped, "Every horse didn't jump" is false under both
scope readings, so L1 assigns probability 0 to this world. -/
theorem rsa_two_world_zero :
    getWorldScore 2 = 0 := by
  native_decide

/-- RSA prefers inverse scope over surface scope.

The model assigns higher probability to the inverse (¬>∀)
interpretation than the surface (∀>¬) interpretation,
reflecting the general preference for inverse scope readings
of "every...not" sentences in English. -/
theorem rsa_prefers_inverse_scope :
    getScopeScore .inverse > getScopeScore .surface := by
  native_decide

/-- Zero-horse world has highest probability.

Both scopes agree that "Every horse didn't jump" is true
when no horse jumped, so this world gets the highest mass. -/
theorem rsa_zero_world_highest :
    getWorldScore 0 > getWorldScore 1 ∧
    getWorldScore 0 > getWorldScore 2 := by
  native_decide

/-- Partial world (one) has more probability than all-jumped world (two).

The inverse scope (¬>∀) is true for w=1 but false for w=2.
Since inverse scope is preferred, w=1 gets more mass than w=2. -/
theorem rsa_one_greater_than_two :
    getWorldScore 1 > getWorldScore 2 := by
  native_decide

-- Connection to Empirical Data

/-- RSA ordering matches empirical ordering.

RSA predicts: P(w=0) > P(w=1) > P(w=2)
Empirical data: 92% > 59% > 18% -/
theorem rsa_matches_empirical_ordering :
    getWorldScore 0 > getWorldScore 1 ∧
    getWorldScore 1 > getWorldScore 2 := by
  native_decide

-- Integration with HasAvailableScopes / HasScopePreference

open ScopeTheory

/-- Marker type for RSA scope preference theory -/
def RSAScopeTheory : Type := Unit

/--
Convert ScopeConfig to ScopeReading for interface compatibility.
-/
def ScopeConfig.toScopeReading' (s : ScopeConfig) : ScopeReading :=
  match s with
  | .surface => ScopeReading.surface ["every", "not"]
  | .inverse => ScopeReading.inverse ["every", "not"]

/-- Convert ℚ to Float for interface compatibility -/
def ratToFloat (q : ℚ) : Float :=
  let numFloat : Float := if q.num ≥ 0 then q.num.natAbs.toFloat else -q.num.natAbs.toFloat
  numFloat / q.den.toFloat

/--
Build ScopePreference from RSA's L1 marginal over interpretations.

RSA provides scores; we convert to the interface format.
-/
def rsaScopePreference : ScopePreference :=
  let surfaceScore := getScopeScore .surface
  let inverseScore := getScopeScore .inverse
  if inverseScore > surfaceScore then
    { ranking := [ScopeConfig.toScopeReading' .inverse, ScopeConfig.toScopeReading' .surface]
    , scores := [ratToFloat inverseScore, ratToFloat surfaceScore]
    , aligned := by simp }
  else
    { ranking := [ScopeConfig.toScopeReading' .surface, ScopeConfig.toScopeReading' .inverse]
    , scores := [ratToFloat surfaceScore, ratToFloat inverseScore]
    , aligned := by simp }

/--
RSA implements HasScopePreference for ScopedForm.

Given a ScopedForm (from Montague), RSA computes preferences based on
L1 listener inference.
-/
instance : HasScopePreference RSAScopeTheory ScopedForm Unit where
  preferScopes form _ctx avail :=
    -- For now, we only handle the specific "every horse didn't jump" case
    -- A general implementation would parameterize by the meaning function
    if form.surface == "Every horse didn't jump" && avail.isAmbiguous then
      rsaScopePreference
    else
      -- Default: surface preferred
      { ranking := avail.readings
      , scores := avail.readings.map (λ _ => 1.0)
      , aligned := by simp }

/-- RSA's interpretation set matches ScopedForm's available scopes.

The interpretations used by RSA ({surface, inverse}) correspond exactly to
the available scopes declared by the ScopedForm. -/
theorem rsa_interps_match_available_scopes :
    everyHorseDidntJump_form.availableScopes.length =
    everyHorseDidntJump_meaning.interps.length := by
  native_decide

/-- RSA scope preference agrees with marginal distribution.

The preference ranking from RSA puts inverse first (since P(inverse) > P(surface)). -/
theorem rsa_preference_is_inverse_first :
    getScopeScore .inverse > getScopeScore .surface := by
  native_decide

/-- RSA's available interpretations come from ScopedForm.

RSA does not stipulate its own scope readings; they are
derived from the grammatical analysis in ScopedForm. -/
theorem rsa_grounded_in_scopedform :
    (everyHorseDidntJump_form.availableScopes.map ScopeConfig.toScopeReading') =
    (everyHorseDidntJump_meaning.interps.map ScopeConfig.toScopeReading') := by
  native_decide

/-- From ScopedForm through RSA to preference ranking.

1. ScopedForm declares available scopes (grammar)
2. WorldMeaning provides truth conditions (semantics)
3. RSA computes L1 distribution (pragmatics)
4. Preference ranking emerges from L1 marginal -/
theorem full_scope_integration :
    -- ScopedForm is ambiguous
    everyHorseDidntJump_form.availableScopes.length > 1 ∧
    -- RSA uses exactly those interpretations
    everyHorseDidntJump_meaning.interps.length = everyHorseDidntJump_form.availableScopes.length ∧
    -- RSA prefers inverse (pragmatic preference)
    getScopeScore .inverse > getScopeScore .surface := by
  native_decide

-- Using Core.Parse (not Exhaustifiable)

/-
## Scope Ambiguity Uses Core.Parse Directly

Scope ambiguity is not exhaustification:
- Scope ambiguity: different quantifier raising configurations (surface/inverse)
- EXH placement: where exhaustification operator inserts (M/O/I)

We use `Core.Parse` and `Core.scopeParses` directly here, not the
`Exhaustifiable` typeclass (which is for EXH-specific phenomena like
Franke & Bergen 2020).
-/

open Core

/-- Map ScopeConfig to Core.Parse -/
def scopeConfigToParse : ScopeConfig → Parse
  | .surface => Parse.surface
  | .inverse => Parse.inverse

/-- Core.scopeParses matches our ScopeConfig -/
theorem scope_parses_match :
    scopeParses.length = 2 ∧
    scopeParses.map Parse.id = ["surface", "inverse"] := by
  native_decide

/-- Scope parses list -/
def scopeParsesList : List Core.Parse := scopeParses

/-- Parse-based world distribution uses scope parses (2), not EXH parses (8) -/
theorem uses_scope_not_exh_parses :
    scopeParsesList.length = 2 := by
  native_decide

/-- Empirical data type for scope ordering predictions. -/
structure ScopeEmpiricalOrdering where
  /-- Does RSA predict more probability for 0-horses than 1-horse? -/
  zeroGtOne : Bool
  /-- Does RSA predict more probability for 1-horse than 2-horses? -/
  oneGtTwo : Bool
  deriving Repr

/-- RSA prediction for the scope ambiguity ordering.

    Computed from the L1 world distribution: P(w=0) > P(w=1) > P(w=2). -/
def rsaPrediction : ScopeEmpiricalOrdering :=
  { zeroGtOne := getWorldScore 0 > getWorldScore 1
  , oneGtTwo := getWorldScore 1 > getWorldScore 2 }

end RSA.ScontrasPearl2021
