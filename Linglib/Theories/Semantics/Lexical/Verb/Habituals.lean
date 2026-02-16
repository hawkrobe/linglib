/-
Traditional HAB operator and frequency-based threshold semantics for habituals.
HAB quantifies over "characteristic" occasions; threshold semantics replaces this
with observable frequency > θ, where θ is pragmatically inferred (Tessler & Goodman 2019).

- Carlson, G.N. (1977). Reference to Kinds in English.
- Krifka, M. et al. (1995). Genericity: An Introduction.
- Bhatt, R. (1999). Covert Modality in Non-finite Contexts.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith

namespace Semantics.Lexical.Verb.Habituals

section Core

/-- A time interval or occasion for habitual quantification. -/
structure Occasion where
  id : Nat
  deriving DecidableEq, Repr

instance : Inhabited Occasion := ⟨{ id := 0 }⟩

/-- An activity predicate (what John does at an occasion). -/
abbrev Activity := Occasion → Bool

/-- A characteristicness predicate (which occasions are "typical"). -/
abbrev Characteristic := Occasion → Bool

/-- Traditional HAB: `∀t. characteristic(t) → activity(t)`. -/
def traditionalHAB
    (occasions : List Occasion)
    (characteristic : Characteristic)
    (activity : Activity)
    : Bool :=
  occasions.all λ t =>
    !characteristic t || activity t

/-- Alternative: existential characterization of non-habitual. -/
def traditionalHAB_existential
    (occasions : List Occasion)
    (characteristic : Characteristic)
    (activity : Activity)
    : Bool :=
  !occasions.any λ t => characteristic t && !activity t

/-- The two formulations are equivalent. -/
theorem hab_formulations_equiv
    (occasions : List Occasion)
    (characteristic : Characteristic)
    (activity : Activity)
    : traditionalHAB occasions characteristic activity =
      traditionalHAB_existential occasions characteristic activity := by
  simp only [traditionalHAB, traditionalHAB_existential, List.all_eq_not_any_not]
  congr 1
  induction occasions with
  | nil => rfl
  | cons o os ih =>
    simp only [List.any_cons]
    rw [ih]
    cases characteristic o <;> cases activity o <;> rfl

end Core

section Frequency

/-- Frequency of an activity: proportion of occasions where it occurs. -/
def frequency
    (occasions : List Occasion)
    (activity : Activity)
    : ℚ :=
  let active := occasions.filter activity
  if occasions.length = 0 then 0
  else (active.length : ℚ) / (occasions.length : ℚ)

/-- Threshold-based habitual: true iff frequency exceeds threshold. -/
def thresholdHabitual
    (occasions : List Occasion)
    (activity : Activity)
    (threshold : ℚ)
    : Bool :=
  frequency occasions activity > threshold

/-- For any HAB configuration, there exists a matching threshold giving the same truth value.

    Proof sketch: both sides are `Bool`, so we case-split. When HAB = true, pick
    θ = frequency − 1 (any value beats its predecessor); when HAB = false, pick
    θ = frequency (strict self-comparison is false). This is an expressiveness result:
    threshold semantics can simulate any HAB outcome, though not vice versa (it loses
    the characteristic-occasion structure). -/
theorem hab_reduces_to_threshold
    (occasions : List Occasion)
    (characteristic : Characteristic)
    (activity : Activity)
    (_hNonEmpty : occasions.length > 0)
    : ∃ θ : ℚ, traditionalHAB occasions characteristic activity =
               thresholdHabitual occasions activity θ := by
  let f := frequency occasions activity
  cases h : traditionalHAB occasions characteristic activity
  · -- HAB = false: pick θ = frequency (frequency > frequency is false by irreflexivity)
    refine ⟨f, ?_⟩
    show false = decide (f > f)
    rw [decide_eq_false (not_lt.mpr (le_refl (α := ℚ) f))]
  · -- HAB = true: pick θ = frequency - 1 (frequency > frequency - 1 since 0 < 1)
    refine ⟨f - 1, ?_⟩
    show true = decide (f > f - 1)
    have hgt : f > f - 1 := by linarith
    rw [decide_eq_true hgt]

/-- Activity types with different frequency expectations. -/
inductive ActivityType where
  | neutral      -- Eating, sleeping, walking (high frequency expected)
  | occupation   -- Doctor, teacher, smoker (regular but not constant)
  | striking     -- Murder, crime (very low frequency sufficient)
  | achievement  -- Win championship, graduate (once is enough)
  deriving DecidableEq, Repr

/-- Expected frequency threshold by activity type. -/
def expectedThreshold : ActivityType → ℚ
  | .neutral => 8/10      -- Most occasions
  | .occupation => 5/10   -- Regular occasions
  | .striking => 1/100    -- Rare is enough
  | .achievement => 0     -- Once suffices

end Frequency

section Examples

def occasions : List Occasion := [
  { id := 0 }, { id := 1 }, { id := 2 }, { id := 3 }, { id := 4 },
  { id := 5 }, { id := 6 }, { id := 7 }, { id := 8 }, { id := 9 }
]

def johnSmokesActivity : Activity := λ t =>
  t.id ∈ [0, 1, 2, 4, 5, 8]

def normalOccasions : Characteristic := λ t =>
  t.id ∈ [0, 1, 2, 3, 4, 5, 6, 7]

#eval frequency occasions johnSmokesActivity
#eval thresholdHabitual occasions johnSmokesActivity (1/2)

/-- Unified structure for GEN/HAB elimination. -/
structure ThresholdQuantifier where
  name : String
  /-- What we measure (prevalence for GEN, frequency for HAB) -/
  measureName : String
  /-- The threshold (inferred pragmatically) -/
  threshold : ℚ

def genAsThreshold : ThresholdQuantifier :=
  { name := "GEN"
  , measureName := "prevalence"
  , threshold := 0
  }

def habAsThreshold : ThresholdQuantifier :=
  { name := "HAB"
  , measureName := "frequency"
  , threshold := 0
  }

end Examples

end Semantics.Lexical.Verb.Habituals
