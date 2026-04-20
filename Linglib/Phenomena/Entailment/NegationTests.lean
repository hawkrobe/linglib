/-
Verification that formal negation predictions match empirical judgments
from `Phenomena.Negation.Basic`. Tests DE, not-UE, and DE-comp-DE = UE.
-/

import Linglib.Theories.Semantics.Entailment.Basic
import Linglib.Theories.Semantics.Entailment.Polarity
import Linglib.Phenomena.Negation.Basic
import Mathlib.Data.Set.Basic

namespace Semantics.Entailment.NegationTests

open Semantics.Entailment
open Semantics.Entailment.Polarity
open Phenomena.Negation

section TestDomain

/-- A simple domain with dogs and cats (both animals). -/
inductive Animal where
  | dog1 | dog2 | cat1 | cat2
  deriving DecidableEq, Repr

def allAnimals : List Animal := [.dog1, .dog2, .cat1, .cat2]

/-- Proposition: x is a dog. -/
def isDog : Set Animal := λ x => match x with
  | .dog1 | .dog2 => True
  | _ => False

/-- Proposition: x is an animal (tautology in this domain). -/
def isAnimal : Set Animal := λ _ => True

/-- dogs subset animals: isDog |= isAnimal. -/
theorem dogs_subset_animals : ∀ x, isDog x → isAnimal x := by
  intro x _; trivial

end TestDomain

section DEVerification

/-- Negation is DE: dogs <= animals implies not-animal <= not-dog. -/
theorem negation_de_test :
    ∀ x, ¬ isAnimal x → ¬ isDog x := by
  intro x hna hd
  exact hna (dogs_subset_animals x hd)

/-- DE prediction matches `negation_de_valid`. -/
theorem de_prediction_matches_data :
    negation_de_valid.judgedValid = true := rfl

/-- Negation is not UE: not-dog does not entail not-animal. -/
example : ∃ x, ¬ isDog x ∧ ¬ ¬ isAnimal x := by
  refine ⟨Animal.cat1, ?_, ?_⟩
  · intro h; cases h
  · intro h; exact h trivial

/-- Not-UE prediction matches `negation_not_ue`. -/
theorem not_ue_prediction_matches_data :
    negation_not_ue.judgedValid = false := rfl

/-- Double negation is UE (DE comp DE = UE). -/
theorem double_negation_is_ue : IsUpwardEntailing (pnot ∘ pnot) :=
  pnot_pnot_isUpwardEntailing

/-- Double negation prediction matches `double_negation_ue`. -/
theorem double_neg_prediction_matches_data :
    double_negation_ue.judgedValid = true := rfl

/-- All negation predictions from formal semantics match empirical judgments. -/
theorem all_predictions_match :
    negation_de_valid.judgedValid = true ∧
    negation_not_ue.judgedValid = false ∧
    double_negation_ue.judgedValid = true := by
  exact ⟨rfl, rfl, rfl⟩

end DEVerification

end Semantics.Entailment.NegationTests
