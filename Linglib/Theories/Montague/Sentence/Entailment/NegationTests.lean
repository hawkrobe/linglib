/-
Verification that formal negation predictions match empirical judgments
from `Phenomena.Negation.Basic`. Tests DE, not-UE, and DE-comp-DE = UE.
-/

import Linglib.Theories.Montague.Sentence.Entailment.Basic
import Linglib.Theories.Montague.Core.Polarity
import Linglib.Core.Proposition
import Linglib.Phenomena.Negation.Basic

namespace Montague.Sentence.Entailment.NegationTests

open Montague.Sentence.Entailment
open Montague.Core.Polarity
open Phenomena.Negation
open Core.Proposition

section TestDomain

/-- A simple domain with dogs and cats (both animals). -/
inductive Animal where
  | dog1 | dog2 | cat1 | cat2
  deriving DecidableEq, BEq, Repr

def allAnimals : List Animal := [.dog1, .dog2, .cat1, .cat2]

/-- Proposition: x is a dog. -/
def isDog : BProp Animal := λ x => match x with
  | .dog1 | .dog2 => true
  | _ => false

/-- Proposition: x is an animal (tautology in this domain). -/
def isAnimal : BProp Animal := λ _ => true

/-- dogs subset animals: isDog |= isAnimal. -/
theorem dogs_subset_animals : ∀ x, isDog x = true → isAnimal x = true := by
  intro x _; rfl

end TestDomain

section DEVerification

/-- Negation is DE: dogs <= animals implies not-animal <= not-dog. -/
theorem negation_de_test :
    ∀ x, Decidable.pnot Animal isAnimal x = true →
         Decidable.pnot Animal isDog x = true :=
  Decidable.pnot_reverses_entailment isDog isAnimal dogs_subset_animals

/-- DE prediction matches `negation_de_valid`. -/
theorem de_prediction_matches_data :
    negation_de_valid.judgedValid = true := rfl

/-- Negation is not UE: not-dog does not entail not-animal. -/
example : ∃ x, Decidable.pnot Animal isDog x = true ∧
               Decidable.pnot Animal isAnimal x = false := by
  use Animal.cat1
  simp [Decidable.pnot, isDog, isAnimal]

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

end Montague.Sentence.Entailment.NegationTests
