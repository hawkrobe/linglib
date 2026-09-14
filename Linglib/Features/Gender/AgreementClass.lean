import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Cardinal.Finite
import Linglib.Features.Gender.Basic

/-!
# Agreement classes and target genders

This file defines the agreement classes of a language's nouns and the target genders of its
agreement targets, and classifies the map between the target genders of two numbers.

An agreement class is a set of nouns that take the same agreement forms on every target in
every morphosyntactic form, and the controller genders of a language are its agreement
classes. A target gender is a form an agreeing target distinguishes, and there may be fewer
target genders than controller genders: Romanian has three of the latter over two of the
former in each number. The target genders of the singular and the plural determine one
another, as in French, the singular's determine the plural's without the converse, as in
German, or neither determines the other, as in Romanian or Lak.

## Main definitions

* `Gender.agreementClasses`: the kernel of the noun-level agreement map.
* `Gender.targetGenders`: the range of the agreement map restricted to one target.
* `Gender.Parallel`, `Gender.Convergent`, `Gender.Crossed`: the map between the target
  genders of two numbers, as each factors through the other or not.

## Main results

* `Gender.card_quotient_agreementClasses`: the controller genders are as many as the
  agreement map has values.
* `Gender.card_range_le_prod`: the controller genders are at most the product over the
  targets of the target genders.
* `Gender.System.Assigned.agreementClasses_eq`: when a faithful system mediates agreement,
  the agreement classes are the fibres of its assignment.

## References

* [corbett-1991] — chapter 6
* [zaliznjak-1964] — agreement classes
* [greenberg-1963] — Universal 37: the plural never distinguishes more genders than the
  singular
-/

namespace Gender

variable {N T F : Type*}

/-- Zaliznjak's agreement classes: two nouns are in one class when they take the same form
on every target in every morphosyntactic form. -/
abbrev agreementClasses (agr : N → T → F) : Setoid N := Setoid.ker agr

/-- The controller genders are the agreement classes: as many as the agreement map has
values. -/
theorem card_quotient_agreementClasses (agr : N → T → F) :
    Nat.card (Quotient (agreementClasses agr)) = Nat.card (Set.range agr) :=
  Nat.card_congr (Setoid.quotientKerEquivRange agr)

/-- The target genders of a target: the forms it shows. -/
abbrev targetGenders (agr : N → T → F) (t : T) : Set F := Set.range (agr · t)

/-- The controller genders are at most the product of the target genders over the targets. -/
theorem card_range_le_prod [Finite N] [Fintype T] (agr : N → T → F) :
    Nat.card (Set.range agr) ≤ ∏ t, Nat.card (targetGenders agr t) := by
  rw [← Nat.card_pi]
  exact Nat.card_le_card_of_injective (λ f t => ⟨f.1 t, f.2.imp λ n hn => congrFun hn t⟩)
    λ f g h => Subtype.ext (funext λ t => congrArg Subtype.val (congrFun h t))

/-- When a faithful system mediates agreement, the agreement classes are the fibres of its
assignment: the controller genders are the genders. -/
theorem System.Assigned.agreementClasses_eq {G : Type*} (S : System.Assigned N G)
    {nounAgr : N → T → F} {agr : G → T → F} (med : S.Mediates nounAgr agr)
    (faith : Faithful agr) : agreementClasses nounAgr = Setoid.ker S.assign :=
  Setoid.ext λ a b => by
    change nounAgr a = nounAgr b ↔ S.assign a = S.assign b
    rw [med a, med b, faith.eq_iff]

section NumberMap

variable {F' : Type*}

/-- The map between the target genders of two numbers is parallel when each determines the
other. -/
def Parallel (sg : N → F) (pl : N → F') : Prop :=
  Function.FactorsThrough pl sg ∧ Function.FactorsThrough sg pl

/-- Convergent when the first determines the second but not conversely. -/
def Convergent (sg : N → F) (pl : N → F') : Prop :=
  Function.FactorsThrough pl sg ∧ ¬ Function.FactorsThrough sg pl

/-- Crossed when neither determines the other. -/
def Crossed (sg : N → F) (pl : N → F') : Prop :=
  ¬ Function.FactorsThrough pl sg ∧ ¬ Function.FactorsThrough sg pl

variable [Fintype N] [DecidableEq F] [DecidableEq F'] (sg : N → F) (pl : N → F')

instance : Decidable (Parallel sg pl) := by
  unfold Parallel; infer_instance

instance : Decidable (Convergent sg pl) := by
  unfold Convergent; infer_instance

instance : Decidable (Crossed sg pl) := by
  unfold Crossed; infer_instance

end NumberMap

end Gender
