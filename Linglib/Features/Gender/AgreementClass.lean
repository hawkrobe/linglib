import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Cardinal.Finite
import Linglib.Core.Relation.FactorsThroughOn
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
* `Gender.agreementClasses_eq_ker_of_faithful`: when a faithful carrier mediates
  agreement, the agreement classes are the fibres of the assignment.
* `Gender.parallel_iff_ker_eq`, `Gender.convergent_iff_ker_lt`: the map between two numbers'
  target genders is the order of their kernels.

## Implementation notes

* The index `T` of the agreement map is whatever the map is restricted to: a target
  category, a morphosyntactic form, or a pair of the two, so that target genders can be
  counted per target as well as per number across targets.
* Subgenders, agreement classes differing on a minority of forms, inquorate genders, small
  closed classes whose pattern mixes other genders, and overdifferentiated targets are the
  steps from agreement classes to controller genders that remain to be defined; until then
  the agreement classes of a fragment are its controller genders only when the fragment
  records no such class.

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

/-- When noun-level agreement is the per-gender behaviour of a faithful carrier, the
agreement classes are the fibres of the assignment: the genders are the agreement classes. -/
theorem agreementClasses_eq_ker_of_faithful {G : Type*} {assign : N → G}
    {nounAgr : N → T → F} {agr : G → T → F} (med : nounAgr = agr ∘ assign)
    (faith : Faithful agr) : agreementClasses nounAgr = Setoid.ker assign :=
  Setoid.ext λ a b => by
    rw [Setoid.ker_def, Setoid.ker_def, med, Function.comp_apply, Function.comp_apply,
      faith.eq_iff]

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

/-- Parallel target genders have the same kernel. -/
theorem parallel_iff_ker_eq {sg : N → F} {pl : N → F'} :
    Parallel sg pl ↔ Setoid.ker sg = Setoid.ker pl := by
  simp only [Parallel, Function.factorsThrough_iff_ker_le, le_antisymm_iff]

/-- Convergent target genders have strictly ordered kernels. -/
theorem convergent_iff_ker_lt {sg : N → F} {pl : N → F'} :
    Convergent sg pl ↔ Setoid.ker sg < Setoid.ker pl := by
  simp only [Convergent, Function.factorsThrough_iff_ker_le, lt_iff_le_not_ge]

variable [Fintype N] [DecidableEq F] [DecidableEq F'] (sg : N → F) (pl : N → F')

instance : Decidable (Parallel sg pl) := by
  unfold Parallel; infer_instance

instance : Decidable (Convergent sg pl) := by
  unfold Convergent; infer_instance

instance : Decidable (Crossed sg pl) := by
  unfold Crossed; infer_instance

end NumberMap

end Gender
