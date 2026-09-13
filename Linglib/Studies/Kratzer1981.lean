/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype
import Linglib.Semantics.Conditionals.Restrictor
import Linglib.Semantics.Modality.Kratzer.Operators

/-!
# Kratzer (1981): The Notional Category of Modality

This file formalizes the paper's practical-inference example, on the modal base and ordering
source semantics of `Modality.Kratzer.Operators`. Someone wants two things, to become mayor
and to avoid the pub, while the circumstances are such that they become mayor only if they go
to the pub. The circumstances supply the modal base and the desires the ordering source, and
the two ideals pull apart: a world where the speaker goes to the pub and becomes mayor and one
where they stay home and do not are incomparable, so the ordering is not connected. Of the
five conclusions the paper considers, the three necessities and impossibilities (that the
speaker should go to the pub, should avoid it, and could become mayor without it) fail, while
the two possibilities (that they could go and could avoid going) hold, under the paper's
limit-free necessity and its dual possibility.

The paper's section on conditionals treats an if-clause as restricting the modal base of the
modal in its matrix clause, the substrate's `Conditionals.Restrictor.conditionalNecessity`,
and derives the kinds of conditional from the settings of the two backgrounds: material
implication from a totally realistic base and an empty ordering source
(`material_implication`), strict implication from an empty base and an empty ordering source
(`strict_implication`), counterfactuals from an empty base and a totally realistic ordering
source, the subject of the paper's companion on partition and revision, and deontic
conditionals from an empty base and an ordering source of what is morally good. The deontic
example is the argument against analyzing conditionals as modalized material implications:
given that justice must be done, that analysis makes *if someone was treated unjustly, the
injustice must be amended for* and *... must be rewarded* both vacuously true
(`traditional_collapses`), while restricting an empty base by the antecedent and ordering by
what is morally good makes the first true and the second false
(`injustice_must_be_amended`, `not_injustice_must_be_rewarded`), a world where injustice is
amended for being closer to the good than one where it is rewarded, the truth conditions of
[lewis-1973].

## Implementation notes

The worlds are the four combinations of becoming mayor and going to the pub, so every claim
is decided once the modal base, the ordering source, and the operators are unfolded. The
example also fixes the reading of `bestWorlds`: the world that is at least as good as every
accessible world does not exist here, so the minimality reading, on which the best worlds are
the two ideal-realizing ones, is the one that agrees with the limit-free operators.

The deontic example's worlds are the situations with no injustice and those where an injustice
was amended for, rewarded, or neither; the ordering source of what is morally good is left
informal in the paper and is rendered by two ideals, that there is no injustice and that any
injustice is amended for. The section on conditionals is read from the revised version of the
paper in [kratzer-2012].

## References

* [kratzer-1981]
* [kratzer-2012] — Chapter 2, the revised version of the paper
* [lewis-1973]
-/

namespace Kratzer1981

open Modality.Kratzer

/-- A world: does the speaker become mayor, and go to the pub regularly? -/
abbrev World := Bool × Bool

/-- The evaluation world, arbitrary since the backgrounds are constant. -/
def w₀ : World := (false, false)

/-- The relevant circumstances: the speaker becomes mayor only by going to the pub. -/
def circumstances : ModalBase World := Function.const World [λ w => w.1 = true → w.2 = true]

/-- What the speaker wants: to become mayor, and to avoid the pub. -/
def desires : OrderingSource World :=
  Function.const World [λ w => w.1 = true, λ w => w.2 = false]

/-- Decide a claim about the backgrounds and the ordering over the four worlds. -/
scoped macro "decide_worlds" : tactic =>
  `(tactic| (simp only [accessibleWorlds, propIntersection, atLeastAsGoodAs_iff, circumstances,
      desires, Function.const_apply, Set.mem_ofPred_eq, List.forall_mem_cons, List.mem_nil_iff,
      false_implies, implies_true, and_true]; decide))

/-- The paper's clause (c): the world of going to the pub and becoming mayor and the world of
staying home are incomparable, so the ordering is not connected. -/
theorem mayor_pub_incomparable :
    ¬ atLeastAsGoodAs (desires w₀) (true, true) (false, false) ∧
      ¬ atLeastAsGoodAs (desires w₀) (false, false) (true, true) := by
  decide_worlds

/-- Clause (f): the accessible world where the speaker goes to the pub and still fails to
become mayor is strictly worse than either ideal-realizing world. -/
theorem pub_no_mayor_worst :
    ∀ v ∈ ({(true, true), (false, false)} : Set World),
      atLeastAsGoodAs (desires w₀) v (false, true) ∧
        ¬ atLeastAsGoodAs (desires w₀) (false, true) v := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  decide_worlds

/-- No accessible world is at least as good as every accessible world: on the dominance
reading of "best" the example would have no best world at all. -/
theorem no_dominant_world :
    ¬ ∃ w ∈ accessibleWorlds circumstances w₀,
      ∀ v ∈ accessibleWorlds circumstances w₀, atLeastAsGoodAs (desires w₀) w v := by
  decide_worlds

/-- The best worlds are the two ideal-realizing ones. -/
theorem mem_bestWorlds_iff (w : World) :
    w ∈ bestWorlds circumstances desires w₀ ↔ w = (true, true) ∨ w = (false, false) := by
  revert w
  simp only [bestWorlds, Core.Order.Normality.mem_optimal, kratzerNormality,
    Core.Order.Normality.fromProps, Preorder.ofCriteria_le_iff]
  decide_worlds

/-- The example satisfies the Limit Assumption, so the paper's limit-free operators are
quantification over `bestWorlds`. -/
theorem limitAssumption : LimitAssumption circumstances desires w₀ := by
  simp only [LimitAssumption, mem_bestWorlds_iff]
  decide_worlds

/-- Decide a verdict of the limit-free operators through the best worlds. -/
scoped macro "decide_verdict" : tactic =>
  `(tactic| (simp only [humanPossibility, humanNecessity_iff_necessity limitAssumption,
      necessity, ModalLogic.box, kratzerBestR, mem_bestWorlds_iff, forall_eq_or_imp,
      forall_eq]; decide))

/-- Conclusion one fails: the speaker need not go to the pub. -/
theorem not_must_pub : ¬ humanNecessity circumstances desires (·.2 = true) w₀ := by
  decide_verdict

/-- Conclusion two fails: the speaker need not avoid the pub. -/
theorem not_must_avoid : ¬ humanNecessity circumstances desires (·.2 = false) w₀ := by
  decide_verdict

/-- Conclusion three fails: becoming mayor without the pub is not even accessible, and wishes
cannot override facts. -/
theorem not_can_mayor_without_pub :
    ¬ humanPossibility circumstances desires (λ w => w.1 = true ∧ w.2 = false) w₀ := by
  decide_verdict

/-- Conclusion four holds: the speaker could go to the pub. -/
theorem can_pub : humanPossibility circumstances desires (·.2 = true) w₀ := by
  decide_verdict

/-- Conclusion five holds: the speaker could avoid the pub. -/
theorem can_avoid : humanPossibility circumstances desires (·.2 = false) w₀ := by
  decide_verdict

/-! ### Conditionals

An if-clause restricts the modal base of the modal in its matrix clause, so `(if α)
(necessarily β)` is the necessity of `β` at the base enlarged by `α`. The kinds of conditional
differ in the settings of the two backgrounds. -/

open Conditionals.Restrictor

/-- Material implication: a totally realistic modal base and an empty ordering source. -/
theorem material_implication {W : Type*} {f : ModalBase W} (hf : isTotallyRealistic f)
    (α β : W → Prop) (w : W) :
    conditionalNecessity f emptyBackground α β w ↔ (α w → β w) :=
  material_from_restrictor f α β w (hf w)

/-- Strict implication: an empty modal base and an empty ordering source, so the conditional
holds iff the antecedent logically implies the consequent. -/
theorem strict_implication {W : Type*} (α β : W → Prop) (w : W) :
    conditionalNecessity emptyBackground emptyBackground α β w ↔ ∀ v, α v → β v := by
  rw [restrictor_eq_strict, empty_base_universal_access]
  simp

/-- Under an analysis of conditionals as modalized material implications, a necessity that
the antecedent fail makes every conditional with that antecedent vacuously true. -/
theorem traditional_vacuous {W : Type*} (f : ModalBase W) (α β : W → Prop) (w : W)
    (h : simpleNecessity f (λ v => ¬ α v) w) : simpleNecessity f (λ v => α v → β v) w :=
  λ v hv hα => absurd hα (h v hv)

/-! #### The deontic example -/

/-- What became of an injustice: it was amended for, rewarded, or neither. -/
inductive Redress where
  | amended
  | rewarded
  | neither
  deriving DecidableEq, Repr, Fintype

/-- A situation: no injustice, or an injustice and what became of it. -/
abbrev Situation := Option Redress

/-- Someone was treated unjustly. -/
def injustice (s : Situation) : Prop := s.isSome = true

/-- The injustice was amended for. -/
def amended (s : Situation) : Prop := s = some .amended

/-- The injustice was rewarded. -/
def rewarded (s : Situation) : Prop := s = some .rewarded

instance : DecidablePred injustice := λ s => inferInstanceAs (Decidable (s.isSome = true))
instance : DecidablePred amended := λ s => inferInstanceAs (Decidable (s = some .amended))
instance : DecidablePred rewarded := λ s => inferInstanceAs (Decidable (s = some .rewarded))

/-- What is morally good: there is no injustice, and any injustice is amended for. A situation
with amended injustice is not good, but it is closer to the good than one where the injustice
is rewarded or unredressed. -/
def morallyGood : OrderingSource Situation :=
  Function.const Situation [λ s => ¬ injustice s, λ s => injustice s → amended s]

/-- The morally accessible situations of the traditional analysis: those without injustice. -/
def morallyAccessible : ModalBase Situation := Function.const Situation [λ s => ¬ injustice s]

/-- Decide a claim about the backgrounds and the ordering over the four situations. -/
scoped macro "decide_situations" : tactic =>
  `(tactic| (simp only [accessibleWorlds, propIntersection, restrictedBase, emptyBackground,
      atLeastAsGoodAs_iff, morallyGood, morallyAccessible, Function.const_apply,
      Set.mem_ofPred_eq, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
      and_true, injustice, amended, rewarded]; decide))

/-- With an empty base, the situation closest to the good is the one without injustice. -/
theorem mem_bestWorlds_good_iff (s : Situation) :
    s ∈ bestWorlds emptyBackground morallyGood none ↔ s = none := by
  revert s
  simp only [bestWorlds, Core.Order.Normality.mem_optimal, kratzerNormality,
    Core.Order.Normality.fromProps, Preorder.ofCriteria_le_iff]
  decide_situations

/-- Among the situations with injustice, the one closest to the good is the one where it is
amended for. -/
theorem mem_bestWorlds_injustice_iff (s : Situation) :
    s ∈ bestWorlds (restrictedBase emptyBackground injustice) morallyGood none ↔
      s = some .amended := by
  revert s
  simp only [bestWorlds, Core.Order.Normality.mem_optimal, kratzerNormality,
    Core.Order.Normality.fromProps, Preorder.ofCriteria_le_iff]
  decide_situations

/-- The restricted base satisfies the Limit Assumption, so the verdicts below are those of the
paper's human necessity as well. -/
theorem limitAssumption_injustice :
    LimitAssumption (restrictedBase emptyBackground injustice) morallyGood none := by
  simp only [LimitAssumption, mem_bestWorlds_injustice_iff]
  decide_situations

/-- (59): justice must be done, there being no injustice in the situations closest to the
good. -/
theorem justice_must_be_done : necessity emptyBackground morallyGood (λ s => ¬ injustice s) none := by
  simp only [necessity, ModalLogic.box, kratzerBestR, mem_bestWorlds_good_iff, forall_eq]
  decide

/-- (60): if someone was treated unjustly, the injustice must be amended for. -/
theorem injustice_must_be_amended :
    conditionalNecessity emptyBackground morallyGood injustice amended none := by
  simp only [conditionalNecessity, necessity, ModalLogic.box, kratzerBestR,
    mem_bestWorlds_injustice_iff, forall_eq]
  decide

/-- (61) is false: the injustice need not be rewarded. -/
theorem not_injustice_must_be_rewarded :
    ¬ conditionalNecessity emptyBackground morallyGood injustice rewarded none := by
  simp only [conditionalNecessity, necessity, ModalLogic.box, kratzerBestR,
    mem_bestWorlds_injustice_iff, forall_eq]
  decide

/-- The traditional analysis over the morally accessible situations: (59) holds, and then
(60) and (61) are both vacuously true, since no accessible situation has injustice. -/
theorem traditional_collapses :
    simpleNecessity morallyAccessible (λ s => ¬ injustice s) none ∧
      simpleNecessity morallyAccessible (λ s => injustice s → amended s) none ∧
        simpleNecessity morallyAccessible (λ s => injustice s → rewarded s) none := by
  have h : simpleNecessity morallyAccessible (λ s => ¬ injustice s) none := by
    simp only [simpleNecessity_iff_all]
    decide_situations
  exact ⟨h, traditional_vacuous _ _ _ _ h, traditional_vacuous _ _ _ _ h⟩

end Kratzer1981
