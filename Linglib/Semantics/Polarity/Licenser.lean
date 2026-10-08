/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.Soundness
public import Linglib.Logic.Natural.Strawson
public import Linglib.Semantics.Exhaustification.Antiexhaustive
public import Linglib.Semantics.Questions.Value
public import Linglib.Semantics.Polarity.Strength

/-!
# Licensers

A licenser is what a construction places over the position of a polarity item: a family of
operators, one for each choice of what the construction leaves open, such as the model, a
restrictor, a bound or an accessibility relation. A classical licenser maps between bounded
lattices, von Fintel's map into partial propositions, a modal licenser quantifies over worlds,
and a question licenser is a wh-question. A licenser carries a strength of negation when every
operator in its family does, weak strength modulo presupposition after von Fintel and stronger
ones outright after Gajewski. A modal licenser licenses free choice when the antiexhaustified
existential under one of its operators is consistent, after Chierchia, and a question licenses by
relevance, since widening the domain of a wh-question never lowers its value, after van Rooy.

## Main definitions

* `PolarityItem.Licenser`: the four kinds of licenser.
* `PolarityItem.Licenser.Holds`, `PolarityItem.Licenser.Carries`: a signature held outright and a
  strength of negation carried.
* `PolarityItem.Licenser.LicensesFreeChoice`, `PolarityItem.Licenser.LicensesByRelevance`: the
  free-choice and question routes.

## Implementation notes

* Strength reads the unit conditions of `Signature.HoldsFor`, so a constant map holds no strength
  of negation, and *without* is anti-additive but not anti-morphic.
* The question route states the weak form the theory of question value proves, that widening
  never lowers the question's value; van Rooy's strict condition for rhetorical questions is not
  formalized.

## References

* [von-fintel-1999]
* [gajewski-2011]
* [icard-2012]
* [chierchia-2006]
* [van-rooy-2003-npi]
-/

@[expose] public section

namespace PolarityItem

open NaturalLogic Presupposition Exhaustification MeasureTheory

/-- A family of operators between bounded lattices, indexed by what a construction leaves open. -/
structure OperatorFamily where
  /-- What the construction leaves open. -/
  Param : Type 1
  /-- The lattice the item's position ranges over. -/
  Dom : Param → Type
  /-- The lattice of the result. -/
  Cod : Param → Type
  /-- The domain is a lattice. -/
  [latDom : ∀ p, Lattice (Dom p)]
  /-- The domain is bounded. -/
  [bndDom : ∀ p, BoundedOrder (Dom p)]
  /-- The codomain is a lattice. -/
  [latCod : ∀ p, Lattice (Cod p)]
  /-- The codomain is bounded. -/
  [bndCod : ∀ p, BoundedOrder (Cod p)]
  /-- The operator at each parameter. -/
  op : ∀ p, Dom p → Cod p

attribute [instance] OperatorFamily.latDom OperatorFamily.bndDom OperatorFamily.latCod
  OperatorFamily.bndCod

/-- A family of operators into partial propositions, indexed by what a construction leaves
open. -/
structure PresupposingFamily where
  /-- What the construction leaves open. -/
  Param : Type 1
  /-- The lattice the item's position ranges over. -/
  Dom : Param → Type
  /-- The worlds of the partial propositions. -/
  W : Param → Type
  /-- The domain is a lattice. -/
  [latDom : ∀ p, Lattice (Dom p)]
  /-- The domain is bounded. -/
  [bndDom : ∀ p, BoundedOrder (Dom p)]
  /-- The operator at each parameter. -/
  op : ∀ p, Dom p → PartialProp (W p)

attribute [instance] PresupposingFamily.latDom PresupposingFamily.bndDom

/-- A family of modal operators over worlds, indexed by what a construction leaves open. -/
structure ModalFamily where
  /-- What the construction leaves open. -/
  Param : Type 1
  /-- The worlds. -/
  W : Param → Type
  /-- The operator at each parameter. -/
  op : ∀ p, Set (W p) → Set (W p)

/-- A licenser is the operator a construction places over the position of a polarity item: a
classical operator, an operator into partial propositions, a modal operator, or a question. -/
inductive Licenser : Type 2 where
  | classical (F : OperatorFamily)
  | strawson (F : PresupposingFamily)
  | modal (F : ModalFamily)
  | question

/-- A context licenses polarity items by strengthening, as a generic context licensing free choice
items ([kadmon-landman-1993], [dayal-1996]), or by the relevance of a question
([van-rooy-2003-npi]). -/
inductive LicensingMechanism where
  | strengthening
  | genericIndefinite
  | entropy
  deriving DecidableEq, Repr

namespace Licenser

/-- A licenser holds a signature outright when every operator in its family does; an operator into
partial propositions holds it on its truth set. -/
def Holds : Licenser → Signature → Prop
  | .classical F, σ => ∀ p, σ.HoldsFor (F.op p)
  | .strawson F, σ => ∀ p, σ.HoldsFor fun x ↦ (F.op p x).truthSet
  | .modal _, _ | .question, _ => False

/-- A licenser is Strawson downward entailing when every operator in its family is downward
entailing modulo its presupposition. -/
def IsStrawsonDE : Licenser → Prop
  | .classical F => ∀ p, Antitone (F.op p)
  | .strawson F => ∀ p, NaturalLogic.IsStrawsonDE (F.op p)
  | .modal _ | .question => False

/-- A licenser carries a strength of negation, weak strength modulo presupposition
([von-fintel-1999]) and a stronger one outright ([gajewski-2011]). -/
def Carries (L : Licenser) : DEStrength → Prop
  | .weak => L.IsStrawsonDE
  | s => L.Holds s.toSignature

/-- The route by which a licenser licenses. -/
def mechanism : Licenser → LicensingMechanism
  | .classical _ | .strawson _ => .strengthening
  | .modal _ => .genericIndefinite
  | .question => .entropy

/-- A modal licenser licenses free choice when, under one of its operators and over a domain of at
least two possible witnesses, the antiexhaustified existential is consistent
([chierchia-2006]). -/
def LicensesFreeChoice : Licenser → Prop
  | .modal F => ∃ p, ∃ (E : Type) (P : E → Set (F.W p)) (D : Finset E), 1 < D.card ∧
      (oMinus (fun S ↦ F.op p (subDisj P S)) D).Nonempty
  | .classical _ | .strawson _ | .question => False

/-- A question licenses a domain widener by relevance: widening the domain of a wh-question never
lowers its value in any decision problem ([van-rooy-2003-npi]). -/
def LicensesByRelevance : Licenser → Prop
  | .question => ∀ {W A D : Type} [Fintype W] [DecidableEq W] [DecidableEq D] [MeasurableSpace W]
      [DiscreteMeasurableSpace W] [Finite A] [Nonempty W] (U : W → A → ℝ) (μ : Measure W)
      [IsProbabilityMeasure μ] (P : W → Finset D) (dom dom' : Finset D), dom ⊆ dom' →
      Question.utility U μ (Question.wh P dom) ≤ Question.utility U μ (Question.wh P dom')
  | .classical _ | .strawson _ | .modal _ => False

theorem licensesByRelevance_question : question.LicensesByRelevance :=
  fun U μ _ P _ _ h ↦ Question.utility_wh_mono U μ P h

variable {L : Licenser} {σ τ : Signature} {s t : DEStrength}

theorem Holds.of_le (h : L.Holds σ) (hστ : σ ≤ τ) : L.Holds τ := by
  cases L with
  | classical F | strawson F => exact fun p ↦ (h p).of_le hστ
  | modal _ | question => exact h

theorem Holds.toSignature_of_le (h : L.Holds t.toSignature) (hst : s ≤ t) :
    L.Holds s.toSignature :=
  h.of_le (DEStrength.toSignature_antitone hst)

theorem isStrawsonDE_of_holds_anti (h : L.Holds .anti) : L.IsStrawsonDE := by
  cases L with
  | classical F => exact fun p ↦ Signature.holdsFor_anti_iff.mp (h p)
  | strawson F =>
    exact fun p ↦ NaturalLogic.IsStrawsonDE.of_antitone_truthSet
      (Signature.holdsFor_anti_iff.mp (h p))
  | modal _ | question => exact h

theorem carries_of_holds (h : L.Holds s.toSignature) : L.Carries s := by
  cases s with
  | weak => exact isStrawsonDE_of_holds_anti h
  | antiAdditive | antiMorphic => exact h

/-- A classical licenser carries a strength exactly when it holds it outright. -/
theorem carries_classical_iff {F : OperatorFamily} :
    (classical F).Carries s ↔ (classical F).Holds s.toSignature := by
  cases s with
  | weak => exact forall_congr' fun p ↦ Signature.holdsFor_anti_iff.symm
  | antiAdditive | antiMorphic => exact Iff.rfl

/-- A licenser holding exactly the strength `s₀` outright holds `s` exactly when `s ≤ s₀`. -/
theorem holds_toSignature_iff {s₀ : DEStrength} (h : L.Holds s₀.toSignature)
    (hn : ∀ s, s₀ < s → ¬ L.Holds s.toSignature) : L.Holds s.toSignature ↔ s ≤ s₀ :=
  ⟨fun hs ↦ not_lt.mp fun hlt ↦ hn s hlt hs, fun hs ↦ h.toSignature_of_le hs⟩

/-- A licenser holding no strength outright holds none. -/
theorem not_holds_toSignature (h : ¬ L.Holds .anti) : ¬ L.Holds s.toSignature := fun hs ↦
  h (hs.of_le (DEStrength.toSignature_antitone (by cases s <;> decide : DEStrength.weak ≤ s)))

/-- A Strawson-only licenser, downward entailing modulo presupposition and not outright, carries
exactly weak strength ([gajewski-2011]). -/
theorem carries_iff_eq_weak (hde : L.IsStrawsonDE) (h : ¬ L.Holds .anti) :
    L.Carries s ↔ s = .weak := by
  cases s with
  | weak => exact iff_of_true hde rfl
  | antiAdditive | antiMorphic => exact iff_of_false (not_holds_toSignature h) (by decide)

end Licenser

end PolarityItem
