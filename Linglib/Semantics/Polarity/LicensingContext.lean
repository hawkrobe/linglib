/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Polarity.Licenser
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Quantification.Signatures
public import Linglib.Semantics.Quantification.Indefinite
public import Linglib.Semantics.Tense.RunTimes
public import Mathlib.Basic.Rel

/-!
# Licensing contexts

A licensing context is a construction that can host a polarity item, given by the licenser it
places over the item and by the function of Haspelmath's implicational map it realizes, where it
realizes one. Each context below is named for its construction, and what its licenser carries is
a theorem about the operators it denotes. Clausal negation is anti-morphic. *Nobody*, the
restrictor of a universal, *without*, *deny*, *before*, *too … to* and the clausal comparative are
anti-additive and no more, and *few*, *at most* and *doubt* downward entailing and no more. Focus
*only*, adversatives, superlatives, conditional antecedents and temporal *since* are downward
entailing only modulo their presuppositions, the modals, imperatives, generics and free relatives
are modal licensers, and questions license by relevance. The inventory is open: a fragment or a
study can define a context of its own.

## Main declarations

* `PolarityItem.LicensingContext`: a construction, given by its licenser and its function on
  Haspelmath's map.
* `PolarityItem.LicensingContext.negation`, `PolarityItem.LicensingContext.nobody`, …: the
  contexts, each with its certificate (`holds_negation`, `holds_nobody_iff`, …).

## Implementation notes

* *Before* is Anscombe's universal reading, *before ever*. *Too … to* is the
  subject's degree exceeding every degree at which the infinitive holds, after Meier. *Doubt* is not
  believing and *deny* asserting the negation, over a doxastic or assertoric accessibility.
* The free relative is read as a necessity over its alternatives, with the modal presupposition of
  *-ever*; the generic is a necessity over normal worlds.
* Haspelmath's placements are his book's. *Nobody*, *before*-clauses and adversatives sit between
  direct and indirect negation there, so they realize no function here, nor do the rows outside
  the map's inventory.

## References

* [ladusaw-1979]
* [zwarts-1998]
* [vanderwouden-1997]
* [von-fintel-1999]
* [gajewski-2011]
* [anscombe-1964]
* [hoeksema-1983]
* [meier-2003]
* [chierchia-2006]
* [kadmon-landman-1993]
* [van-rooy-2003-npi]
* [haspelmath-1997]
-/

@[expose] public section

namespace PolarityItem

open NaturalLogic Presupposition Quantifier Quantifier.GQ Tense Indefinite

/-- A licensing context is a construction that can host a polarity item: the licenser it places
over the item, and the function of [haspelmath-1997]'s implicational map it realizes. -/
structure LicensingContext where
  /-- The operator family over the item's position. -/
  licenser : Licenser
  /-- The function of the implicational map the construction realizes, if any. -/
  haspelmath : Option HaspelmathFunction

/-! ### The parameters of the operator families -/

/-- A domain of individuals and a predicate over it. -/
structure Predicate where
  /-- The individuals. -/
  ι : Type
  /-- The predicate. -/
  A : ι → Prop

/-- A finite domain and a predicate over it. -/
structure FinitePredicate extends Predicate where
  /-- The domain is finite. -/
  [fin : Fintype ι]

attribute [instance] FinitePredicate.fin

/-- A predicate true of something, the restrictor of a negative quantifier. -/
structure NonemptyPredicate extends Predicate where
  nonempty : ∃ x, A x

/-- A predicate false of something, the scope of a universal. -/
structure NonuniversalPredicate extends Predicate where
  nonuniversal : ∃ x, ¬ A x

/-- A bound and a finite predicate, the restrictor of *at most n*. -/
structure BoundedPredicate extends FinitePredicate where
  /-- The bound. -/
  n : ℕ

/-- A time line and the run times of a main clause. -/
structure MainClause where
  /-- The times. -/
  T : Type
  /-- The times are linearly ordered. -/
  [ord : LinearOrder T]
  /-- The run times of the main clause. -/
  A : Set (NonemptyInterval T)

attribute [instance] MainClause.ord

/-- A measure of individuals on a linearly ordered scale, and the individual compared. -/
structure Measured where
  /-- The individuals. -/
  E : Type
  /-- The degrees. -/
  D : Type
  /-- The degrees are linearly ordered. -/
  [ord : LinearOrder D]
  /-- The measure. -/
  μ : E → D
  /-- The individual compared. -/
  x : E

attribute [instance] Measured.ord

/-- An accessibility relation over worlds, and the evaluation world. -/
structure Accessibility where
  /-- The worlds. -/
  W : Type
  /-- The accessibility relation. -/
  R : SetRel W W
  /-- The evaluation world. -/
  w : W

/-- An accessibility relation with a world accessible from the evaluation world. -/
structure SerialAccessibility extends Accessibility where
  serial : ∃ v, (w, v) ∈ R

/-- An accessibility relation over worlds. -/
structure Frame where
  /-- The worlds. -/
  W : Type
  /-- The accessibility relation. -/
  R : SetRel W W

/-- A focused individual among others, over worlds. -/
structure Focus where
  /-- The individuals. -/
  ι : Type
  /-- The worlds. -/
  W : Type
  /-- The focused individual. -/
  x : ι

/-- The doxastic state, the domain and the ordering source of an adversative attitude. -/
structure Attitude where
  /-- The worlds. -/
  W : Type
  /-- The doxastic state. -/
  dox : W → Set W
  /-- The domain. -/
  base : W → Set W
  /-- The ordering source. -/
  g : W → List (W → Prop)

/-- A measure of the members of a comparison class, and the individual described. -/
structure Superlative where
  /-- The individuals. -/
  α : Type
  /-- The worlds. -/
  W : Type
  /-- The degrees. -/
  D : Type
  /-- The degrees are preordered. -/
  [pre : Preorder D]
  /-- The measure. -/
  μ : α → D
  /-- The individual described. -/
  x : α

attribute [instance] Superlative.pre

/-- The modal horizon and the consequent of a counterfactual. -/
structure Horizon where
  /-- The evaluation indices. -/
  I : Type
  /-- The worlds. -/
  W : Type
  /-- The modal horizon. -/
  horizon : I → Set W
  /-- The consequent. -/
  q : Set W

/-- A time line and the shift back to the reference time of *since*. -/
structure Ago where
  /-- The times. -/
  T : Type
  /-- The times are linearly ordered. -/
  [ord : LinearOrder T]
  /-- The shift back. -/
  ago : T → T

attribute [instance] Ago.ord

namespace LicensingContext

/-! ### The contexts -/

/-- Clausal negation, as in *not*, complement over predicates. -/
def negation : LicensingContext :=
  ⟨.classical ⟨Type, fun α ↦ α → Prop, fun α ↦ α → Prop, fun _ ↦ compl⟩, some .directNeg⟩

/-- A negative quantifier, as in *nobody*, over a restrictor true of something. -/
def nobody : LicensingContext :=
  ⟨.classical ⟨NonemptyPredicate, fun p ↦ p.ι → Prop, fun _ ↦ Prop, fun p ↦ GQ.no p.A⟩, none⟩

/-- *Few* NP, the proportional reading of the English fragment. -/
def few : LicensingContext :=
  ⟨.classical ⟨FinitePredicate, fun p ↦ p.ι → Prop, fun _ ↦ Prop, fun p ↦ GQ.few p.A⟩, none⟩

/-- *At most n* NP. -/
def atMost : LicensingContext :=
  ⟨.classical ⟨BoundedPredicate, fun p ↦ p.ι → Prop, fun _ ↦ Prop, fun p ↦ GQ.atMost p.n p.A⟩,
    none⟩

/-- The restrictor of a universal, as in *everyone who*, over a scope false of something. -/
def universalRestrictor : LicensingContext :=
  ⟨.classical ⟨NonuniversalPredicate, fun p ↦ p.ι → Prop, fun _ ↦ Prop,
    fun p R ↦ GQ.every R p.A⟩, none⟩

/-- A *without*-phrase: the matrix predicate holding without the phrase's. -/
def withoutClause : LicensingContext :=
  ⟨.classical ⟨Predicate, fun p ↦ p.ι → Prop, fun p ↦ p.ι → Prop, fun p V ↦ p.A ⊓ Vᶜ⟩,
    some .indirectNeg⟩

/-- A *before*-clause, Anscombe's universal *before*. -/
def beforeClause : LicensingContext :=
  ⟨.classical ⟨MainClause, fun p ↦ Set (NonemptyInterval p.T), fun _ ↦ Prop,
    fun p ↦ beforeEver p.A⟩, none⟩

/-- The degrees a clause leaves the compared individual above. -/
abbrev exceedsFamily : OperatorFamily :=
  ⟨Measured, fun p ↦ Set p.D, fun _ ↦ Prop, fun p Δ ↦ p.μ p.x ∈ strictUpperBounds Δ⟩

/-- A clausal comparative, *taller than S*, the individual above every degree of the clause. -/
def clausalComparative : LicensingContext := ⟨.classical exceedsFamily, some .comparative⟩

/-- *Too* ADJ *to* VP, the individual above every degree at which the infinitive holds. -/
def tooTo : LicensingContext := ⟨.classical exceedsFamily, none⟩

/-- A verb of doubting, as in *I doubt that*, which does not believe its complement. -/
def doubtVerb : LicensingContext :=
  ⟨.classical ⟨Accessibility, fun p ↦ Set p.W, fun _ ↦ Prop, fun p P ↦ p.w ∉ p.R.core P⟩,
    some .indirectNeg⟩

/-- A verb of denying, as in *she denied that*, which asserts the negation of its complement. -/
def denyVerb : LicensingContext :=
  ⟨.classical ⟨SerialAccessibility, fun p ↦ Set p.W, fun _ ↦ Prop,
    fun p P ↦ p.w ∈ p.R.core Pᶜ⟩, some .indirectNeg⟩

/-- The scope of focus *only*, von Fintel's *only*. -/
def onlyFocus : LicensingContext :=
  ⟨.strawson ⟨Focus, fun p ↦ p.ι → Set p.W, fun p ↦ p.W, fun p ↦ only p.x⟩, none⟩

/-- An adversative predicate, as in *sorry*, *surprised*, *regret*. -/
def adversative : LicensingContext :=
  ⟨.strawson ⟨Attitude, fun p ↦ Set p.W, fun p ↦ p.W,
    fun p ↦ Desire.BestWorlds.regret p.dox p.base p.g⟩, none⟩

/-- A superlative, in its comparison class. -/
def superlative : LicensingContext :=
  ⟨.strawson ⟨Superlative, fun p ↦ p.W → Set p.α, fun p ↦ p.W,
    fun p C ↦ Degree.superlative p.μ C p.x⟩, none⟩

/-- The antecedent of a conditional, the modal-horizon counterfactual. -/
def conditionalAntecedent : LicensingContext :=
  ⟨.strawson ⟨Horizon, fun p ↦ Set p.W, fun p ↦ p.I,
    fun p P ↦ Conditional.horizonCounterfactual p.horizon P p.q⟩, some .conditional⟩

/-- Temporal *since*, as in *it's been five years since*. -/
def sinceTemporal : LicensingContext :=
  ⟨.strawson ⟨Ago, fun p ↦ Set p.T, fun p ↦ p.T, fun p ↦ since p.ago⟩, none⟩

/-- A question. -/
def question : LicensingContext := ⟨.question, some .question⟩

/-- Necessity over a frame. -/
abbrev necessityFamily : ModalFamily := ⟨Frame, fun p ↦ p.W, fun p ↦ p.R.core⟩

/-- A possibility modal. -/
def modalPossibility : LicensingContext :=
  ⟨.modal ⟨Frame, fun p ↦ p.W, fun p ↦ p.R.preimage⟩, some .freeChoice⟩

/-- A necessity modal. -/
def modalNecessity : LicensingContext := ⟨.modal necessityFamily, some .freeChoice⟩

/-- An imperative, a necessity over what is commanded. -/
def imperative : LicensingContext := ⟨.modal necessityFamily, some .freeChoice⟩

/-- A generic sentence, a necessity over normal worlds. -/
def generic : LicensingContext := ⟨.modal necessityFamily, some .freeChoice⟩

/-- A free relative, as in *whatever*, *whoever*, a necessity over its alternatives. -/
def freeRelative : LicensingContext := ⟨.modal necessityFamily, some .freeChoice⟩

/-- Contexts realizing different functions of the map are different. -/
theorem ne_of_haspelmath_ne {c c' : LicensingContext} (h : c.haspelmath ≠ c'.haspelmath) :
    c ≠ c' :=
  mt (congrArg haspelmath) h

/-! ### Classical licensers -/

open Licenser

theorem holds_negation (s : DEStrength) : negation.licenser.Holds s.toSignature :=
  (show negation.licenser.Holds .antiAddMult from fun _ ↦
    Signature.holdsFor_antiAddMult_compl).toSignature_of_le (s := s) (t := .antiMorphic)
      (by cases s <;> decide)

theorem holds_nobody_iff {s : DEStrength} :
    nobody.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_antiAdd_iff.mpr
    ⟨(rightAntiAdditive_iff_isAntiAdditive _).mp rightAntiAdditive_no _,
      eq_false fun h ↦ p.nonempty.elim fun x hx ↦ h x hx trivial⟩) fun s hs h ↦ ?_
  obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
  have := (Signature.holdsFor_antiAddMult_iff.mp (h ⟨⟨Bool, ⊤⟩, ⟨true, trivial⟩⟩)).2.1
    (· = true) (· = false)
  simp [GQ.no, Pi.inf_apply] at this

theorem holds_few_iff {s : DEStrength} : few.licenser.Holds s.toSignature ↔ s ≤ .weak := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_anti_iff.mpr (scopeAntitone_few p.A))
    fun s hs h ↦ ?_
  have := (Signature.holdsFor_antiAdd_iff.mp ((h.toSignature_of_le (s := .antiAdditive)
    (by revert hs; cases s <;> decide)) ⟨⟨Fin 3, ⊤⟩⟩)).1 (· = 0) (· = 1)
  revert this
  show GQ.few (⊤ : Fin 3 → Prop) (fun x ↦ x = 0 ∨ x = 1) = (_ ∧ _) → False
  rw [eq_iff_iff]
  decide

theorem holds_atMost_iff {s : DEStrength} : atMost.licenser.Holds s.toSignature ↔ s ≤ .weak := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_anti_iff.mpr
    (scopeAntitone_atMost p.n p.A)) fun s hs h ↦ ?_
  have := (Signature.holdsFor_antiAdd_iff.mp ((h.toSignature_of_le (s := .antiAdditive)
    (by revert hs; cases s <;> decide)) ⟨⟨⟨Bool, ⊤⟩⟩, 1⟩)).1 (· = true) (· = false)
  revert this
  show GQ.atMost 1 (⊤ : Bool → Prop) (fun x ↦ x = true ∨ x = false) = (_ ∧ _) → False
  rw [eq_iff_iff]
  decide

theorem holds_universalRestrictor_iff {s : DEStrength} :
    universalRestrictor.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_antiAdd_iff.mpr
    ⟨(leftAntiAdditive_iff_isAntiAdditive _).mp leftAntiAdditive_every _,
      eq_false fun h ↦ p.nonuniversal.elim fun x hx ↦ hx (h x trivial)⟩) fun s hs h ↦ ?_
  obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
  have := (Signature.holdsFor_antiAddMult_iff.mp (h ⟨⟨Bool, ⊥⟩, ⟨true, id⟩⟩)).2.1
    (· = true) (· = false)
  simp [GQ.every, Pi.inf_apply] at this

theorem holds_withoutClause_iff {s : DEStrength} :
    withoutClause.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_antiAdd_iff.mpr
    ⟨fun V V' ↦ by
      show p.A ⊓ (V ⊔ V')ᶜ = (p.A ⊓ Vᶜ) ⊓ (p.A ⊓ V'ᶜ)
      rw [compl_sup, inf_inf_distrib_left], by simp⟩) fun s hs h ↦ ?_
  obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
  have := (Signature.holdsFor_antiAddMult_iff.mp (h ⟨Unit, ⊥⟩)).2.2
  simp at this

theorem holds_beforeClause_iff {s : DEStrength} :
    beforeClause.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_antiAdd_iff.mpr ⟨fun B C ↦ propext
    ⟨fun ⟨t, ht, h⟩ ↦ ⟨⟨t, ht, fun t' ⟨i, hi, hti⟩ ↦ h t' ⟨i, .inl hi, hti⟩⟩,
      ⟨t, ht, fun t' ⟨i, hi, hti⟩ ↦ h t' ⟨i, .inr hi, hti⟩⟩⟩,
    fun ⟨⟨t, ht, h₁⟩, ⟨s, hs, h₂⟩⟩ ↦ ⟨min t s,
      by rcases min_choice t s with h | h <;> rw [h] <;> assumption,
      fun t' ⟨i, hi, hti⟩ ↦ hi.elim (fun hi ↦ (min_le_left t s).trans_lt (h₁ t' ⟨i, hi, hti⟩))
        fun hi ↦ (min_le_right t s).trans_lt (h₂ t' ⟨i, hi, hti⟩)⟩⟩,
    eq_bot_iff.2 fun ⟨t, _, h⟩ ↦ lt_irrefl t (h t ⟨NonemptyInterval.pure t, trivial, by simp⟩)⟩)
    fun s hs h ↦ ?_
  obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
  have := (Signature.holdsFor_antiAddMult_iff.mp (h ⟨ℕ, ∅⟩)).2.2
  simp [beforeEver, timeTrace] at this

theorem holds_exceedsFamily_iff {s : DEStrength} :
    (classical exceedsFamily).Holds s.toSignature ↔ s ≤ .antiAdditive := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_antiAdd_iff.mpr
    ⟨fun Δ Δ' ↦ propext (show _ ∈ strictUpperBounds (Δ ∪ Δ') ↔ _ ∈ strictUpperBounds Δ ∧ _ by
      simp [strictUpperBounds, or_imp, forall_and]),
      eq_false fun h ↦ lt_irrefl _ (h (Set.mem_univ (p.μ p.x)))⟩) fun s hs h ↦ ?_
  obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
  have := (Signature.holdsFor_antiAddMult_iff.mp (h ⟨ℕ, ℕ, id, 1⟩)).2.1 ({2} : Set ℕ) {1}
  simp at this

theorem holds_clausalComparative_iff {s : DEStrength} :
    clausalComparative.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive :=
  holds_exceedsFamily_iff

theorem holds_tooTo_iff {s : DEStrength} :
    tooTo.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive :=
  holds_exceedsFamily_iff

theorem holds_doubtVerb_iff {s : DEStrength} :
    doubtVerb.licenser.Holds s.toSignature ↔ s ≤ .weak := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_anti_iff.mpr
    fun P Q hPQ hQ hP ↦ hQ fun _ hv ↦ hPQ (hP hv)) fun s hs h ↦ ?_
  have := (Signature.holdsFor_antiAdd_iff.mp ((h.toSignature_of_le (s := .antiAdditive)
    (by revert hs; cases s <;> decide)) ⟨Bool, .univ, true⟩)).1 {true} {false}
  revert this
  simp only [SetRel.core, Set.mem_ofPred_eq, Set.sup_eq_union, inf_Prop_eq, eq_iff_iff]
  decide

theorem holds_denyVerb_iff {s : DEStrength} :
    denyVerb.licenser.Holds s.toSignature ↔ s ≤ .antiAdditive := by
  refine holds_toSignature_iff (fun p ↦ Signature.holdsFor_antiAdd_iff.mpr
    ⟨fun P Q ↦ propext (show p.w ∈ p.R.core (P ∪ Q)ᶜ ↔ p.w ∈ p.R.core Pᶜ ∧ p.w ∈ p.R.core Qᶜ from
      ⟨fun h ↦ ⟨fun _ hv hP ↦ h hv (.inl hP), fun _ hv hQ ↦ h hv (.inr hQ)⟩,
        fun ⟨h₁, h₂⟩ _ hv hPQ ↦ hPQ.elim (h₁ hv) (h₂ hv)⟩),
      eq_false fun h ↦ p.serial.elim fun v hv ↦ h hv trivial⟩) fun s hs h ↦ ?_
  obtain rfl : s = .antiMorphic := by revert hs; cases s <;> decide
  have := (Signature.holdsFor_antiAddMult_iff.mp (h ⟨⟨Bool, .univ, true⟩, ⟨true, trivial⟩⟩)).2.1
    {true} {false}
  revert this
  simp only [SetRel.core, Set.mem_ofPred_eq, Set.inf_eq_inter, sup_Prop_eq, eq_iff_iff]
  decide

/-! ### Strawson licensers -/

theorem isStrawsonDE_onlyFocus : onlyFocus.licenser.IsStrawsonDE := fun p ↦ isStrawsonDE_only p.x

theorem not_holds_onlyFocus : ¬ onlyFocus.licenser.Holds .anti := fun h ↦
  not_antitone_truthSet_only (Signature.holdsFor_anti_iff.mp (h ⟨Bool, Unit, true⟩))

theorem isStrawsonDE_adversative : adversative.licenser.IsStrawsonDE := fun p ↦
  Desire.BestWorlds.isStrawsonDE_regret p.dox p.base p.g

theorem not_holds_adversative : ¬ adversative.licenser.Holds .anti := fun h ↦
  Desire.BestWorlds.not_antitone_truthSet_regret (Signature.holdsFor_anti_iff.mp
    (h ⟨Bool, fun _ ↦ {true}, fun _ ↦ .univ, fun _ ↦ [(· = false)]⟩))

theorem isStrawsonDE_superlative : superlative.licenser.IsStrawsonDE := fun p ↦
  Degree.isStrawsonDE_superlative p.μ p.x

theorem not_holds_superlative : ¬ superlative.licenser.Holds .anti := fun h ↦
  Degree.not_antitone_truthSet_superlative (Signature.holdsFor_anti_iff.mp
    (h ⟨Unit, Unit, ℕ, fun _ ↦ 0, ()⟩))

theorem isStrawsonDE_conditionalAntecedent : conditionalAntecedent.licenser.IsStrawsonDE :=
  fun p ↦ Conditional.isStrawsonDE_horizonCounterfactual p.horizon p.q

theorem not_holds_conditionalAntecedent : ¬ conditionalAntecedent.licenser.Holds .anti := fun h ↦
  Conditional.not_antitone_truthSet_horizonCounterfactual (Signature.holdsFor_anti_iff.mp
    (h ⟨Unit, Unit, fun _ ↦ .univ, .univ⟩))

theorem isStrawsonDE_sinceTemporal : sinceTemporal.licenser.IsStrawsonDE := fun p ↦
  isStrawsonDE_since p.ago

theorem not_holds_sinceTemporal : ¬ sinceTemporal.licenser.Holds .anti := fun h ↦
  not_antitone_truthSet_since (Signature.holdsFor_anti_iff.mp (h ⟨ℤ, (· - 5)⟩))

/-! ### Modal licensers and questions -/

/-- Over three worlds, the first accessing the other two, each the one world where one of two
individuals is a witness. -/
private def branching : SetRel (Fin 3) (Fin 3) := {p | p.1 = 0 ∧ p.2 ≠ 0}

private def witnessAt (d : Fin 2) : Set (Fin 3) := {d.succ}

theorem licensesFreeChoice_necessityFamily : (Licenser.modal necessityFamily).LicensesFreeChoice :=
  ⟨⟨Fin 3, branching⟩, Fin 2, witnessAt, .univ, by decide, 0,
    Exhaustification.mem_oMinus_of_forall_ne
      (fun v hv ↦ by
        obtain ⟨d, rfl⟩ := Fin.exists_succ_eq.2 hv.2
        exact Set.mem_iUnion₂.2 ⟨d, Finset.mem_univ _, rfl⟩)
      fun S _ hne ⟨d, hd⟩ h ↦ by
        have hd' : (d + 1) ∉ S := fun h' ↦ hne (Finset.eq_univ_iff_forall.2 fun x ↦ by
          fin_cases d <;> fin_cases x <;> simp_all)
        have := @h (d + 1).succ ⟨rfl, Fin.succ_ne_zero (d + 1)⟩
        obtain ⟨e, he, hev⟩ := Set.mem_iUnion₂.1 this
        exact hd' ((Fin.succ_injective _ (Set.mem_singleton_iff.1 hev)).symm ▸ he)⟩

theorem licensesFreeChoice_modalPossibility : modalPossibility.licenser.LicensesFreeChoice :=
  ⟨⟨Fin 3, branching⟩, Fin 2, witnessAt, .univ, by decide, 0, by
    show 0 ∈ Exhaustification.oMinus
      (fun S ↦ branching.preimage (Exhaustification.subDisj witnessAt S)) .univ
    rw [Exhaustification.oMinus_preimage_subDisj witnessAt branching Finset.univ_nonempty]
    exact Set.mem_iInter₂.2 fun d _ ↦ ⟨d.succ, rfl, rfl, d.succ_ne_zero⟩⟩

end LicensingContext

end PolarityItem
