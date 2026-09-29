module

public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Logic.Natural.Additivity
public import Linglib.Logic.Natural.Strawson.Basic
public import Linglib.Semantics.Quantification.Signatures
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Semantics.Quantification.Counting

/-!
# Model witnesses for the licensing contexts

A licensing context carries a strength of negation (`LicensingContext.strength`), which the
licensing relation reads in two ways: modulo presuppositions for weak items and outright for strong
items and positive polarity items. Each witnessed context has a model operator certifying the
reading it supports. A presupposition-free context has a `ContextWitness`, a function holding
every strength the context carries (`DEStrength.HoldsFor`); a Strawson-only context has a
`StrawsonWitness`, an operator into partial propositions that is Strawson downward entailing
([von-fintel-1999]) and, where the context is anti-additive, Strawson anti-additive
([gajewski-2011]).

The classical witnesses are complementation for negation, the sections of *every*, *no* and *few*,
and *at most two*, which is antitone but not anti-additive (`atMost_not_antiAdditive`), the
strictness that makes its context weak. The Strawson witnesses are the operators of
`Logic/Natural/Strawson/Basic.lean`: *only*, *regret*, *since*, superlatives and *would*. The
contexts of *before*, *without*, *deny*, *doubt*, *too … to* and the comparatives have no operator
yet, and questions and the generic contexts license by other routes than strength.

## Main declarations

* `PolarityItem.ContextWitness`, `PolarityItem.StrawsonWitness`: the two kinds of witness.
* `PolarityItem.ContextWitness.holdsFor_of_licenses`: at a classically witnessed context, licensing
  by strengthening means the operator holds the strength the item requires.

## References

* [von-fintel-1999]
* [gajewski-2011]
* [zwarts-1998]
* [icard-2012]
-/

@[expose] public section

namespace PolarityItem

open NaturalLogic Presupposition
open Quantifier Quantifier.GQ Quantifier.NP

/-- A **classical witness** of a licensing context is a function holding every strength of
negation the context carries. -/
structure ContextWitness (c : LicensingContext) where
  {α : Type*}
  {β : Type*}
  [latticeα : Lattice α]
  [latticeβ : Lattice β]
  /-- The context function. -/
  f : α → β
  /-- The function holds every strength the context carries. -/
  holdsFor : ∀ s : DEStrength, (s : WithBot DEStrength) ≤ c.strength → s.HoldsFor f

/-- A **Strawson witness** of a licensing context is an operator into partial propositions that is
Strawson downward entailing, and Strawson anti-additive where the context is anti-additive. -/
structure StrawsonWitness (c : LicensingContext) where
  {α : Type*}
  {W : Type*}
  [latticeα : Lattice α]
  /-- The context operator. -/
  op : α → PartialProp W
  isStrawsonDE : IsStrawsonDE op
  isStrawsonAA : (DEStrength.antiAdditive : WithBot DEStrength) ≤ c.strength →
    IsStrawsonAntiAdditive op

/-- The classical witness of a context of strength `s₀` given by a function holding `s₀`. -/
def ContextWitness.ofHoldsFor {c : LicensingContext} {s₀ : DEStrength}
    (hc : c.strength = s₀) {α β : Type*} [Lattice α] [Lattice β] {f : α → β}
    (hf : s₀.HoldsFor f) : ContextWitness c where
  f := f
  holdsFor _ hs := hf.of_le (WithBot.coe_le_coe.mp (hc ▸ hs))

/-! ### The at-most operator -/

/-- *At most n* of the restrictor are in the scope, over four individuals. -/
def atMost (n : ℕ) (restr scope : Set (Fin 4)) : Prop :=
  ∀ ws : List (Fin 4), ws.Nodup → (∀ w ∈ ws, restr w ∧ scope w) → ws.length ≤ n

theorem atMost_mono (n : ℕ) (restr p q : Set (Fin 4)) (hpq : ∀ w, p w → q w)
    (h : atMost n restr q) : atMost n restr p :=
  fun ws hnd hall ↦ h ws hnd fun w hw ↦ ⟨(hall w hw).1, hpq w (hall w hw).2⟩

/-- *At most two students*, with a fixed restrictor. -/
def atMost2_student : Set (Fin 4) → Set (Fin 4) := fun scope _ ↦ atMost 2 {0, 1} scope

theorem atMost_antitone_scope : Antitone atMost2_student :=
  fun p q hpq _ h ↦ atMost_mono 2 {0, 1} p q (fun _ hp ↦ hpq hp) h

/-- *At most one student*, with a fixed restrictor. -/
def atMost1_student : Set (Fin 4) → Set (Fin 4) := fun scope _ ↦ atMost 1 {0, 1} scope

/-- *At most one student* is not anti-additive, the strictness separating weak strength from
anti-additivity. -/
theorem atMost_not_antiAdditive : ¬ IsAntiAdditive atMost1_student := by
  intro hAA
  have h := isAntiAdditive_iff_mem.mp hAA
  let q : Set (Fin 4) := fun w ↦ w = 1
  let p : Set (Fin 4) := {0}
  have key : atMost1_student (p ∪ q) 0 ↔ atMost1_student p 0 ∧ atMost1_student q 0 := h p q 0
  have single : ∀ (r : Set (Fin 4)) (v : Fin 4), (∀ w, r w → w = v) → atMost1_student r 0 := by
    intro r v hr ws hnd hall
    rcases ws with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp
    · simp
    · have ha := hr a (hall a (List.mem_cons_self ..)).2
      have hb := hr b (hall b (List.mem_cons_of_mem _ (List.mem_cons_self ..))).2
      exact absurd (ha.trans hb.symm) (List.ne_of_not_mem_cons (List.Nodup.notMem hnd))
  have hp : atMost1_student p 0 := single p 0 fun _ hw ↦ hw
  have hq : atMost1_student q 0 := single q 1 fun _ hw ↦ hw
  have hpq : ¬ atMost1_student (p ∪ q) 0 := fun hle ↦ by
    have : ([(0 : Fin 4), 1]).length ≤ 1 := hle [0, 1] (by decide) fun w hw ↦ by
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact ⟨Or.inl rfl, Or.inl rfl⟩
      · rcases List.mem_singleton.mp hw' with rfl
        exact ⟨Or.inr rfl, Or.inr rfl⟩
    simp at this
  exact hpq (key.mpr ⟨hp, hq⟩)

/-! ### Classical witnesses -/

/-- Complementation, the witness of clausal negation, is anti-morphic. -/
def negationWitness : ContextWitness .negation :=
  .ofHoldsFor (s₀ := .antiMorphic) (by decide) (isAntiMorphic_compl (α := Set (Fin 4)))

/-- The restrictor section of *every*, the witness of the restrictor of a universal, is
anti-additive. -/
noncomputable def universalRestrictorWitness : ContextWitness .universalRestrictor :=
  .ofHoldsFor (s₀ := .antiAdditive) (f := fun R ↦ every (α := Bool) R fun _ ↦ False) (by decide)
    ((leftAntiAdditive_iff_isAntiAdditive _).mp leftAntiAdditive_every _)

/-- The scope section of *no*, the witness of *nobody*, is anti-additive. -/
noncomputable def nobodyWitness : ContextWitness .nobody :=
  .ofHoldsFor (s₀ := .antiAdditive) (f := no (α := Bool) fun _ ↦ True) (by decide)
    ((rightAntiAdditive_iff_isAntiAdditive _).mp rightAntiAdditive_no _)

/-- The scope section of *few* is antitone. -/
noncomputable def fewWitness : ContextWitness .few :=
  .ofHoldsFor (s₀ := .weak) (f := few (α := Bool) fun _ ↦ True) (by decide)
    (scopeAntitone_few _)

/-- *At most two* is antitone, and not anti-additive (`atMost_not_antiAdditive`). -/
def atMostWitness : ContextWitness .atMost :=
  .ofHoldsFor (s₀ := .weak) (by decide) atMost_antitone_scope

/-- At a classically witnessed context, licensing by strengthening means that the operator holds
the strength the item requires. -/
theorem ContextWitness.holdsFor_of_licenses {c : LicensingContext} (w : ContextWitness c)
    {e : PolarityItem} (hc : c.mechanism = .strengthening) (h : c.Licenses e) :
    ∀ r ∈ e.licensor, @DEStrength.HoldsFor _ _ w.latticeα w.latticeβ r w.f := by
  rcases h with ⟨-, r, hr, hle, -⟩ | ⟨hm, -⟩ | ⟨hm, -⟩
  · intro r' hr'
    rw [Option.mem_def] at hr hr'
    obtain rfl : r' = r := Option.some_injective _ (hr'.symm.trans hr)
    exact w.holdsFor r' hle
  all_goals exact absurd (hc.symm.trans hm) (by decide)

/-! ### Strawson witnesses -/

/-- Focus *only* is Strawson anti-additive and not classically antitone (`only_not_antitone`). -/
def onlyFocusWitness : StrawsonWitness .onlyFocus where
  op := only (W := Fin 4) (0 : Fin 4)
  isStrawsonDE := only_isStrawsonDE 0
  isStrawsonAA _ := only_isStrawsonAA 0

/-- Adversatives are Strawson anti-additive, with doxastic factivity, and not classically antitone
(`regret_not_antitone`). -/
def adversativeWitness : StrawsonWitness .adversative where
  op := regret (W := Fin 4) (fun w ↦ {w}) (fun _ ↦ {1})
  isStrawsonDE := regret_isStrawsonDE _ _
  isStrawsonAA _ := regret_isStrawsonAA _ _

/-- Temporal *since* is Strawson antitone, with its past-event presupposition, and not classically
antitone (`since_not_antitone`). -/
def sinceTemporalWitness : StrawsonWitness .sinceTemporal where
  op := since (W := Fin 4) (fun _ ↦ {0}) (fun _ ↦ ∅)
  isStrawsonDE := since_isStrawsonDE _ _
  isStrawsonAA h := absurd h (by decide)

/-- Superlatives are Strawson anti-additive in their restriction, with the designated-subject
presupposition. -/
def superlativeWitness : StrawsonWitness .superlative where
  op := (superlative (W := Fin 4) (id : Fin 4 → Fin 4) · 0)
  isStrawsonDE := superlative_isStrawsonDE _ _
  isStrawsonAA _ := superlative_isStrawsonAA _ _

/-- Conditional antecedents are Strawson anti-additive, with the presupposition that the modal base
admits the antecedent, and not classically antitone (`would_not_antitone`). -/
def conditionalAntecedentWitness : StrawsonWitness .conditionalAntecedent where
  op := (would (W := Fin 4) (fun _ ↦ Set.univ) · ∅)
  isStrawsonDE := would_isStrawsonDE _ _
  isStrawsonAA _ := would_isStrawsonAA _ _

end PolarityItem
