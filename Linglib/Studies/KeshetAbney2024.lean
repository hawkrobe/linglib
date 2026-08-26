import Linglib.Core.Data.Fin.VecNotation
import Linglib.Logic.PIP.Felicity
import Linglib.Logic.PIP.Intensional
import Linglib.Data.Examples.KeshetAbney2024

/-!
# Keshet & Abney (2024): Intensional Anaphora

A pronoun presupposes that its antecedent description has a non-empty
extension (9). In PIP (`Logic/PIP/Basic.lean`) the antecedent description of a
summation pronoun is a formula label, so "Andrea might be eating a
cheeseburger. #It is large." (79) is `might_w(ΣwE) ∧ E ≡ … ∧ large_w(ΣbE |
single(ΣbE))`: the world variable of `E` is bound by the summation inside
`might` at its first use and by the discourse at the pronoun, so the
pronoun's description is evaluated at the discourse world, and felicity (83)
demands `single(ΣbE)` in every world where Andrea *might* be eating one —
including the worlds where she is not. With `must` (88)–(90) the realistic
modal base guarantees the description at the world of evaluation, and the
pronoun is fine; with a value-based presupposition of existence the mayoral
candidates of (85), who all exist, would wrongly license "she". This file
states the paper's discourses over `PIP` and proves the felicity conditions
it derives from them, at the level of a scenario (accessibility, antecedent
description, continuation) and on its models.

The paper's felicity conditions (78), (83), (87), (90), (97) quantify `∀w`
over worlds; the statements below take a world of evaluation `w₀` and an
assignment sending `w` to it.

## Main definitions

* `Scenario`, `Scenario.model` — an intensional model with accessibility, an
  antecedent description and a continuation.
* `descE`, `base`, `Modal.apply`, `continuation`, `discourse` — the antecedent
  description, the modal base `β_w`, `might_w`/`must_w` (35), the continuation
  with its summation pronoun `Σbφ | single(Σbφ)` (71), and the discourse
  `modal_w(Σwφ) ∧ E ≡ … ∧ cont_w(Σbφ | single(Σbφ))` with `φ` the label `E`
  before expansion and its definition after.
* `discourseMight`, `discourseMust`, `plain`, `bathroom` — (80b)+(82b), (89),
  (75)+(76), and (95).

## Main statements

* `expandSelf_discourseMight`, `expandSelf_discourseMust`, `expandSelf_bathroom`
  — expanding the label retrieves the antecedent description in the modal and
  at the pronoun.
* `felicitous_discourse_iff` — a modal discourse is felicitous at `w₀` iff the
  modal claim there implies a unique satisfier of the description at `w₀`.
* `felicitous_discourseMight_iff`, `not_felicitous_burger` — (83)/(87): with
  `might`, every world from which a description-world is accessible needs a
  unique satisfier; (79) fails at a world where Andrea is fasting.
* `felicitous_discourseMust_iff`, `felicitous_discourseMust_of_realistic` —
  (90): with a realistic modal base and unique satisfiers, `must` licenses the
  pronoun.
* `felicitous_plain` — (78): the unembedded discourse (74) is felicitous.
* `felicitous_bathroom_iff` — (97): the bathroom disjunction is felicitous iff
  a bathroom, if there is one, is unique.

## References

* [keshet-abney-2024]
* [stone-1999]
* [brasoveanu-2010]
-/

namespace KeshetAbney2024

open PIP

/-- The variables of the discourses: the world `w`, the modal-base world `u`,
the antecedent's individual `b`. -/
inductive Var
  | w
  | u
  | b
  deriving DecidableEq

/-- The formula labels: the antecedent description `E`, and `X` of (95). -/
inductive Lab
  | E
  | X
  deriving DecidableEq

/-- Relation symbols, by number of non-world arguments: accessibility between
worlds, and the antecedent description and continuation of entities. -/
inductive Sym : ℕ → Type
  | acc : Sym 1
  | desc : Sym 1
  | cont : Sym 1

/-- Terms of the discourses. -/
abbrev Tm := Term Var Lab Sym

/-- Formulas of the discourses. -/
abbrev Fm := Formula Var Lab Sym

/-! ### Scenarios -/

variable {W E : Type}

/-- A scenario: accessibility between worlds, the antecedent description and
the continuation's predicate, each relative to a world. -/
structure Scenario (W E : Type) where
  acc : W → W → Prop
  desc : W → E → Prop
  cont : W → E → Prop

/-- The model of a scenario. -/
def Scenario.model (S : Scenario W E) : Model Sym (Atom W E) :=
  Model.intensional fun {_} r w as => match r with
    | .acc => ∃ u, as 0 = Sum.inl u ∧ S.acc w u
    | .desc => ∃ e, as 0 = Sum.inr e ∧ S.desc w e
    | .cont => ∃ e, as 0 = Sum.inr e ∧ S.cont w e

/-! ### The discourses -/

/-- `E ≡ desc_w([b]) ∧ single(b)`: the antecedent description of (80b),
with a bracketed local variable for the indefinite. -/
def descE : Fm := .conj (.atom .desc (.var .w) ![.bvar .b]) (.sg (.var .b))

/-- `acc(w, u)`: `u` is accessible from `w`. -/
def access : Fm := .atom .acc (.var .w) ![.var .u]

/-- `Σu acc(w, u)`: the modal base `β_w`. -/
def base : Tm := .sigma .u access

/-- The one-place modals (35): `might_w(Σwφ) = some(β_w, Σwφ)` and
`must_w(Σwφ) = every(β_w, Σwφ)`. -/
inductive Modal
  | might
  | must

/-- A modal applied to its base and its prejacent. -/
def Modal.apply : Modal → Tm → Tm → Fm
  | .might, β, ψ => .some_ β ψ
  | .must, β, ψ => .subset β ψ

/-- `cont_w(Σbφ | single(Σbφ))`: the continuation (82b), with the summation pronoun
`Term.sgPronoun` (71). -/
def continuation (φ : Fm) : Fm := .atom .cont (.var .w) ![Term.sgPronoun .b φ]

/-- `modal_w(Σwφ) ∧ E ≡ desc_w([b]) ∧ single(b) ∧ cont_w(Σbφ | single(Σbφ))`. -/
def discourse (m : Modal) (φ : Fm) : Fm :=
  .conj (.conj (m.apply base (.sigma .w φ)) (.labelDef .E descE)) (continuation φ)

/-- (80b) ∧ (82b): "Andrea might be eating a cheeseburger. It is large." -/
def discourseMight : Fm := discourse .might (.label .E)

/-- (89): "There must be some sort of animal in the shed. It's making quite a
racket!" -/
def discourseMust : Fm := discourse .must (.label .E)

/-- (75) ∧ (76): "Andrea is eating a cheeseburger. It is large.", with the
simple pronoun `b | single(b)`. -/
def plain : Fm := .conj descE (.atom .cont (.var .w) ![.presup (.var .b) (.sg (.var .b))])

/-- (95): "Either there's no bathroom in this house or it's in a funny place.",
`(¬∃bX ∨ cont_w(ΣbX | single(ΣbX))) ∧ X ≡ desc_w([b]) ∧ single(b)`. -/
def bathroom : Fm :=
  .conj (.disj (.neg (.exists_ .b (.label .X))) (continuation (.label .X))) (.labelDef .X descE)

/-! ### Label expansion -/

theorem expandSelf_discourseMight : discourseMight.expandSelf = discourse .might descE := by
  rw [Formula.expandSelf, show discourseMight.defs = [(.E, descE)] from rfl, Formula.expand]
  simp only [List.foldl_cons, List.foldl_nil, discourseMight, discourse, Modal.apply, Formula.some_,
    continuation, Term.sgPronoun, descE, access, base, Formula.substLabels, Term.substLabels,
    assignment, Matrix.comp_vecCons, Matrix.comp_vecEmpty, reduceIte, Option.getD_some]

theorem expandSelf_discourseMust : discourseMust.expandSelf = discourse .must descE := by
  rw [Formula.expandSelf, show discourseMust.defs = [(.E, descE)] from rfl, Formula.expand]
  simp only [List.foldl_cons, List.foldl_nil, discourseMust, discourse, Modal.apply,
    continuation, Term.sgPronoun, descE, access, base, Formula.substLabels, Term.substLabels,
    assignment, Matrix.comp_vecCons, Matrix.comp_vecEmpty, reduceIte, Option.getD_some]

theorem expandSelf_bathroom :
    bathroom.expandSelf =
      .conj (.disj (.neg (.exists_ .b descE)) (continuation descE)) (.labelDef .X descE) := by
  rw [Formula.expandSelf, show bathroom.defs = [(.X, descE)] from rfl, Formula.expand]
  simp only [List.foldl_cons, List.foldl_nil, bathroom, Formula.disj, continuation, Term.sgPronoun,
    descE, Formula.substLabels, Term.substLabels, assignment, Matrix.comp_vecCons,
    Matrix.comp_vecEmpty, reduceIte, Option.getD_some]

/-! ### Values and felicity at a world of evaluation -/

variable (S : Scenario W E) (h : Var → Set (Atom W E)) {w₀ : W}

theorem locals_descE : descE.locals = [.b] := rfl

theorem felicitous_descE : descE.Felicitous S.model h :=
  Formula.felicitous_of_presupFree _ _ _ (by decide)

theorem felicitous_access : access.Felicitous S.model h :=
  Formula.felicitous_of_presupFree _ _ _ (by decide)

theorem realize_descE :
    descE.Realize S.model h ↔ ∃ w e, h .w = world w ∧ h .b = {Sum.inr e} ∧ S.desc w e := by
  simp only [descE, Formula.realize_conj, Formula.realize_atom, Formula.realize_sg,
    Matrix.comp_vecCons, Matrix.comp_vecEmpty, Term.realize_var, Term.realize_bvar, Scenario.model,
    Model.intensional_apply₁, Matrix.cons_val_zero]
  constructor
  · rintro ⟨⟨w, hw, -, hall⟩, a, ha⟩
    obtain ⟨e, rfl, he⟩ := hall a (by rw [ha]; exact Set.mem_singleton a)
    exact ⟨w, e, hw, ha, he⟩
  · rintro ⟨w, e, hw, hb, he⟩
    exact ⟨⟨w, hw, ⟨_, by rw [hb]; exact Set.mem_singleton _⟩,
      fun a ha => ⟨e, by rw [hb] at ha; exact ha, he⟩⟩, _, hb⟩

/-- `ΣbE` at `w₀`: the satisfiers of the description there. -/
theorem realize_sigmaB_descE (hw : h .w = world w₀) :
    (Term.sigma .b descE).realize S.model h = {a | ∃ e, a = Sum.inr e ∧ S.desc w₀ e} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_ofPred_eq]
  simp only [realize_descE]
  constructor
  · rintro ⟨g', hg, ha, w, e, hw', hb, he⟩
    rw [hg (by decide), hw, world_inj] at hw'
    subst hw'
    rw [hb] at ha
    exact ⟨e, ha, he⟩
  · rintro ⟨e, rfl, he⟩
    refine ⟨Function.update h .b {Sum.inr e}, fun y hy => Function.update_of_ne hy.2 _ _,
      by simp, w₀, e, ?_, by simp, he⟩
    rw [Function.update_of_ne (by decide), hw]

/-- `ΣwE`: the worlds with a satisfier of the description. -/
theorem realize_sigmaW_descE :
    (Term.sigma .w descE).realize S.model h = {a | ∃ w e, a = Sum.inl w ∧ S.desc w e} := by
  ext a
  rw [Term.mem_realize_sigma, Set.mem_ofPred_eq]
  simp only [realize_descE]
  constructor
  · rintro ⟨g', -, ha, w, e, hw', -, he⟩
    rw [hw'] at ha
    exact ⟨w, e, ha, he⟩
  · rintro ⟨w, e, rfl, he⟩
    refine ⟨Function.update (Function.update h .w (world w)) .b {Sum.inr e}, fun y hy => ?_,
      by simp [world], w, e, by simp, by simp, he⟩
    simp only [Set.mem_ofPred_eq, locals_descE, List.mem_singleton] at hy
    rw [Function.update_of_ne hy.1, Function.update_of_ne hy.2]

/-- The modal base: the worlds accessible from the world of `w`. -/
theorem realize_base :
    base.realize S.model h = {a | ∃ w u, h .w = world w ∧ a = Sum.inl u ∧ S.acc w u} := by
  ext a
  rw [base, Term.mem_realize_sigma, Set.mem_ofPred_eq]
  simp only [access, Formula.realize_atom, Matrix.comp_vecCons, Matrix.comp_vecEmpty,
    Term.realize_var, Scenario.model, Model.intensional_apply₁, Matrix.cons_val_zero]
  constructor
  · rintro ⟨g', hg, ha, w, hw, -, hall⟩
    obtain ⟨u, rfl, hacc⟩ := hall a ha
    exact ⟨w, u, (hg (by decide)).symm.trans hw, rfl, hacc⟩
  · rintro ⟨w, u, hw, rfl, hacc⟩
    refine ⟨Function.update h .u (world u), fun y hy => Function.update_of_ne hy.2 _ _,
      by simp [world], w, by rw [Function.update_of_ne (by decide), hw],
      ⟨Sum.inl u, by simp [world]⟩, fun a ha => by simp only [world] at ha; exact ⟨u, ha, hacc⟩⟩

/-- `might_w(ΣwE)` at `w₀`: some accessible world has a satisfier. -/
theorem realize_might (hw : h .w = world w₀) :
    (Modal.apply .might base (.sigma .w descE)).Realize S.model h ↔
      ∃ u e, S.acc w₀ u ∧ S.desc u e := by
  rw [Modal.apply, Formula.realize_some, realize_base, realize_sigmaW_descE]
  constructor
  · rintro ⟨_, ⟨w, u, hw', rfl, hacc⟩, w', e, ⟨⟩, he⟩
    obtain rfl := world_inj.1 (hw.symm.trans hw')
    exact ⟨u, e, hacc, he⟩
  · rintro ⟨u, e, hacc, he⟩
    exact ⟨_, ⟨w₀, u, hw, rfl, hacc⟩, u, e, rfl, he⟩

/-- `must_w(ΣwE)` at `w₀`: every accessible world has a satisfier. -/
theorem realize_must (hw : h .w = world w₀) :
    (Modal.apply .must base (.sigma .w descE)).Realize S.model h ↔
      ∀ u, S.acc w₀ u → ∃ e, S.desc u e := by
  rw [Modal.apply, Formula.realize_subset, realize_base, realize_sigmaW_descE, Set.subset_def]
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro H u hu
    obtain ⟨w', e, hw', he⟩ := H _ ⟨w₀, u, hw, rfl, hu⟩
    cases Sum.inl.inj hw'
    exact ⟨e, he⟩
  · rintro H _ ⟨w, u, hw', rfl, hu⟩
    obtain rfl := world_inj.1 (hw.symm.trans hw')
    obtain ⟨e, he⟩ := H u hu
    exact ⟨u, e, rfl, he⟩

theorem felicitous_modal (m : Modal) :
    (m.apply base (.sigma .w descE)).Felicitous S.model h := by
  cases m <;> simp only [Modal.apply, Formula.felicitous_some, Formula.felicitous_subset, base,
    Term.felicitous_sigma_of_forall _ _ (felicitous_access S),
    Term.felicitous_sigma_of_forall _ _ (felicitous_descE S), and_self]

theorem felicitous_pronoun_iff (hw : h .w = world w₀) :
    (Term.sgPronoun .b descE).Felicitous S.model h ↔ ∃! e, S.desc w₀ e := by
  rw [Term.felicitous_sgPronoun, realize_sigmaB_descE S h hw, exists_eq_singleton_iff]
  exact and_iff_right (Term.felicitous_sigma_of_forall _ _ (felicitous_descE S))

theorem felicitous_continuation_iff (hw : h .w = world w₀) :
    (continuation descE).Felicitous S.model h ↔ ∃! e, S.desc w₀ e := by
  simp only [continuation, Formula.felicitous_atom, Term.felicitous_var, Fin.forall_fin_one,
    Matrix.cons_val_zero, true_and, felicitous_pronoun_iff S h hw]

/-- A modal discourse is felicitous at `w₀` iff the modal claim there implies
a unique satisfier of the antecedent description at `w₀`. -/
theorem felicitous_discourse_iff (m : Modal) (hw : h .w = world w₀) :
    (discourse m descE).Felicitous S.model h ↔
      ((m.apply base (.sigma .w descE)).Realize S.model h → ∃! e, S.desc w₀ e) := by
  simp only [discourse, Formula.felicitous_conj, Formula.realize_conj, Formula.felicitous_labelDef,
    Formula.realize_labelDef, felicitous_modal, felicitous_continuation_iff S h hw, implies_true,
    and_true, true_and]

/-- (83): with `might`, the discourse is felicitous at `w₀` iff, whenever a
world with a satisfier is accessible from `w₀`, `w₀` itself has a unique
satisfier. -/
theorem felicitous_discourseMight_iff (hw : h .w = world w₀) :
    discourseMight.expandSelf.Felicitous S.model h ↔
      ((∃ u e, S.acc w₀ u ∧ S.desc u e) → ∃! e, S.desc w₀ e) := by
  rw [expandSelf_discourseMight, felicitous_discourse_iff S h _ hw, realize_might S h hw]

/-- (90): with `must`, the discourse is felicitous at `w₀` iff, whenever every
world accessible from `w₀` has a satisfier, `w₀` has a unique one. -/
theorem felicitous_discourseMust_iff (hw : h .w = world w₀) :
    discourseMust.expandSelf.Felicitous S.model h ↔
      ((∀ u, S.acc w₀ u → ∃ e, S.desc u e) → ∃! e, S.desc w₀ e) := by
  rw [expandSelf_discourseMust, felicitous_discourse_iff S h _ hw, realize_must S h hw]

/-- (88)–(90): a realistic modal base and the scalar implicature that a
satisfier is unique make the `must` discourse felicitous at every world. -/
theorem felicitous_discourseMust_of_realistic (hr : ∀ w, S.acc w w)
    (hu : ∀ w, (∃ e, S.desc w e) → ∃! e, S.desc w e) (hw : h .w = world w₀) :
    discourseMust.expandSelf.Felicitous S.model h :=
  (felicitous_discourseMust_iff S h hw).2 fun H => hu _ (H _ (hr _))

/-- (78): the unembedded discourse (74) is felicitous under every assignment,
the assertion `single(b)` satisfying the pronoun's presupposition. -/
theorem felicitous_plain : plain.Felicitous S.model h :=
  ⟨felicitous_descE S h, fun hd => ⟨trivial, Fin.forall_fin_one.2 ⟨trivial, trivial, hd.2⟩⟩⟩

theorem felicitous_exists_descE : (Formula.exists_ .b descE).Felicitous S.model h :=
  fun g' _ => felicitous_descE S g'

theorem realize_exists_descE (hw : h .w = world w₀) :
    (Formula.exists_ .b descE).Realize S.model h ↔ ∃ e, S.desc w₀ e := by
  rw [Formula.realize_exists]
  simp only [realize_descE]
  constructor
  · rintro ⟨g', hg, w, e, hw', -, he⟩
    obtain rfl := world_inj.1 (hw.symm.trans ((hg (by simp)).symm.trans hw'))
    exact ⟨e, he⟩
  · rintro ⟨e, he⟩
    exact ⟨Function.update h .b {Sum.inr e}, fun y hy => Function.update_of_ne hy _ _, w₀, e,
      by rw [Function.update_of_ne (by decide), hw], by simp, he⟩

/-- (97): the bathroom disjunction is felicitous at `w₀` iff a bathroom there,
if any, is unique. -/
theorem felicitous_bathroom_iff (hw : h .w = world w₀) :
    bathroom.expandSelf.Felicitous S.model h ↔
      ((∃ e, S.desc w₀ e) → ∃! e, S.desc w₀ e) := by
  rw [expandSelf_bathroom]
  simp only [Formula.felicitous_conj, Formula.felicitous_disj, Formula.felicitous_neg,
    Formula.felicitous_labelDef, Formula.realize_neg, not_not, felicitous_exists_descE,
    realize_exists_descE S h hw, felicitous_continuation_iff S h hw, implies_true, and_true,
    true_and]

/-! ### Possible burgers -/

/-- (79): at `false` Andrea is fasting and at `true` she is eating a
cheeseburger, and for all anyone knows at either world, either is actual. -/
def burger : Scenario Bool Unit where
  acc _ _ := True
  desc w _ := w = true
  cont _ _ := True

/-- (79) is infelicitous at the world where Andrea is fasting but might be
eating a cheeseburger: `ΣbE` is empty there. -/
theorem not_felicitous_burger (h : Var → Set (Atom Bool Unit)) (hw : h .w = world false) :
    ¬ discourseMight.expandSelf.Felicitous burger.model h := by
  rw [felicitous_discourseMight_iff burger h hw]
  intro H
  obtain ⟨_, h1⟩ := (H ⟨true, (), trivial, rfl⟩).exists
  exact Bool.false_ne_true h1

end KeshetAbney2024
