import Mathlib.Data.Fin.VecNotation
import Linglib.Logic.PIP.Basic
import Linglib.Data.Examples.KeshetAbney2024

/-!
# Keshet & Abney (2024): Intensional Anaphora

[keshet-abney-2024] [stone-1999] [brasoveanu-2010]

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
pronoun is fine; with a value-based presupposition of existence
([stone-1999], [brasoveanu-2010]) the mayoral candidates of (85), who all
exist, would wrongly license "she". This file states the paper's
discourses over `PIP` and proves the felicity conditions it derives from
them, at the level of a scenario (accessibility, antecedent description,
continuation) and on its models.

The paper's felicity conditions (78), (83), (87), (90), (97) quantify `∀w`
over worlds; the statements below take a world of evaluation `w₀` and an
assignment sending `w` to it.

## Main definitions

* `Scenario`, `Scenario.model` — an intensional model with worlds and
  entities as atoms, distributive predicates, `single`, `some`, `every` and
  accessibility.
* `descE`, `base`, `modal`, `pronoun`, `continuation`, `discourse` — the
  antecedent description, the modal base `β_w`, `might_w`/`must_w` (35), the
  summation pronoun `Σbφ | single(Σbφ)` (71), and the discourse
  `modal_w(Σwφ) ∧ E ≡ … ∧ cont_w(Σbφ | single(Σbφ))` with `φ` the label `E`
  before expansion and its definition after.
* `discourseMight`, `discourseMust`, `plain`, `bathroom` — (80b)+(82b), (89),
  (75)+(76), and (95).

## Main statements

* `expandSelf_discourse`, `expandSelf_bathroom` — expanding the label
  retrieves the antecedent description in the modal and at the pronoun.
* `fel_discourse_iff` — a modal discourse is felicitous at `w₀` iff the modal
  claim there implies a unique satisfier of the description at `w₀`.
* `fel_discourseMight_iff`, `not_fel_burger` — (83)/(87): with `might`, every
  world from which a description-world is accessible needs a unique
  satisfier; (79) fails at a world where Andrea is fasting.
* `fel_discourseMust_iff`, `fel_discourseMust_of_realistic` — (90): with a
  realistic modal base and unique satisfiers, `must` licenses the pronoun.
* `fel_plain` — (78): the unembedded discourse (74) is felicitous.
* `fel_bathroom_iff` — (97): the bathroom disjunction is felicitous iff a
  bathroom, if there is one, is unique.
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

/-- Predicate symbols: `single`, the quantifier relations `some` and `every`
over pluralities, accessibility `acc`, a world-indexed antecedent
description `desc` and continuation `cont`. -/
inductive Pred
  | single
  | some
  | every
  | acc
  | desc
  | cont
  deriving DecidableEq

/-! ### Scenarios -/

/-- The atoms of an intensional model: worlds and entities. -/
abbrev Atom (W E : Type) := W ⊕ E

variable {W E : Type}

/-- A world as a singleton plurality. -/
def world (w : W) : Set (Atom W E) := {Sum.inl w}

theorem world_inj {w w' : W} : (world w : Set (Atom W E)) = world w' ↔ w = w' :=
  Set.singleton_eq_singleton_iff.trans Sum.inl_injective.eq_iff

/-- A distributive predicate at a world: true of a nonempty plurality of
entities each satisfying `R` there. -/
def distr (R : W → E → Prop) (Wp X : Set (Atom W E)) : Prop :=
  ∃ w, Wp = world w ∧ X.Nonempty ∧ ∀ a ∈ X, ∃ e, a = Sum.inr e ∧ R w e

/-- A scenario: accessibility between worlds, the antecedent description and
the continuation's predicate, each relative to a world. -/
structure Scenario (W E : Type) where
  acc : W → W → Prop
  desc : W → E → Prop
  cont : W → E → Prop

/-- The model of a scenario. -/
def Scenario.model (S : Scenario W E) : Model Pred (Atom W E) where
  I p := fun {n} ts => match p, n, ts with
    | .single, 1, ts => ∃ a, ts 0 = {a}
    | .some, 2, ts => (ts 0 ∩ ts 1).Nonempty
    | .every, 2, ts => ts 0 ⊆ ts 1
    | .acc, 2, ts => ∃ w u, ts 0 = world w ∧ ts 1 = world u ∧ S.acc w u
    | .desc, 2, ts => distr S.desc (ts 0) (ts 1)
    | .cont, 2, ts => distr S.cont (ts 0) (ts 1)
    | _, _, _ => False

/-! ### The discourses -/

/-- `E ≡ desc_w([b]) ∧ single(b)`: the antecedent description of (80b),
with a bracketed local variable for the indefinite. -/
def descE : Formula Var Lab Pred :=
  .conj (.atom .desc ![.var .w, .bvar .b]) (.atom .single ![.var .b])

/-- `acc(w, u)`: `u` is accessible from `w`. -/
def access : Formula Var Lab Pred := .atom .acc ![.var .w, .var .u]

/-- `Σu acc(w, u)`: the modal base `β_w`. -/
def base : Term Var Lab Pred := .sigma .u access

/-- `q(β_w, Σwφ)`: `might_w(Σwφ)` for `q = some` and `must_w(Σwφ)` for
`q = every` (35). -/
def modal (q : Pred) (φ : Formula Var Lab Pred) : Formula Var Lab Pred :=
  .atom q ![base, .sigma .w φ]

/-- `Σbφ | single(Σbφ)`: the summation pronoun with its singular
presupposition (71), (82b). -/
def pronoun (φ : Formula Var Lab Pred) : Term Var Lab Pred :=
  .presup (.sigma .b φ) (.atom .single ![.sigma .b φ])

/-- `cont_w(Σbφ | single(Σbφ))`: the continuation (82b). -/
def continuation (φ : Formula Var Lab Pred) : Formula Var Lab Pred :=
  .atom .cont ![.var .w, pronoun φ]

/-- `q(β_w, Σwφ) ∧ E ≡ desc_w([b]) ∧ single(b) ∧ cont_w(Σbφ | single(Σbφ))`. -/
def discourse (q : Pred) (φ : Formula Var Lab Pred) : Formula Var Lab Pred :=
  .conj (.conj (modal q φ) (.labelDef .E descE)) (continuation φ)

/-- (80b) ∧ (82b): "Andrea might be eating a cheeseburger. It is large." -/
def discourseMight : Formula Var Lab Pred := discourse .some (.label .E)

/-- (89): "There must be some sort of animal in the shed. It's making quite a
racket!" -/
def discourseMust : Formula Var Lab Pred := discourse .every (.label .E)

/-- (75) ∧ (76): "Andrea is eating a cheeseburger. It is large.", with the
simple pronoun `b | single(b)`. -/
def plain : Formula Var Lab Pred :=
  .conj descE (.atom .cont ![.var .w, .presup (.var .b) (.atom .single ![.var .b])])

/-- (95): "Either there's no bathroom in this house or it's in a funny place.",
`(¬∃bX ∨ cont_w(ΣbX | single(ΣbX))) ∧ X ≡ desc_w([b]) ∧ single(b)`. -/
def bathroom : Formula Var Lab Pred :=
  .conj (.disj (.neg (.exists_ .b (.label .X))) (continuation (.label .X))) (.labelDef .X descE)

/-! ### Label expansion -/

theorem vecCons_map {α β : Type*} {n : ℕ} (f : α → β) (a : α) (v : Fin n → α) :
    (fun i => f (Matrix.vecCons a v i)) = Matrix.vecCons (f a) fun i => f (v i) :=
  Fin.comp_cons f a v

theorem vecEmpty_map {α β : Type*} (f : α → β) : (fun i => f (![] i)) = (![] : Fin 0 → β) :=
  funext fun i => i.elim0

theorem substLabel_descE (Y : Lab) (ψ : Formula Var Lab Pred) :
    Formula.substLabel Y ψ descE = descE := by
  simp only [descE, Formula.substLabel, Term.substLabel, vecCons_map, vecEmpty_map]

/-- Expanding the label retrieves the antecedent description in the modal
and at the pronoun. -/
theorem expandSelf_discourse (q : Pred) :
    (discourse q (.label .E)).expandSelf = discourse q descE := by
  rw [Formula.expandSelf, show (discourse q (.label .E)).defs = [(.E, descE)] from rfl]
  simp only [Formula.expand, List.foldr_cons, List.foldr_nil, discourse, modal, base, access,
    continuation, pronoun, Formula.substLabel, Term.substLabel, substLabel_descE, vecCons_map,
    vecEmpty_map, reduceIte]

theorem expandSelf_bathroom :
    bathroom.expandSelf =
      .conj (.disj (.neg (.exists_ .b descE)) (continuation descE)) (.labelDef .X descE) := by
  rw [Formula.expandSelf, show bathroom.defs = [(.X, descE)] from rfl]
  simp only [Formula.expand, List.foldr_cons, List.foldr_nil, bathroom, Formula.disj, continuation,
    pronoun, Formula.substLabel, Term.substLabel, substLabel_descE, vecCons_map, vecEmpty_map,
    reduceIte]

/-! ### Values and felicity at a world of evaluation -/

variable (S : Scenario W E) (h : Var → Set (Atom W E)) {w₀ : W}

theorem locals_descE : descE.locals = [.b] := rfl

theorem locals_access : access.locals = [] := rfl

theorem fel_descE : descE.fel S.model h :=
  ⟨Fin.forall_fin_two.2 ⟨trivial, trivial⟩, fun _ => Fin.forall_fin_one.2 trivial⟩

theorem fel_sigmaB_descE : (Term.sigma .b descE).fel S.model h := by
  simp [Term.fel, locals_descE, forallOver, fel_descE]

theorem fel_sigmaW_descE : (Term.sigma .w descE).fel S.model h := by
  simp [Term.fel, locals_descE, forallOver, fel_descE]

theorem fel_base : base.fel S.model h := by
  simp only [base, Term.fel, locals_access, List.filter_nil, forallOver]
  exact fun _ => Fin.forall_fin_two.2 ⟨trivial, trivial⟩

theorem fel_modal (q : Pred) : (modal q descE).fel S.model h :=
  Fin.forall_fin_two.2 ⟨fel_base S h, fel_sigmaW_descE S h⟩

theorem sat_access : access.sat S.model h ↔ ∃ w u, h .w = world w ∧ h .u = world u ∧ S.acc w u :=
  Iff.rfl

theorem sat_descE (X : Set (Atom W E)) :
    descE.sat S.model (Function.update h .b X) ↔
      ∃ w e, h .w = world w ∧ X = {Sum.inr e} ∧ S.desc w e := by
  show distr S.desc {a | a ∈ Function.update h .b X .w} {a | a ∈ Function.update h .b X .b} ∧
    (∃ a, {a' | a' ∈ Function.update h .b X .b} = {a}) ↔ _
  simp only [Set.ofPred_mem_eq, Function.update_self,
    Function.update_of_ne (show Var.w ≠ Var.b by decide), distr]
  constructor
  · rintro ⟨⟨w, hw, -, hall⟩, a, rfl⟩
    obtain ⟨e, rfl, he⟩ := hall a rfl
    exact ⟨w, e, hw, rfl, he⟩
  · rintro ⟨w, e, hw, rfl, he⟩
    exact ⟨⟨w, hw, ⟨_, rfl⟩, fun a ha => ⟨e, ha, he⟩⟩, _, rfl⟩

theorem mem_sigmaB_descE (hw : h .w = world w₀) (a : Atom W E) :
    (Term.sigma .b descE).mem S.model h a ↔ ∃ e, a = Sum.inr e ∧ S.desc w₀ e := by
  simp only [Term.mem, locals_descE, List.filter_cons, List.filter_nil, decide_eq_true_eq, ne_eq,
    not_true_eq_false, reduceIte, closeOver, sat_descE, hw, world_inj]
  constructor
  · rintro ⟨d, ⟨_, e, rfl, rfl, he⟩, ha⟩
    exact ⟨e, ha, he⟩
  · rintro ⟨e, rfl, he⟩
    exact ⟨_, ⟨w₀, e, rfl, rfl, he⟩, rfl⟩

theorem mem_sigmaW_descE (a : Atom W E) :
    (Term.sigma .w descE).mem S.model h a ↔ ∃ w e, a = Sum.inl w ∧ S.desc w e := by
  simp only [Term.mem, locals_descE, List.filter_cons, List.filter_nil, decide_eq_true_eq, ne_eq,
    reduceCtorEq, not_false_eq_true, reduceIte, closeOver, sat_descE, Function.update_self]
  constructor
  · rintro ⟨d, ⟨X, w, e, rfl, rfl, he⟩, ha⟩
    exact ⟨w, e, ha, he⟩
  · rintro ⟨w, e, rfl, he⟩
    exact ⟨world w, ⟨{Sum.inr e}, w, e, rfl, rfl, he⟩, rfl⟩

theorem mem_base (a : Atom W E) :
    base.mem S.model h a ↔ ∃ w u, h .w = world w ∧ a = Sum.inl u ∧ S.acc w u := by
  simp only [base, Term.mem, locals_access, List.filter_nil, closeOver, sat_access,
    Function.update_self, Function.update_of_ne (show Var.w ≠ Var.u by decide)]
  constructor
  · rintro ⟨d, ⟨w, u, hw, rfl, hacc⟩, ha⟩
    exact ⟨w, u, hw, ha, hacc⟩
  · rintro ⟨w, u, hw, rfl, hacc⟩
    exact ⟨world u, ⟨w, u, hw, rfl, hacc⟩, rfl⟩

theorem exists_eq_singleton_iff (P : E → Prop) :
    (∃ a : Atom W E, {x | ∃ e, x = Sum.inr e ∧ P e} = {a}) ↔ ∃! e, P e := by
  simp only [Set.eq_singleton_iff_unique_mem, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ⟨e, rfl, he⟩, hu⟩
    exact ⟨e, he, fun e' he' => Sum.inr_injective (hu _ ⟨e', rfl, he'⟩)⟩
  · rintro ⟨e, he, hu⟩
    exact ⟨_, ⟨e, rfl, he⟩, fun x ⟨e', hx, he'⟩ => hx ▸ congrArg Sum.inr (hu e' he')⟩

/-- `single(ΣbE)` at `w₀`: exactly one satisfier of the description there. -/
theorem sat_single_sigmaB (hw : h .w = world w₀) :
    (Formula.atom .single ![Term.sigma .b descE]).sat S.model h ↔ ∃! e, S.desc w₀ e := by
  show (∃ a, {x | (Term.sigma .b descE).mem S.model h x} = {a}) ↔ _
  simp only [mem_sigmaB_descE S h hw, exists_eq_singleton_iff]

theorem fel_pronoun_iff (hw : h .w = world w₀) :
    (pronoun descE).fel S.model h ↔ ∃! e, S.desc w₀ e := by
  show (Term.sigma .b descE).fel S.model h ∧ (∀ i, (![Term.sigma .b descE] i).fel S.model h) ∧
    (Formula.atom .single ![Term.sigma .b descE]).sat S.model h ↔ _
  simp only [Fin.forall_fin_one, Matrix.cons_val_zero, fel_sigmaB_descE, sat_single_sigmaB S h hw,
    true_and]

theorem fel_continuation_iff (hw : h .w = world w₀) :
    (continuation descE).fel S.model h ↔ ∃! e, S.desc w₀ e := by
  show (∀ i, (![Term.var Var.w, pronoun descE] i).fel S.model h) ↔ _
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, Term.fel,
    fel_pronoun_iff S h hw, true_and]

/-- A modal discourse is felicitous at `w₀` iff the modal claim there implies
a unique satisfier of the antecedent description at `w₀`. -/
theorem fel_discourse_iff (q : Pred) (hw : h .w = world w₀) :
    (discourse q descE).fel S.model h ↔ ((modal q descE).sat S.model h → ∃! e, S.desc w₀ e) := by
  show ((modal q descE).fel S.model h ∧ ((modal q descE).sat S.model h → True)) ∧
    ((modal q descE).sat S.model h ∧ True → (continuation descE).fel S.model h) ↔ _
  simp only [fel_modal, fel_continuation_iff S h hw, implies_true, and_true, true_and]

/-- `might_w(ΣwE)` at `w₀`: some accessible world has a satisfier. -/
theorem sat_modal_some (hw : h .w = world w₀) :
    (modal .some descE).sat S.model h ↔ ∃ u e, S.acc w₀ u ∧ S.desc u e := by
  show ({a | base.mem S.model h a} ∩ {a | (Term.sigma .w descE).mem S.model h a}).Nonempty ↔ _
  simp only [Set.Nonempty, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_base, mem_sigmaW_descE, hw,
    world_inj]
  constructor
  · rintro ⟨_, ⟨_, u, rfl, rfl, hacc⟩, w, e, ⟨⟩, he⟩
    exact ⟨u, e, hacc, he⟩
  · rintro ⟨u, e, hacc, he⟩
    exact ⟨_, ⟨_, u, rfl, rfl, hacc⟩, u, e, rfl, he⟩

/-- `must_w(ΣwE)` at `w₀`: every accessible world has a satisfier. -/
theorem sat_modal_every (hw : h .w = world w₀) :
    (modal .every descE).sat S.model h ↔ ∀ u, S.acc w₀ u → ∃ e, S.desc u e := by
  show {a | base.mem S.model h a} ⊆ {a | (Term.sigma .w descE).mem S.model h a} ↔ _
  simp only [Set.subset_def, Set.mem_ofPred_eq, mem_base, mem_sigmaW_descE, hw, world_inj]
  constructor
  · intro H u hu
    obtain ⟨w, e, hw', he⟩ := H _ ⟨_, u, rfl, rfl, hu⟩
    cases Sum.inl.inj hw'
    exact ⟨e, he⟩
  · rintro H _ ⟨_, u, rfl, rfl, hu⟩
    obtain ⟨e, he⟩ := H u hu
    exact ⟨u, e, rfl, he⟩

/-- (83): with `might`, the discourse is felicitous at `w₀` iff, whenever a
world with a satisfier is accessible from `w₀`, `w₀` itself has a unique
satisfier. -/
theorem fel_discourseMight_iff (hw : h .w = world w₀) :
    discourseMight.expandSelf.fel S.model h ↔
      ((∃ u e, S.acc w₀ u ∧ S.desc u e) → ∃! e, S.desc w₀ e) := by
  rw [discourseMight, expandSelf_discourse, fel_discourse_iff S h _ hw, sat_modal_some S h hw]

/-- (90): with `must`, the discourse is felicitous at `w₀` iff, whenever every
world accessible from `w₀` has a satisfier, `w₀` has a unique one. -/
theorem fel_discourseMust_iff (hw : h .w = world w₀) :
    discourseMust.expandSelf.fel S.model h ↔
      ((∀ u, S.acc w₀ u → ∃ e, S.desc u e) → ∃! e, S.desc w₀ e) := by
  rw [discourseMust, expandSelf_discourse, fel_discourse_iff S h _ hw, sat_modal_every S h hw]

/-- (88)–(90): a realistic modal base and the scalar implicature that a
satisfier is unique make the `must` discourse felicitous at every world. -/
theorem fel_discourseMust_of_realistic (hr : ∀ w, S.acc w w)
    (hu : ∀ w, (∃ e, S.desc w e) → ∃! e, S.desc w e) (hw : h .w = world w₀) :
    discourseMust.expandSelf.fel S.model h :=
  (fel_discourseMust_iff S h hw).2 fun H => hu _ (H _ (hr _))

/-- (78): the unembedded discourse (74) is felicitous under every assignment,
the assertion `single(b)` satisfying the pronoun's presupposition. -/
theorem fel_plain : plain.fel S.model h := by
  refine ⟨fel_descE S h, fun hd => ?_⟩
  show ∀ i, (![Term.var Var.w, Term.presup (.var .b) (.atom .single ![.var .b])] i).fel S.model h
  exact Fin.forall_fin_two.2 ⟨trivial, trivial, Fin.forall_fin_one.2 trivial, hd.2⟩

/-- (97): the bathroom disjunction is felicitous at `w₀` iff a bathroom there,
if any, is unique. -/
theorem fel_bathroom_iff (hw : h .w = world w₀) :
    bathroom.expandSelf.fel S.model h ↔ ((∃ e, S.desc w₀ e) → ∃! e, S.desc w₀ e) := by
  rw [expandSelf_bathroom]
  show ((Formula.neg (.exists_ .b descE)).disj (continuation descE)).fel S.model h ∧ (_ → True) ↔ _
  rw [Formula.fel_disj, fel_continuation_iff S h hw]
  show ((∀ d, descE.fel S.model (Function.update h .b d)) ∧
    (¬¬(∃ d, descE.sat S.model (Function.update h .b d)) → _)) ∧ _ ↔ _
  simp only [fel_descE, implies_true, true_and, and_true, not_not, sat_descE, hw, world_inj]
  constructor
  · exact fun H ⟨e, he⟩ => H ⟨_, w₀, e, rfl, rfl, he⟩
  · rintro H ⟨_, _, e, rfl, rfl, he⟩
    exact H ⟨e, he⟩

/-! ### Possible burgers -/

/-- (79): at `false` Andrea is fasting and at `true` she is eating a
cheeseburger, and for all anyone knows at either world, either is actual. -/
def burger : Scenario Bool Unit where
  acc _ _ := True
  desc w _ := w = true
  cont _ _ := True

/-- (79) is infelicitous at the world where Andrea is fasting but might be
eating a cheeseburger: `ΣbE` is empty there. -/
theorem not_fel_burger (h : Var → Set (Atom Bool Unit)) (hw : h .w = world false) :
    ¬ discourseMight.expandSelf.fel burger.model h := by
  rw [fel_discourseMight_iff burger h hw]
  intro H
  obtain ⟨_, h1⟩ := (H ⟨true, (), trivial, rfl⟩).exists
  exact Bool.false_ne_true h1

end KeshetAbney2024
