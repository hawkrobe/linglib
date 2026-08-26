import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Function.Basic
import Linglib.Logic.PIP.Syntax

/-!
# PIP: truth

Pluralities are sets of atoms. A term denotes a plurality — a variable its
assignment, `⋃{x : φ}` and `Σxφ` the union of the values of `x` over the
assignments agreeing with the current one outside the bound variables (for
summation, also outside the local variables of `φ`) that satisfy `φ` — and a
formula is true or false classically, with presuppositions and label
definitions transparent and an unexpanded label false. A discourse
`φ₁, …, φₙ` means `Σw(φ₁ ∧ … ∧ φₙ)` and is true iff that plurality of worlds is
nonempty.

## Main definitions

* `Model` — the interpretation of relation symbols over pluralities.
* `Term.Mem`, `Term.realize`, `Formula.Realize` — value and truth relative to
  a model and an assignment.

## Main statements

* `Formula.realize_atom`, `Formula.realize_conj`, … — the clauses of truth,
  as simp lemmas; `Formula.realize_disj`, …, `Formula.realize_some` — the
  derived connectives.
* `Formula.realize_exists_iff_abs_nonempty` — `∃xφ` is true iff `⋃{x : φ}` is
  nonempty, when `φ` is false of the null plurality.
* `Formula.realize_elim` — the PIP constructs are eliminable: the translation
  preserves truth.

## References

* [keshet-abney-2024]
* [abney-keshet-2025]
-/

namespace PIP

universe u v w

variable {V : Type u} {L : Type v} {P : ℕ → Type w} {α : Type*}

/-- A model: pluralities are sets of atoms `α`, and each `n`-ary relation symbol
is interpreted over a world plurality and a tuple of `n` pluralities. -/
structure Model (P : ℕ → Type w) (α : Type u) where
  /-- The interpretation of relation symbols. -/
  I : ∀ {n : ℕ}, P n → Set α → (Fin n → Set α) → Prop

section Semantics

variable [DecidableEq V]

mutual
/-- Membership in the value of a term: a variable's assignment, the union of the
abstracted values, the union of the summed values over assignments agreeing
outside the summation variable and the local variables, intersection, the
empty plurality, and the body of a presupposed term. -/
def Term.Mem (M : Model P α) (g : V → Set α) : Term V L P → α → Prop
  | .var x, a => a ∈ g x
  | .bvar x, a => a ∈ g x
  | .abs x φ, a => ∃ g', Set.EqOn g' g {x}ᶜ ∧ a ∈ g' x ∧ φ.Realize M g'
  | .sigma x φ, a =>
      ∃ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} ∧ a ∈ g' x ∧ φ.Realize M g'
  | .inter s t, a => s.Mem M g a ∧ t.Mem M g a
  | .empty, _ => False
  | .presup t _, a => t.Mem M g a
/-- Truth of a formula: classical, with presuppositions and label definitions
transparent and an unexpanded label false. -/
def Formula.Realize (M : Model P α) (g : V → Set α) : Formula V L P → Prop
  | .top => True
  | .atom r w ts => M.I r {a | w.Mem M g a} fun i => {a | (ts i).Mem M g a}
  | .eq s t => {a | s.Mem M g a} = {a | t.Mem M g a}
  | .subset s t => {a | s.Mem M g a} ⊆ {a | t.Mem M g a}
  | .mem s t => ∃ a, {b | s.Mem M g b} = {a} ∧ t.Mem M g a
  | .sg t => ∃ a, {b | t.Mem M g b} = {a}
  | .pl t => ∃ a b, a ≠ b ∧ t.Mem M g a ∧ t.Mem M g b
  | .neg φ => ¬ φ.Realize M g
  | .conj φ ψ => φ.Realize M g ∧ ψ.Realize M g
  | .exists_ x φ => ∃ g', Set.EqOn g' g {x}ᶜ ∧ φ.Realize M g'
  | .presup φ _ => φ.Realize M g
  | .labelDef _ _ => True
  | .label _ => False
end

variable (M : Model P α) (g : V → Set α)

/-- The value of a term. -/
def Term.realize (t : Term V L P) : Set α := {a | t.Mem M g a}

@[simp] theorem Term.mem_realize {t : Term V L P} {a : α} : a ∈ t.realize M g ↔ t.Mem M g a :=
  Iff.rfl

@[simp] theorem Term.realize_var (x : V) : (Term.var x : Term V L P).realize M g = g x := rfl

@[simp] theorem Term.realize_bvar (x : V) : (Term.bvar x : Term V L P).realize M g = g x := rfl

@[simp] theorem Term.realize_inter (s t : Term V L P) :
    (Term.inter s t).realize M g = s.realize M g ∩ t.realize M g := rfl

@[simp] theorem Term.realize_empty : (Term.empty : Term V L P).realize M g = ∅ := rfl

@[simp] theorem Term.realize_presup (t : Term V L P) (ψ : Formula V L P) :
    (Term.presup t ψ).realize M g = t.realize M g := rfl

theorem Term.mem_realize_abs (x : V) (φ : Formula V L P) (a : α) :
    a ∈ (Term.abs x φ).realize M g ↔ ∃ g', Set.EqOn g' g {x}ᶜ ∧ a ∈ g' x ∧ φ.Realize M g' :=
  Iff.rfl

theorem Term.mem_realize_sigma (x : V) (φ : Formula V L P) (a : α) :
    a ∈ (Term.sigma x φ).realize M g ↔
      ∃ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} ∧ a ∈ g' x ∧ φ.Realize M g' := Iff.rfl

@[simp] theorem Formula.realize_top : (Formula.top : Formula V L P).Realize M g ↔ True := Iff.rfl

@[simp] theorem Formula.realize_atom {n : ℕ} (r : P n) (w : Term V L P)
    (ts : Fin n → Term V L P) :
    (Formula.atom r w ts).Realize M g ↔ M.I r (w.realize M g) fun i => (ts i).realize M g :=
  Iff.rfl

@[simp] theorem Formula.realize_eq (s t : Term V L P) :
    (Formula.eq s t).Realize M g ↔ s.realize M g = t.realize M g := Iff.rfl

@[simp] theorem Formula.realize_subset (s t : Term V L P) :
    (Formula.subset s t).Realize M g ↔ s.realize M g ⊆ t.realize M g := Iff.rfl

@[simp] theorem Formula.realize_mem (s t : Term V L P) :
    (Formula.mem s t).Realize M g ↔ ∃ a, s.realize M g = {a} ∧ a ∈ t.realize M g := Iff.rfl

@[simp] theorem Formula.realize_sg (t : Term V L P) :
    (Formula.sg t).Realize M g ↔ ∃ a, t.realize M g = {a} := Iff.rfl

@[simp] theorem Formula.realize_pl (t : Term V L P) :
    (Formula.pl t).Realize M g ↔ ∃ a b, a ≠ b ∧ a ∈ t.realize M g ∧ b ∈ t.realize M g :=
  Iff.rfl

@[simp] theorem Formula.realize_neg (φ : Formula V L P) :
    (Formula.neg φ).Realize M g ↔ ¬ φ.Realize M g := Iff.rfl

@[simp] theorem Formula.realize_conj (φ ψ : Formula V L P) :
    (Formula.conj φ ψ).Realize M g ↔ φ.Realize M g ∧ ψ.Realize M g := Iff.rfl

theorem Formula.realize_exists (x : V) (φ : Formula V L P) :
    (Formula.exists_ x φ).Realize M g ↔ ∃ g', Set.EqOn g' g {x}ᶜ ∧ φ.Realize M g' := Iff.rfl

@[simp] theorem Formula.realize_presup (φ ψ : Formula V L P) :
    (Formula.presup φ ψ).Realize M g ↔ φ.Realize M g := Iff.rfl

@[simp] theorem Formula.realize_labelDef (X : L) (φ : Formula V L P) :
    (Formula.labelDef X φ).Realize M g ↔ True := Iff.rfl

@[simp] theorem Formula.realize_label (X : L) :
    (Formula.label X : Formula V L P).Realize M g ↔ False := Iff.rfl

/-! ### Derived clauses -/

theorem Formula.realize_disj (φ ψ : Formula V L P) :
    (φ.disj ψ).Realize M g ↔ φ.Realize M g ∨ ψ.Realize M g :=
  show ¬(¬φ.Realize M g ∧ ¬ψ.Realize M g) ↔ _ from or_iff_not_and_not.symm

theorem Formula.realize_impl (φ ψ : Formula V L P) :
    (φ.impl ψ).Realize M g ↔ (φ.Realize M g → ψ.Realize M g) :=
  show ¬(φ.Realize M g ∧ ¬ψ.Realize M g) ↔ _ from not_and_not_right

theorem Formula.realize_iff (φ ψ : Formula V L P) :
    (φ.iff_ ψ).Realize M g ↔ (φ.Realize M g ↔ ψ.Realize M g) := by
  show (φ.impl ψ).Realize M g ∧ (ψ.impl φ).Realize M g ↔ _
  rw [Formula.realize_impl, Formula.realize_impl]
  exact iff_iff_implies_and_implies.symm

theorem Formula.realize_forall (x : V) (φ : Formula V L P) :
    (Formula.forall_ x φ).Realize M g ↔ ∀ g', Set.EqOn g' g {x}ᶜ → φ.Realize M g' :=
  show ¬(∃ g', Set.EqOn g' g {x}ᶜ ∧ ¬φ.Realize M g') ↔ _ by
    simp only [not_exists, not_and, not_not]

theorem Formula.realize_some (s t : Term V L P) :
    (Formula.some_ s t).Realize M g ↔ (s.realize M g ∩ t.realize M g).Nonempty :=
  show ¬(s.realize M g ∩ t.realize M g = ∅) ↔ _ from Set.nonempty_iff_ne_empty.symm

/-- `∃xφ` is true iff `⋃{x : φ}` is nonempty, provided `φ` is false when `x` is
the null plurality — the standing assumption that predicates are false of the
null individual. -/
theorem Formula.realize_exists_iff_abs_nonempty (x : V) (φ : Formula V L P)
    (h : ∀ g', g' x = ∅ → ¬ φ.Realize M g') :
    (Formula.exists_ x φ).Realize M g ↔ ((Term.abs x φ).realize M g).Nonempty := by
  constructor
  · rintro ⟨g', hg, hφ⟩
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr fun he => h g' he hφ
    exact ⟨a, g', hg, ha, hφ⟩
  · rintro ⟨_, g', hg, _, hφ⟩
    exact ⟨g', hg, hφ⟩

/-! ### Eliminability -/

theorem Formula.realize_closeList (xs : List V) (φ : Formula V L P) :
    ∀ g : V → Set α, (φ.closeList xs).Realize M g ↔
      ∃ g', Set.EqOn g' g {y | y ∉ xs} ∧ φ.Realize M g' := by
  induction xs with
  | nil =>
    refine fun g => ⟨fun h => ⟨g, fun _ _ => rfl, h⟩, ?_⟩
    rintro ⟨g', hg, h⟩
    rwa [show g' = g from funext fun y => hg (by simp)] at h
  | cons x xs ih =>
    intro g
    show (∃ g₁, Set.EqOn g₁ g {x}ᶜ ∧ (φ.closeList xs).Realize M g₁) ↔ _
    simp only [ih]
    constructor
    · rintro ⟨g₁, hg₁, g', hg', h⟩
      refine ⟨g', fun y hy => ?_, h⟩
      simp only [List.mem_cons, not_or, Set.mem_ofPred_eq] at hy
      exact (hg' hy.2).trans (hg₁ hy.1)
    · rintro ⟨g', hg', h⟩
      refine ⟨Function.update g x (g' x), fun y hy => Function.update_of_ne hy _ _, g', ?_, h⟩
      intro y hy
      by_cases hyx : y = x
      · subst hyx; simp
      · rw [Function.update_of_ne hyx]
        exact hg' (by simp only [Set.mem_ofPred_eq, List.mem_cons, not_or]; exact ⟨hyx, hy⟩)

mutual
/-- The translation preserves values. -/
theorem Term.mem_elim : ∀ (g : V → Set α) (t : Term V L P) (a : α),
    t.elim.Mem M g a ↔ t.Mem M g a
  | _, .var _, _ => Iff.rfl
  | _, .bvar _, _ => Iff.rfl
  | g, .abs x φ, a =>
      show (∃ g', Set.EqOn g' g {x}ᶜ ∧ a ∈ g' x ∧ φ.elim.Realize M g') ↔ ∃ g', _ from
        exists_congr fun _ => and_congr_right fun _ => and_congr_right fun _ =>
          Formula.realize_elim _ φ
  | g, .sigma x φ, a => by
      show (∃ g₁, Set.EqOn g₁ g {x}ᶜ ∧ a ∈ g₁ x ∧ (φ.elim.closeList _).Realize M g₁) ↔
        ∃ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} ∧ a ∈ g' x ∧ φ.Realize M g'
      simp only [Formula.realize_closeList, Formula.realize_elim]
      constructor
      · rintro ⟨g₁, hg₁, ha, g', hg', h⟩
        refine ⟨g', fun y hy => ?_, ?_, h⟩
        · have hy' : y ∉ φ.locals.filter (· ≠ x) := fun h' => hy.1 (List.mem_filter.1 h').1
          exact (hg' hy').trans (hg₁ hy.2)
        · rwa [hg' (by simp)]
      · rintro ⟨g', hg', ha, h⟩
        refine ⟨Function.update g x (g' x), fun y hy => Function.update_of_ne hy _ _,
          by simpa using ha, g', fun y hy => ?_, h⟩
        by_cases hyx : y = x
        · subst hyx; simp
        · rw [Function.update_of_ne hyx]
          exact hg' ⟨fun hl => hy (List.mem_filter.2 ⟨hl, by simpa using hyx⟩), hyx⟩
  | g, .inter s t, a => and_congr (Term.mem_elim g s a) (Term.mem_elim g t a)
  | _, .empty, _ => Iff.rfl
  | g, .presup t _, a => Term.mem_elim g t a
/-- The PIP constructs are eliminable: the translation preserves truth. -/
theorem Formula.realize_elim : ∀ (g : V → Set α) (φ : Formula V L P),
    φ.elim.Realize M g ↔ φ.Realize M g
  | _, .top => Iff.rfl
  | g, .atom r w ts => by
      show M.I r {a | w.elim.Mem M g a} (fun i => {a | (ts i).elim.Mem M g a}) ↔ _
      rw [Set.ext fun a => Term.mem_elim g w a,
        show (fun i => {a | (ts i).elim.Mem M g a}) = fun i => {a | (ts i).Mem M g a} from
          funext fun i => Set.ext fun a => Term.mem_elim g (ts i) a]
      exact Iff.rfl
  | g, .eq s t => by
      show {a | s.elim.Mem M g a} = {a | t.elim.Mem M g a} ↔ _
      rw [Set.ext fun a => Term.mem_elim g s a, Set.ext fun a => Term.mem_elim g t a]
      exact Iff.rfl
  | g, .subset s t => by
      show {a | s.elim.Mem M g a} ⊆ {a | t.elim.Mem M g a} ↔ _
      rw [Set.ext fun a => Term.mem_elim g s a, Set.ext fun a => Term.mem_elim g t a]
      exact Iff.rfl
  | g, .mem s t => by
      show (∃ a, {b | s.elim.Mem M g b} = {a} ∧ t.elim.Mem M g a) ↔ _
      rw [Set.ext fun a => Term.mem_elim g s a]
      exact exists_congr fun a => and_congr_right fun _ => Term.mem_elim g t a
  | g, .sg t => by
      show (∃ a, {b | t.elim.Mem M g b} = {a}) ↔ _
      rw [Set.ext fun a => Term.mem_elim g t a]
      exact Iff.rfl
  | g, .pl t =>
      exists_congr fun a => exists_congr fun b => and_congr_right fun _ =>
        and_congr (Term.mem_elim g t a) (Term.mem_elim g t b)
  | g, .neg φ => not_congr (Formula.realize_elim g φ)
  | g, .conj φ ψ => and_congr (Formula.realize_elim g φ) (Formula.realize_elim g ψ)
  | g, .exists_ x φ =>
      exists_congr fun _ => and_congr_right fun _ => Formula.realize_elim _ φ
  | g, .presup φ _ => Formula.realize_elim g φ
  | _, .labelDef _ _ => Iff.rfl
  | _, .label _ => Iff.rfl
end

end Semantics

end PIP
