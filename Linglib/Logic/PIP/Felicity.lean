import Linglib.Logic.PIP.Semantics

/-!
# Felicity of PIP formulas

This file defines the felicity operator `F` on the terms and formulas of PIP.
A presupposition `φ|ψ` is felicitous iff `φ` and `ψ` are and `ψ` is true; a
conjunction `φ ∧ ψ` iff `φ` is and, whenever `φ` is true, `ψ` is; a quantifier,
abstraction or summation iff its body is for every value of the variables it
binds; the other connectives and relations iff their parts are. Felicity is
independent of truth. The PIP-value of a formula records its truth, its
felicity, its local variables and its label definitions, and two formulas are
intersubstitutable iff they have the same PIP-value in every model under every
assignment.

## Main definitions

* `Term.Felicitous`, `Formula.Felicitous` — the felicity operator `F`.
* `Value`, `Formula.value` — the PIP-value of a formula.

## Main statements

* `Formula.felicitous_atom`, `Formula.felicitous_conj`, … — the clauses of
  felicity, as simp lemmas; `Formula.felicitous_disj`, …,
  `Formula.felicitous_some` — the derived connectives.
* `Formula.felicitous_of_presupFree` — every infelicity traces to a
  presupposition.
* `Term.felicitous_sigma_conj_of_felicitous` — felicity of a discourse
  extended by a sentence reduces to the earlier discourse strictly implying
  the new sentence's felicity.

## References

* [keshet-abney-2024]
* [abney-keshet-2025]
* [karttunen-1974]
-/

namespace PIP

universe u v w

variable {V : Type u} {L : Type v} {P : ℕ → Type w} {α : Type*}

section Felicity

variable [DecidableEq V] (M : Model P α) (g : V → Set α)

mutual
/-- Felicity of a term: `τ|ψ` needs `τ` and `ψ` felicitous and `ψ` true;
abstraction and summation need their bodies felicitous for every value. -/
def Term.Felicitous (M : Model P α) (g : V → Set α) : Term V L P → Prop
  | .var _ => True
  | .bvar _ => True
  | .abs x φ => ∀ g', Set.EqOn g' g {x}ᶜ → φ.Felicitous M g'
  | .sigma x φ => ∀ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} → φ.Felicitous M g'
  | .inter s t => s.Felicitous M g ∧ t.Felicitous M g
  | .empty => True
  | .presup t ψ => t.Felicitous M g ∧ ψ.Felicitous M g ∧ ψ.Realize M g
/-- Felicity of a formula: the operator `F`, with asymmetric conjunction — the
first conjunct may satisfy the presuppositions of the second. -/
def Formula.Felicitous (M : Model P α) (g : V → Set α) : Formula V L P → Prop
  | .top => True
  | .atom _ w ts => w.Felicitous M g ∧ ∀ i, (ts i).Felicitous M g
  | .eq s t => s.Felicitous M g ∧ t.Felicitous M g
  | .subset s t => s.Felicitous M g ∧ t.Felicitous M g
  | .mem s t => s.Felicitous M g ∧ t.Felicitous M g
  | .sg t => t.Felicitous M g
  | .pl t => t.Felicitous M g
  | .neg φ => φ.Felicitous M g
  | .conj φ ψ => φ.Felicitous M g ∧ (φ.Realize M g → ψ.Felicitous M g)
  | .exists_ x φ => ∀ g', Set.EqOn g' g {x}ᶜ → φ.Felicitous M g'
  | .presup φ ψ => φ.Felicitous M g ∧ ψ.Felicitous M g ∧ ψ.Realize M g
  | .labelDef _ _ => True
  | .label _ => False
end

@[simp] theorem Term.felicitous_var (x : V) : (Term.var x : Term V L P).Felicitous M g :=
  trivial

@[simp] theorem Term.felicitous_bvar (x : V) : (Term.bvar x : Term V L P).Felicitous M g :=
  trivial

@[simp] theorem Term.felicitous_empty : (Term.empty : Term V L P).Felicitous M g := trivial

@[simp] theorem Term.felicitous_inter (s t : Term V L P) :
    (Term.inter s t).Felicitous M g ↔ s.Felicitous M g ∧ t.Felicitous M g := Iff.rfl

@[simp] theorem Term.felicitous_presup (t : Term V L P) (ψ : Formula V L P) :
    (Term.presup t ψ).Felicitous M g ↔
      t.Felicitous M g ∧ ψ.Felicitous M g ∧ ψ.Realize M g := Iff.rfl

theorem Term.felicitous_abs (x : V) (φ : Formula V L P) :
    (Term.abs x φ).Felicitous M g ↔ ∀ g', Set.EqOn g' g {x}ᶜ → φ.Felicitous M g' := Iff.rfl

theorem Term.felicitous_sigma (x : V) (φ : Formula V L P) :
    (Term.sigma x φ).Felicitous M g ↔
      ∀ g', Set.EqOn g' g {y | y ∉ φ.locals ∧ y ≠ x} → φ.Felicitous M g' := Iff.rfl

theorem Term.felicitous_abs_of_forall {x : V} {φ : Formula V L P}
    (h : ∀ g, φ.Felicitous M g) : (Term.abs x φ).Felicitous M g := fun _ _ => h _

theorem Term.felicitous_sigma_of_forall {x : V} {φ : Formula V L P}
    (h : ∀ g, φ.Felicitous M g) : (Term.sigma x φ).Felicitous M g := fun _ _ => h _

@[simp] theorem Formula.felicitous_top : (Formula.top : Formula V L P).Felicitous M g := trivial

@[simp] theorem Formula.felicitous_atom {n : ℕ} (r : P n) (w : Term V L P)
    (ts : Fin n → Term V L P) :
    (Formula.atom r w ts).Felicitous M g ↔ w.Felicitous M g ∧ ∀ i, (ts i).Felicitous M g :=
  Iff.rfl

@[simp] theorem Formula.felicitous_eq (s t : Term V L P) :
    (Formula.eq s t).Felicitous M g ↔ s.Felicitous M g ∧ t.Felicitous M g := Iff.rfl

@[simp] theorem Formula.felicitous_subset (s t : Term V L P) :
    (Formula.subset s t).Felicitous M g ↔ s.Felicitous M g ∧ t.Felicitous M g := Iff.rfl

@[simp] theorem Formula.felicitous_mem (s t : Term V L P) :
    (Formula.mem s t).Felicitous M g ↔ s.Felicitous M g ∧ t.Felicitous M g := Iff.rfl

@[simp] theorem Formula.felicitous_sg (t : Term V L P) :
    (Formula.sg t).Felicitous M g ↔ t.Felicitous M g := Iff.rfl

@[simp] theorem Formula.felicitous_pl (t : Term V L P) :
    (Formula.pl t).Felicitous M g ↔ t.Felicitous M g := Iff.rfl

@[simp] theorem Formula.felicitous_neg (φ : Formula V L P) :
    (Formula.neg φ).Felicitous M g ↔ φ.Felicitous M g := Iff.rfl

@[simp] theorem Formula.felicitous_conj (φ ψ : Formula V L P) :
    (Formula.conj φ ψ).Felicitous M g ↔
      φ.Felicitous M g ∧ (φ.Realize M g → ψ.Felicitous M g) := Iff.rfl

theorem Formula.felicitous_exists (x : V) (φ : Formula V L P) :
    (Formula.exists_ x φ).Felicitous M g ↔
      ∀ g', Set.EqOn g' g {x}ᶜ → φ.Felicitous M g' := Iff.rfl

@[simp] theorem Formula.felicitous_presup (φ ψ : Formula V L P) :
    (Formula.presup φ ψ).Felicitous M g ↔
      φ.Felicitous M g ∧ ψ.Felicitous M g ∧ ψ.Realize M g := Iff.rfl

@[simp] theorem Formula.felicitous_labelDef (X : L) (φ : Formula V L P) :
    (Formula.labelDef X φ).Felicitous M g := trivial

@[simp] theorem Formula.felicitous_label (X : L) :
    (Formula.label X : Formula V L P).Felicitous M g ↔ False := Iff.rfl

mutual
/-- A term without presuppositions is felicitous. -/
theorem Term.felicitous_of_presupFree :
    ∀ (g : V → Set α) (t : Term V L P), t.PresupFree → t.Felicitous M g
  | _, .var _, _ => trivial
  | _, .bvar _, _ => trivial
  | _, .abs _ φ, h => fun g' _ => Formula.felicitous_of_presupFree g' φ h
  | _, .sigma _ φ, h => fun g' _ => Formula.felicitous_of_presupFree g' φ h
  | g, .inter s t, h =>
      ⟨Term.felicitous_of_presupFree g s h.1, Term.felicitous_of_presupFree g t h.2⟩
  | _, .empty, _ => trivial
  | _, .presup _ _, h => h.elim
/-- Every infelicity traces to a presupposition: a formula without
presuppositions is felicitous. -/
theorem Formula.felicitous_of_presupFree :
    ∀ (g : V → Set α) (φ : Formula V L P), φ.PresupFree → φ.Felicitous M g
  | _, .top, _ => trivial
  | g, .atom _ w ts, h =>
      ⟨Term.felicitous_of_presupFree g w h.1,
        fun i => Term.felicitous_of_presupFree g (ts i) (h.2 i (List.mem_finRange i))⟩
  | g, .eq s t, h =>
      ⟨Term.felicitous_of_presupFree g s h.1, Term.felicitous_of_presupFree g t h.2⟩
  | g, .subset s t, h =>
      ⟨Term.felicitous_of_presupFree g s h.1, Term.felicitous_of_presupFree g t h.2⟩
  | g, .mem s t, h =>
      ⟨Term.felicitous_of_presupFree g s h.1, Term.felicitous_of_presupFree g t h.2⟩
  | g, .sg t, h => Term.felicitous_of_presupFree g t h
  | g, .pl t, h => Term.felicitous_of_presupFree g t h
  | g, .neg φ, h => Formula.felicitous_of_presupFree g φ h
  | g, .conj φ ψ, h =>
      ⟨Formula.felicitous_of_presupFree g φ h.1,
        fun _ => Formula.felicitous_of_presupFree g ψ h.2⟩
  | _, .exists_ _ φ, h => fun g' _ => Formula.felicitous_of_presupFree g' φ h
  | _, .presup _ _, h => h.elim
  | _, .labelDef _ _, _ => trivial
  | _, .label _, h => h.elim
end

theorem Term.felicitous_sgPronoun (x : V) (φ : Formula V L P) :
    (Term.sgPronoun x φ).Felicitous M g ↔
      (Term.sigma x φ).Felicitous M g ∧ ∃ a, (Term.sigma x φ).realize M g = {a} := by
  simp only [Term.sgPronoun, Term.felicitous_presup, Formula.felicitous_sg, Formula.realize_sg,
    and_self_left]

/-! ### Derived clauses -/

/-- `F(φ ∨ ψ)` iff `Fφ ∧ (¬φ → Fψ)`. -/
theorem Formula.felicitous_disj (φ ψ : Formula V L P) :
    (φ.disj ψ).Felicitous M g ↔ φ.Felicitous M g ∧ (¬ φ.Realize M g → ψ.Felicitous M g) :=
  Iff.rfl

/-- `F(φ → ψ)` iff `Fφ ∧ (φ → Fψ)`. -/
theorem Formula.felicitous_impl (φ ψ : Formula V L P) :
    (φ.impl ψ).Felicitous M g ↔ φ.Felicitous M g ∧ (φ.Realize M g → ψ.Felicitous M g) :=
  Iff.rfl

/-- `F(φ ↔ ψ)` iff `Fφ ∧ Fψ`. -/
theorem Formula.felicitous_iff (φ ψ : Formula V L P) :
    (φ.iff_ ψ).Felicitous M g ↔ φ.Felicitous M g ∧ ψ.Felicitous M g := by
  show (φ.impl ψ).Felicitous M g ∧ ((φ.impl ψ).Realize M g → (ψ.impl φ).Felicitous M g) ↔ _
  rw [Formula.felicitous_impl, Formula.felicitous_impl, Formula.realize_impl]
  constructor
  · rintro ⟨⟨hφ, h₁⟩, h₂⟩
    refine ⟨hφ, ?_⟩
    by_cases hp : φ.Realize M g
    · exact h₁ hp
    · exact (h₂ fun h => absurd h hp).1
  · rintro ⟨hφ, hψ⟩
    exact ⟨⟨hφ, fun _ => hψ⟩, fun _ => ⟨hψ, fun _ => hφ⟩⟩

/-- `F(∀xφ)` iff `∀x Fφ`. -/
theorem Formula.felicitous_forall (x : V) (φ : Formula V L P) :
    (Formula.forall_ x φ).Felicitous M g ↔ ∀ g', Set.EqOn g' g {x}ᶜ → φ.Felicitous M g' :=
  Iff.rfl

/-- `F(some(s, t))` iff `Fs ∧ Ft`. -/
theorem Formula.felicitous_some (s t : Term V L P) :
    (Formula.some_ s t).Felicitous M g ↔ s.Felicitous M g ∧ t.Felicitous M g :=
  show (s.Felicitous M g ∧ t.Felicitous M g) ∧ True ↔ _ from (and_true _).to_iff

/-- Felicity of a discourse extended by a sentence: `F Σw(γ ∧ φ)` iff, for every
assignment of the world and the local variables, `Fγ ∧ (γ → Fφ)`. -/
theorem Term.felicitous_sigma_conj (w : V) (γ φ : Formula V L P) :
    (Term.sigma w (γ.conj φ)).Felicitous M g ↔
      ∀ g', Set.EqOn g' g {y | y ∉ (γ.conj φ).locals ∧ y ≠ w} →
        γ.Felicitous M g' ∧ (γ.Realize M g' → φ.Felicitous M g') := Iff.rfl

/-- Given that the discourse so far is felicitous for all values of the local
variables, the extended discourse is felicitous iff the discourse so far
strictly implies the felicity of the new sentence. -/
theorem Term.felicitous_sigma_conj_of_felicitous (w : V) (γ φ : Formula V L P)
    (hγ : ∀ g', Set.EqOn g' g {y | y ∉ (γ.conj φ).locals ∧ y ≠ w} → γ.Felicitous M g') :
    (Term.sigma w (γ.conj φ)).Felicitous M g ↔
      ∀ g', Set.EqOn g' g {y | y ∉ (γ.conj φ).locals ∧ y ≠ w} →
        (γ.Realize M g' → φ.Felicitous M g') :=
  forall_congr' fun g' => imp_congr_right fun hg => and_iff_right (hγ g' hg)

/-! ### Meanings -/

/-- The PIP-value of a formula: its truth, its felicity, its local variables and
its label definitions. -/
@[ext]
structure Value (V : Type u) (L : Type v) (P : ℕ → Type w) where
  /-- Truth. -/
  truth : Prop
  /-- Felicity. -/
  felicity : Prop
  /-- The free local variables. -/
  locals : List V
  /-- The label definitions. -/
  defs : List (L × Formula V L P)

/-- The PIP-value of a formula. Two formulas are intersubstitutable iff they
have the same value in every model under every assignment; truth-equivalent
formulas need not be. -/
def Formula.value (φ : Formula V L P) : Value V L P :=
  ⟨φ.Realize M g, φ.Felicitous M g, φ.locals, φ.defs⟩

end Felicity

end PIP
