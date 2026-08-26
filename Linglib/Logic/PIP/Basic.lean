import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Function.Basic

/-!
# PIP — Plural Intensional Presuppositional predicate calculus

PIP is first-order predicate calculus with set abstraction, equality and the
set-theoretic relations `⊆`, `∈`, `∩`, `∅` and the cardinality predicates `SG`,
`PL`, whose domain consists of pluralities (sets of atoms, worlds among them),
supplemented by five eliminable constructs: bracketed *local* variables `[x]`
slated for unselective closure, summation `Σxφ`, formula labels `X ≡ φ` and
their uses `X`, world arguments on predicates, and presuppositions `φ|ψ`. A
discourse `φ₁, …, φₙ` means `Σw(φ₁ ∧ … ∧ φₙ)` and is true iff that plurality of
worlds is nonempty; it is felicitous iff its label definitions form a function,
it has no free non-local variables, and the felicity operator `F` — defined on
the presupposition operator and the primitive connectives, with asymmetric
conjunction — holds of its closure. Truth and felicity are independent: `φ|ψ`
is true iff `φ` is.

Relation symbols are indexed by arity and take a world as a distinguished
argument. Summation and abstraction bind by name: `Σxφ` denotes the union of
the values of `x` over the assignments agreeing with the current one outside
`x` and the local variables of `φ`.

## Main definitions

* `Term`, `Formula` — the mutual syntax; `Term.locals`, `Formula.locals` the
  local variables; `Term.subst`, `Formula.subst` substitution for a variable.
* `Model` — the interpretation of relation symbols over pluralities.
* `Term.realize`, `Formula.Realize` — value and truth relative to a model and
  an assignment.
* `Term.Felicitous`, `Formula.Felicitous` — the felicity operator `F`;
  `Term.PresupFree`, `Formula.PresupFree` — expressions without
  presuppositions.
* `Formula.substLabels`, `Formula.defs`, `Formula.expand`, `Formula.expandSelf`
  — label assignment and expansion; `Formula.disj`, `Formula.impl`, `Formula.iff_`,
  `Formula.forall_`, `Formula.some_` — the defined connectives.
* `Value`, `Formula.value` — the PIP-value of a formula (truth, felicity, local
  variables, label definitions), whose equality is intersubstitutability.
* `Term.elim`, `Formula.elim` — the translation eliminating the PIP
  constructs.
* `Atom`, `world`, `Model.intensional` — intensional models whose atoms are
  worlds and entities, with relation symbols interpreted distributively.

## Main statements

* `Formula.realize_elim` — the PIP constructs are eliminable: the translation
  preserves truth.
* `Formula.felicitous_of_presupFree` — every infelicity traces to a
  presupposition.
* `Formula.felicitous_disj`, `Formula.felicitous_impl`,
  `Formula.felicitous_iff`, `Formula.felicitous_forall` — the derived felicity
  clauses.
* `Formula.realize_exists_iff_abs_nonempty` — `∃xφ` is true iff `⋃{x : φ}` is
  nonempty, when `φ` is false of the null plurality.
* `Term.felicitous_sigma_conj_of_felicitous` — felicity of a discourse extended
  by a sentence reduces to the earlier discourse strictly implying the new
  sentence's felicity.

## References

* [keshet-abney-2024]
* [abney-keshet-2025]
* [karttunen-1974]
-/

namespace PIP

universe u v w

mutual
/-- Terms: external variables, bracketed local variables `[x]`, set abstraction
`⋃{x : φ}`, summation `Σxφ`, intersection, the empty plurality, and a term with
a presupposition `τ|ψ`. -/
inductive Term (V : Type u) (L : Type v) (P : ℕ → Type w)
  | var (x : V)
  | bvar (x : V)
  | abs (x : V) (φ : Formula V L P)
  | sigma (x : V) (φ : Formula V L P)
  | inter (s t : Term V L P)
  | empty
  | presup (t : Term V L P) (ψ : Formula V L P)
/-- Formulas: the constant `⊤`, predication `P_w(τ₁, …, τₙ)`, equality, inclusion,
membership, the cardinality predicates `SG` and `PL`, negation, conjunction,
selective existential quantification, presupposition `φ|ψ`, label definition
`X ≡ φ`, and label use `X`. -/
inductive Formula (V : Type u) (L : Type v) (P : ℕ → Type w)
  | top
  | atom {n : ℕ} (r : P n) (w : Term V L P) (ts : Fin n → Term V L P)
  | eq (s t : Term V L P)
  | subset (s t : Term V L P)
  | mem (s t : Term V L P)
  | sg (t : Term V L P)
  | pl (t : Term V L P)
  | neg (φ : Formula V L P)
  | conj (φ ψ : Formula V L P)
  | exists_ (x : V) (φ : Formula V L P)
  | presup (φ ψ : Formula V L P)
  | labelDef (X : L) (φ : Formula V L P)
  | label (X : L)
end

variable {V : Type u} {L : Type v} {P : ℕ → Type w} {α : Type*}

/-- Disjunction, as `¬(¬φ ∧ ¬ψ)`. -/
def Formula.disj (φ ψ : Formula V L P) : Formula V L P := .neg (.conj (.neg φ) (.neg ψ))

/-- Implication, as `¬(φ ∧ ¬ψ)`. -/
def Formula.impl (φ ψ : Formula V L P) : Formula V L P := .neg (.conj φ (.neg ψ))

/-- Biconditional, as `(φ → ψ) ∧ (ψ → φ)`. -/
def Formula.iff_ (φ ψ : Formula V L P) : Formula V L P := (φ.impl ψ).conj (ψ.impl φ)

/-- Universal quantification, as `¬∃x¬φ`. -/
def Formula.forall_ (x : V) (φ : Formula V L P) : Formula V L P := .neg (.exists_ x (.neg φ))

/-- Overlap `some(s, t)`, as `¬(s ∩ t = ∅)`. -/
def Formula.some_ (s t : Term V L P) : Formula V L P := .neg (.eq (.inter s t) .empty)

/-! ### Vector arguments -/

theorem vecCons_map {β γ : Type*} {n : ℕ} (f : β → γ) (a : β) (v : Fin n → β) :
    (fun i => f (Matrix.vecCons a v i)) = Matrix.vecCons (f a) fun i => f (v i) :=
  Fin.comp_cons f a v

theorem vecEmpty_map {β γ : Type*} (f : β → γ) : (fun i => f (![] i)) = (![] : Fin 0 → γ) :=
  funext fun i => i.elim0

/-! ### Local variables and substitution -/

section Syntax

variable [DecidableEq V]

mutual
/-- The local variables of a term: bracketed occurrences at top level, with
summation and set abstraction binding theirs. -/
def Term.locals : Term V L P → List V
  | .var _ => []
  | .bvar x => [x]
  | .abs x φ => φ.locals.filter (· ≠ x)
  | .sigma _ _ => []
  | .inter s t => s.locals ++ t.locals
  | .empty => []
  | .presup t ψ => t.locals ++ ψ.locals
/-- The local variables of a formula. -/
def Formula.locals : Formula V L P → List V
  | .top => []
  | .atom _ w ts => w.locals ++ (List.finRange _).flatMap fun i => (ts i).locals
  | .eq s t => s.locals ++ t.locals
  | .subset s t => s.locals ++ t.locals
  | .mem s t => s.locals ++ t.locals
  | .sg t => t.locals
  | .pl t => t.locals
  | .neg φ => φ.locals
  | .conj φ ψ => φ.locals ++ ψ.locals
  | .exists_ x φ => φ.locals.filter (· ≠ x)
  | .presup φ ψ => φ.locals ++ ψ.locals
  | .labelDef _ _ => []
  | .label _ => []
end

/-- Bracket a variable: `[x]` for `x`; other terms are unchanged. -/
def Term.bracket : Term V L P → Term V L P
  | .var x => .bvar x
  | t => t

mutual
/-- Substitute `t` for the variable `x`, the β-reduction of `λx`: a bracketed
occurrence `[x]` becomes the bracketed substitute, binders of `x` are skipped,
and no capture check is made. -/
def Term.subst (x : V) (t : Term V L P) : Term V L P → Term V L P
  | .var y => if y = x then t else .var y
  | .bvar y => if y = x then t.bracket else .bvar y
  | .abs y φ => .abs y (if y = x then φ else Formula.subst x t φ)
  | .sigma y φ => .sigma y (if y = x then φ else Formula.subst x t φ)
  | .inter s u => .inter (Term.subst x t s) (Term.subst x t u)
  | .empty => .empty
  | .presup s ψ => .presup (Term.subst x t s) (Formula.subst x t ψ)
/-- Substitute `t` for the variable `x`. -/
def Formula.subst (x : V) (t : Term V L P) : Formula V L P → Formula V L P
  | .top => .top
  | .atom r w ts => .atom r (Term.subst x t w) fun i => Term.subst x t (ts i)
  | .eq s u => .eq (Term.subst x t s) (Term.subst x t u)
  | .subset s u => .subset (Term.subst x t s) (Term.subst x t u)
  | .mem s u => .mem (Term.subst x t s) (Term.subst x t u)
  | .sg s => .sg (Term.subst x t s)
  | .pl s => .pl (Term.subst x t s)
  | .neg φ => .neg (Formula.subst x t φ)
  | .conj φ ψ => .conj (Formula.subst x t φ) (Formula.subst x t ψ)
  | .exists_ y φ => .exists_ y (if y = x then φ else Formula.subst x t φ)
  | .presup φ ψ => .presup (Formula.subst x t φ) (Formula.subst x t ψ)
  | .labelDef X φ => .labelDef X (Formula.subst x t φ)
  | .label X => .label X
end

end Syntax

/-! ### Expressions without presuppositions -/

mutual
/-- A term with no presupposition operator and no label use. -/
def Term.PresupFree : Term V L P → Prop
  | .var _ => True
  | .bvar _ => True
  | .abs _ φ => φ.PresupFree
  | .sigma _ φ => φ.PresupFree
  | .inter s t => s.PresupFree ∧ t.PresupFree
  | .empty => True
  | .presup _ _ => False
/-- A formula with no presupposition operator and no label use. -/
def Formula.PresupFree : Formula V L P → Prop
  | .top => True
  | .atom _ w ts => w.PresupFree ∧ ∀ i ∈ List.finRange _, (ts i).PresupFree
  | .eq s t => s.PresupFree ∧ t.PresupFree
  | .subset s t => s.PresupFree ∧ t.PresupFree
  | .mem s t => s.PresupFree ∧ t.PresupFree
  | .sg t => t.PresupFree
  | .pl t => t.PresupFree
  | .neg φ => φ.PresupFree
  | .conj φ ψ => φ.PresupFree ∧ ψ.PresupFree
  | .exists_ _ φ => φ.PresupFree
  | .presup _ _ => False
  | .labelDef _ φ => φ.PresupFree
  | .label _ => False
end

mutual
/-- Decidability of `Term.PresupFree`. -/
def Term.decPresupFree : (t : Term V L P) → Decidable t.PresupFree
  | .var _ => isTrue trivial
  | .bvar _ => isTrue trivial
  | .abs _ φ => φ.decPresupFree
  | .sigma _ φ => φ.decPresupFree
  | .inter s t => @instDecidableAnd _ _ s.decPresupFree t.decPresupFree
  | .empty => isTrue trivial
  | .presup _ _ => isFalse id
/-- Decidability of `Formula.PresupFree`. -/
def Formula.decPresupFree : (φ : Formula V L P) → Decidable φ.PresupFree
  | .top => isTrue trivial
  | .atom _ w ts =>
      @instDecidableAnd _ _ w.decPresupFree
        (@List.decidableBAll _ _ (fun i => (ts i).decPresupFree) _)
  | .eq s t => @instDecidableAnd _ _ s.decPresupFree t.decPresupFree
  | .subset s t => @instDecidableAnd _ _ s.decPresupFree t.decPresupFree
  | .mem s t => @instDecidableAnd _ _ s.decPresupFree t.decPresupFree
  | .sg t => t.decPresupFree
  | .pl t => t.decPresupFree
  | .neg φ => φ.decPresupFree
  | .conj φ ψ => @instDecidableAnd _ _ φ.decPresupFree ψ.decPresupFree
  | .exists_ _ φ => φ.decPresupFree
  | .presup _ _ => isFalse id
  | .labelDef _ φ => φ.decPresupFree
  | .label _ => isFalse id
end

instance (t : Term V L P) : Decidable t.PresupFree := t.decPresupFree

instance (φ : Formula V L P) : Decidable φ.PresupFree := φ.decPresupFree

/-! ### Semantics -/

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

/-! ### Felicity -/

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

/-! ### Labels -/

section Labels

variable [DecidableEq L]

mutual
/-- Replace every label use by its definition under the assignment `A`, leaving
undefined labels in place. -/
def Term.substLabels (A : L → Option (Formula V L P)) : Term V L P → Term V L P
  | .var x => .var x
  | .bvar x => .bvar x
  | .abs x φ => .abs x (Formula.substLabels A φ)
  | .sigma x φ => .sigma x (Formula.substLabels A φ)
  | .inter s t => .inter (Term.substLabels A s) (Term.substLabels A t)
  | .empty => .empty
  | .presup t χ => .presup (Term.substLabels A t) (Formula.substLabels A χ)
/-- Replace every label use by its definition under the assignment `A`. -/
def Formula.substLabels (A : L → Option (Formula V L P)) : Formula V L P → Formula V L P
  | .top => .top
  | .atom r w ts => .atom r (Term.substLabels A w) fun i => Term.substLabels A (ts i)
  | .eq s t => .eq (Term.substLabels A s) (Term.substLabels A t)
  | .subset s t => .subset (Term.substLabels A s) (Term.substLabels A t)
  | .mem s t => .mem (Term.substLabels A s) (Term.substLabels A t)
  | .sg t => .sg (Term.substLabels A t)
  | .pl t => .pl (Term.substLabels A t)
  | .neg φ => .neg (Formula.substLabels A φ)
  | .conj φ χ => .conj (Formula.substLabels A φ) (Formula.substLabels A χ)
  | .exists_ x φ => .exists_ x (Formula.substLabels A φ)
  | .presup φ χ => .presup (Formula.substLabels A φ) (Formula.substLabels A χ)
  | .labelDef X φ => .labelDef X (Formula.substLabels A φ)
  | .label X => (A X).getD (.label X)
end

mutual
/-- The label definitions occurring in a term. -/
def Term.defs : Term V L P → List (L × Formula V L P)
  | .var _ => []
  | .bvar _ => []
  | .abs _ φ => φ.defs
  | .sigma _ φ => φ.defs
  | .inter s t => s.defs ++ t.defs
  | .empty => []
  | .presup t ψ => t.defs ++ ψ.defs
/-- The label definitions occurring in a formula. -/
def Formula.defs : Formula V L P → List (L × Formula V L P)
  | .top => []
  | .atom _ w ts => w.defs ++ (List.finRange _).flatMap fun i => (ts i).defs
  | .eq s t => s.defs ++ t.defs
  | .subset s t => s.defs ++ t.defs
  | .mem s t => s.defs ++ t.defs
  | .sg t => t.defs
  | .pl t => t.defs
  | .neg φ => φ.defs
  | .conj φ ψ => φ.defs ++ ψ.defs
  | .exists_ _ φ => φ.defs
  | .presup φ ψ => φ.defs ++ ψ.defs
  | .labelDef X φ => (X, φ) :: φ.defs
  | .label _ => []
end

/-- The label assignment determined by a list of definitions: the first
definition of each label. -/
def assignment : List (L × Formula V L P) → L → Option (Formula V L P)
  | [], _ => none
  | (Y, ψ) :: A, X => if Y = X then some ψ else assignment A X

/-- Expand a formula by a list of label definitions: one round of simultaneous
substitution per definition, which resolves every non-circular chain of
definitions whatever their order. -/
def Formula.expand (A : List (L × Formula V L P)) (φ : Formula V L P) : Formula V L P :=
  A.foldl (fun ψ _ => ψ.substLabels (assignment A)) φ

/-- Expand a formula by its own label definitions. -/
def Formula.expandSelf (φ : Formula V L P) : Formula V L P := φ.expand φ.defs

end Labels

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

/-! ### Eliminability -/

/-- Existential closure over a list of variables, as syntax. -/
def Formula.closeList (xs : List V) (φ : Formula V L P) : Formula V L P :=
  xs.foldr Formula.exists_ φ

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
/-- Translation into predicate calculus with set abstraction: brackets and
presuppositions are dropped, summation becomes abstraction over the closure of
the other local variables, label definitions become `⊤`. -/
def Term.elim : Term V L P → Term V L P
  | .var x => .var x
  | .bvar x => .var x
  | .abs x φ => .abs x φ.elim
  | .sigma x φ => .abs x (φ.elim.closeList (φ.locals.filter (· ≠ x)))
  | .inter s t => .inter s.elim t.elim
  | .empty => .empty
  | .presup t _ => t.elim
/-- Translation into predicate calculus with set abstraction. -/
def Formula.elim : Formula V L P → Formula V L P
  | .top => .top
  | .atom r w ts => .atom r w.elim fun i => (ts i).elim
  | .eq s t => .eq s.elim t.elim
  | .subset s t => .subset s.elim t.elim
  | .mem s t => .mem s.elim t.elim
  | .sg t => .sg t.elim
  | .pl t => .pl t.elim
  | .neg φ => .neg φ.elim
  | .conj φ ψ => .conj φ.elim ψ.elim
  | .exists_ x φ => .exists_ x φ.elim
  | .presup φ _ => φ.elim
  | .labelDef _ _ => .top
  | .label X => .label X
end

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

/-! ### Intensional models -/

/-- The atoms of an intensional model: worlds and entities. -/
abbrev Atom (W E : Type*) := W ⊕ E

variable {W E : Type*}

/-- A world as a singleton plurality. -/
def world (w : W) : Set (Atom W E) := {Sum.inl w}

theorem world_inj {w w' : W} : (world w : Set (Atom W E)) = world w' ↔ w = w' :=
  Set.singleton_eq_singleton_iff.trans Sum.inl_injective.eq_iff

/-- The intensional model of a family of relations on atoms at each world: a
relation symbol holds of a world and nonempty pluralities iff it holds at that
world of every tuple of their members, and of nothing whose world argument is
not a world. -/
def Model.intensional (rel : ∀ {n : ℕ}, P n → W → (Fin n → Atom W E) → Prop) :
    Model P (Atom W E) where
  I r Wp ts := ∃ w, Wp = world w ∧ (∀ i, (ts i).Nonempty) ∧
    ∀ as, (∀ i, as i ∈ ts i) → rel r w as

variable {rel : ∀ {n : ℕ}, P n → W → (Fin n → Atom W E) → Prop}

theorem Model.intensional_apply₁ (r : P 1) (Wp X : Set (Atom W E)) :
    (Model.intensional rel).I r Wp ![X] ↔
      ∃ w, Wp = world w ∧ X.Nonempty ∧ ∀ a ∈ X, rel r w ![a] := by
  simp only [Model.intensional, Fin.forall_fin_one, Matrix.cons_val_zero]
  refine exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ => ⟨?_, ?_⟩
  · exact fun H a ha => H ![a] ha
  · intro H as h
    have := H (as 0) h
    rwa [show ![as 0] = as from funext (Fin.forall_fin_one.2 rfl)] at this

theorem Model.intensional_apply₂ (r : P 2) (Wp X Y : Set (Atom W E)) :
    (Model.intensional rel).I r Wp ![X, Y] ↔
      ∃ w, Wp = world w ∧ X.Nonempty ∧ Y.Nonempty ∧
        ∀ a ∈ X, ∀ b ∈ Y, rel r w ![a, b] := by
  simp only [Model.intensional, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    and_assoc]
  refine exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ⟨?_, ?_⟩
  · exact fun H a ha b hb => H ![a, b] ⟨ha, hb⟩
  · intro H as h
    have := H (as 0) h.1 (as 1) h.2
    rwa [show ![as 0, as 1] = as from funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)] at this

/-- A plurality of entities is a singleton iff exactly one entity satisfies its
description. -/
theorem exists_eq_singleton_iff (Q : E → Prop) :
    (∃ a : Atom W E, {x | ∃ e, x = Sum.inr e ∧ Q e} = {a}) ↔ ∃! e, Q e := by
  simp only [Set.eq_singleton_iff_unique_mem, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ⟨e, rfl, he⟩, hu⟩
    exact ⟨e, he, fun e' he' => Sum.inr_injective (hu _ ⟨e', rfl, he'⟩)⟩
  · rintro ⟨e, he, hu⟩
    exact ⟨_, ⟨e, rfl, he⟩, fun x ⟨e', hx, he'⟩ => hx ▸ congrArg Sum.inr (hu e' he')⟩

end PIP
