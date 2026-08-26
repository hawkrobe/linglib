import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.FinRange

/-!
# PIP — Plural Intensional Presuppositional predicate calculus: syntax

PIP is first-order predicate calculus with set abstraction, equality and the
set-theoretic relations `⊆`, `∈`, `∩`, `∅` and the cardinality predicates `SG`,
`PL`, whose domain consists of pluralities (sets of atoms, worlds among them),
supplemented by five eliminable constructs: bracketed *local* variables `[x]`
slated for unselective closure, summation `Σxφ`, formula labels `X ≡ φ` and
their uses `X`, world arguments on predicates, and presuppositions `φ|ψ`.
Relation symbols are indexed by arity and take a world as a distinguished
argument; summation and abstraction bind by name.

This file defines the syntax: terms and formulas, the defined connectives, the
local variables of an expression, substitution, presupposition-free
expressions, formula labels and their expansion, and the translation
eliminating the PIP constructs. Truth is `Semantics.lean`, felicity
`Felicity.lean`.

## Main definitions

* `Term`, `Formula` — the mutual syntax; `Formula.disj`, `Formula.impl`,
  `Formula.iff_`, `Formula.forall_`, `Formula.some_` — the defined
  connectives; `Term.sgPronoun` — a singular summation pronoun.
* `Term.locals`, `Formula.locals` — the local variables; `Term.subst`,
  `Formula.subst` — substitution for a variable.
* `Term.PresupFree`, `Formula.PresupFree` — expressions without
  presuppositions, decidably.
* `Formula.substLabels`, `Formula.defs`, `assignment`, `Formula.expand`,
  `Formula.expandSelf` — label assignment and expansion, as a bounded fixpoint
  of simultaneous substitution.
* `Formula.closeList`, `Term.elim`, `Formula.elim` — the translation into
  predicate calculus with set abstraction.

## References

* [keshet-abney-2024]
* [abney-keshet-2025]
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

/-- `Σxφ | SG(Σxφ)`: a singular summation pronoun over the description `φ`. -/
def Term.sgPronoun (x : V) (φ : Formula V L P) : Term V L P :=
  .presup (.sigma x φ) (.sg (.sigma x φ))

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

/-! ### Eliminability -/

section Elim

variable [DecidableEq V]

/-- Existential closure over a list of variables, as syntax. -/
def Formula.closeList (xs : List V) (φ : Formula V L P) : Formula V L P :=
  xs.foldr Formula.exists_ φ

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

end Elim

end PIP
