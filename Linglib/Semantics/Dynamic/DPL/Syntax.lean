module

public import Mathlib.ModelTheory.Syntax

/-!
# The syntax of dynamic predicate logic

The formulas of [groenendijk-stokhof-1991]'s dynamic predicate logic over a first-order language
`L` and a type `V` of variables. The syntax is that of ordinary predicate logic with named
variables; what is dynamic is its interpretation (`DPL/Semantics.lean`), under which an
existential quantifier binds occurrences of its variable outside its syntactic scope. The
binding theory of the paper is therefore not the usual one: a formula has a set of free
variables and a set of *active quantifier variables*, those whose existential quantifier can
still bind to the right, and a quantifier's binding exceeds its scope exactly where an active
quantifier variable of a left conjunct or an antecedent is free in what follows.

## Main definitions

* `DPL.Formula L V`: the formulas, with scoped notation `¬ᵈ`, `⋏`, `⋎`, `⟿`, `∃[x]`, `∀[x]`, `≐`;
  `DPL.Formula.exs` and `DPL.Formula.conjs` close over a list of variables and conjoin a list.
* `DPL.Formula.aqv`: the active quantifier variables.
* `DPL.Formula.fv`: the free variables.
* `DPL.Formula.IsScopeBound`: every variable a quantifier binds is in its scope.

## Implementation notes

Mathlib's `FirstOrder.Language.BoundedFormula` binds de Bruijn indices and so identifies
alphabetic variants by construction. Dynamic binding links a quantifier to a named occurrence
outside its scope, which that syntax cannot express, and alphabetic variants are not equivalent
under the dynamic interpretation; hence the named-variable syntax here.

All the connectives and both quantifiers of the paper's syntax are primitive, as in the paper,
so that their interdefinability is a theorem about the interpretation: conjunction and the
existential are not definable from the rest. `top` is the one addition, [visser-1998]'s `⊤`: the
translation of an empty discourse representation structure and the scope of a bare reset need
it, and `x ≐ x` is no substitute, since it reads `x`. Terms are mathlib's, so function symbols
come along; the paper has variables and constants only.

The paper defines binding pairs, active quantifier occurrences, free occurrences and scope
pairs as sets of occurrences, and passes to sets of variables for every fact that uses them;
`aqv` and `fv` are those sets of variables. The paper gives the identity statement no clause;
it is treated as an atom. `IsScopeBound` renders the paper's condition that the binding pairs
are the scope pairs: the two differ exactly by the pairs the clauses for conjunction and
implication add, an active quantifier of the left part with a free occurrence in the right.
`fv` is a syntactic notion and overapproximates the variables the interpretation depends on,
as `x ≐ x` shows.

## References

* [groenendijk-stokhof-1991]
* [visser-1998]
-/

@[expose] public section

open FirstOrder

namespace DPL

universe u v w

/-- The formulas of dynamic predicate logic over the language `L` with variables `V`. -/
inductive Formula (L : Language.{u, v}) (V : Type w) : Type (max u v w)
  /-- The formula that is always true and changes nothing. -/
  | top : Formula L V
  /-- A relation symbol applied to terms. -/
  | rel {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term V) : Formula L V
  /-- An identity statement. -/
  | equal (t₁ t₂ : L.Term V) : Formula L V
  /-- Negation. -/
  | neg (φ : Formula L V) : Formula L V
  /-- Conjunction. -/
  | conj (φ ψ : Formula L V) : Formula L V
  /-- Disjunction. -/
  | disj (φ ψ : Formula L V) : Formula L V
  /-- Implication. -/
  | imp (φ ψ : Formula L V) : Formula L V
  /-- Existential quantification. -/
  | ex (x : V) (φ : Formula L V) : Formula L V
  /-- Universal quantification. -/
  | all (x : V) (φ : Formula L V) : Formula L V

@[inherit_doc] scoped prefix:max "¬ᵈ" => Formula.neg
@[inherit_doc] scoped infixr:69 " ⋏ " => Formula.conj
@[inherit_doc] scoped infixr:68 " ⋎ " => Formula.disj
@[inherit_doc] scoped infixr:62 " ⟿ " => Formula.imp
@[inherit_doc] scoped notation:max "∃[" x "] " φ:max => Formula.ex x φ
@[inherit_doc] scoped notation:max "∀[" x "] " φ:max => Formula.all x φ
@[inherit_doc] scoped infix:88 " ≐ " => Formula.equal

namespace Formula

variable {L : Language.{u, v}} {V : Type w}

/-- The existential closure of a formula over a list of variables. -/
def exs (xs : List V) (φ : Formula L V) : Formula L V := xs.foldr ex φ

/-- The conjunction of a list of formulas, `top` for the empty list. -/
def conjs (φs : List (Formula L V)) : Formula L V := φs.foldr conj top

@[simp] theorem exs_nil (φ : Formula L V) : exs [] φ = φ := rfl

@[simp] theorem exs_cons (x : V) (xs : List V) (φ : Formula L V) :
    exs (x :: xs) φ = ∃[x] (exs xs φ) := rfl

@[simp] theorem conjs_nil : conjs ([] : List (Formula L V)) = top := rfl

@[simp] theorem conjs_cons (φ : Formula L V) (φs : List (Formula L V)) :
    conjs (φ :: φs) = φ ⋏ conjs φs := rfl

variable [DecidableEq V]

/-- The active quantifier variables are those `x` with an occurrence of `∃x` that can still
bind to the right. Only an existential contributes one, and only conjunction passes them on. -/
def aqv : Formula L V → Finset V
  | conj φ ψ => aqv φ ∪ aqv ψ
  | ex x φ => insert x (aqv φ)
  | _ => ∅

/-- The free variables. In a conjunction or an implication the active quantifier variables of
the left part bind into the right part. -/
def fv : Formula L V → Finset V
  | top => ∅
  | rel _ ts => Finset.univ.biUnion fun i => (ts i).varFinset
  | equal t₁ t₂ => t₁.varFinset ∪ t₂.varFinset
  | neg φ => fv φ
  | conj φ ψ | imp φ ψ => fv φ ∪ (fv ψ \ aqv φ)
  | disj φ ψ => fv φ ∪ fv ψ
  | ex x φ | all x φ => (fv φ).erase x

/-- A formula is scope-bound when no active quantifier variable of a left conjunct or an
antecedent is free in what follows, so that every variable a quantifier binds is in its
scope. -/
def IsScopeBound : Formula L V → Prop
  | conj φ ψ | imp φ ψ => IsScopeBound φ ∧ IsScopeBound ψ ∧ Disjoint (aqv φ) (fv ψ)
  | disj φ ψ => IsScopeBound φ ∧ IsScopeBound ψ
  | neg φ | ex _ φ | all _ φ => IsScopeBound φ
  | _ => True

instance decidableIsScopeBound : (φ : Formula L V) → Decidable φ.IsScopeBound
  | top | rel .. | equal .. => isTrue trivial
  | neg φ | ex _ φ | all _ φ => decidableIsScopeBound φ
  | conj φ ψ | imp φ ψ =>
    haveI := decidableIsScopeBound φ; haveI := decidableIsScopeBound ψ
    inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | disj φ ψ =>
    haveI := decidableIsScopeBound φ; haveI := decidableIsScopeBound ψ
    inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem aqv_conj (φ ψ : Formula L V) : (φ ⋏ ψ).aqv = φ.aqv ∪ ψ.aqv := rfl

@[simp] theorem aqv_ex (x : V) (φ : Formula L V) : (∃[x] φ).aqv = insert x φ.aqv := rfl

@[simp] theorem fv_conj (φ ψ : Formula L V) : (φ ⋏ ψ).fv = φ.fv ∪ (ψ.fv \ φ.aqv) := rfl

@[simp] theorem fv_imp (φ ψ : Formula L V) : (φ ⟿ ψ).fv = φ.fv ∪ (ψ.fv \ φ.aqv) := rfl

@[simp] theorem fv_ex (x : V) (φ : Formula L V) : (∃[x] φ).fv = φ.fv.erase x := rfl

@[simp] theorem fv_all (x : V) (φ : Formula L V) : (∀[x] φ).fv = φ.fv.erase x := rfl

theorem isScopeBound_conj {φ ψ : Formula L V} :
    (φ ⋏ ψ).IsScopeBound ↔ φ.IsScopeBound ∧ ψ.IsScopeBound ∧ Disjoint φ.aqv ψ.fv := Iff.rfl

theorem isScopeBound_imp {φ ψ : Formula L V} :
    (φ ⟿ ψ).IsScopeBound ↔ φ.IsScopeBound ∧ ψ.IsScopeBound ∧ Disjoint φ.aqv ψ.fv := Iff.rfl

end Formula

end DPL
