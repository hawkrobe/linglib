import Linglib.Semantics.Dynamic.CDRT
import Linglib.Semantics.Dynamic.DPL.Syntax
import Mathlib.ModelTheory.Semantics

/-!
# The interpretations of dynamic predicate logic

A formula of `DPL/Syntax.lean` has two interpretations in a structure `M`. The dynamic one,
`Formula.eval`, is [groenendijk-stokhof-1991]'s: a relation between assignments, built from the
update algebra of `Update.lean`, with conjunction as composition, the existential as a random
reset followed by its scope, and everything else a test. The static one, `Formula.static`, is
the usual satisfaction set, built in the cylindric set algebra of assignments, with the
existential as cylindrification. A formula is true at an assignment under the dynamic
interpretation when it has an output there, `(φ.eval M).dom`; the two notions of truth agree on
the scope-bound formulas and differ where a quantifier binds outside its scope.

## Main definitions

* `DPL.Formula.eval`: the dynamic interpretation.
* `DPL.Formula.static`: the static interpretation.

## Main results

* `DPL.Formula.isTest_eval`: a formula with no active quantifier variable is a test.

## Implementation notes

`eval` is stated through the substrate's `dexists` and `dforall`, so that the laws of the update
algebra apply to it as they stand; `mem_dexists` and `mem_dforall` unfold them at assignments.
The converse of `isTest_eval` fails, a test such as `x ≐ y ⋏ ∃[x] (x ≐ y)` having an active
quantifier variable.

## References

* [groenendijk-stokhof-1991]
* [henkin-monk-tarski-1971]
-/

open FirstOrder FirstOrder.Language DynamicSemantics DynamicSemantics.Update SetRel
  CylindricAlgebra

namespace DPL.Formula

universe u v w x

variable {L : Language.{u, v}} {V : Type w} [DecidableEq V] (M : Type x) [L.Structure M]

/-- The dynamic interpretation relates the input assignments to their output assignments. -/
def eval : Formula L V → Update (V → M)
  | top => .id
  | rel R ts => test {g | Structure.RelMap R fun i => (ts i).realize g}
  | equal t₁ t₂ => test {g | t₁.realize g = t₂.realize g}
  | neg φ => test (Update.neg (eval φ))
  | conj φ ψ => eval φ ○ eval ψ
  | disj φ ψ => test (Update.disj (eval φ) (eval ψ))
  | imp φ ψ => test (impl (eval φ) (eval ψ))
  | ex x φ => dexists x (eval φ)
  | all x φ => test (dforall x (eval φ))

/-- The static interpretation is the set of assignments that satisfy the formula in predicate
logic. -/
def static : Formula L V → Set (V → M)
  | top => Set.univ
  | rel R ts => {g | Structure.RelMap R fun i => (ts i).realize g}
  | equal t₁ t₂ => {g | t₁.realize g = t₂.realize g}
  | neg φ => (static φ)ᶜ
  | conj φ ψ => static φ ∩ static ψ
  | disj φ ψ => static φ ∪ static ψ
  | imp φ ψ => (static φ)ᶜ ∪ static ψ
  | ex x φ => cyl x (static φ)
  | all x φ => (cyl x (static φ)ᶜ)ᶜ

variable (φ ψ : Formula L V) (x : V)

open scoped DPL

@[simp] theorem eval_top : (top : Formula L V).eval M = .id := rfl

@[simp] theorem eval_neg : (¬ᵈφ).eval M = test (Update.neg (φ.eval M)) := rfl

@[simp] theorem eval_conj : (φ ⋏ ψ).eval M = φ.eval M ○ ψ.eval M := rfl

@[simp] theorem eval_disj : (φ ⋎ ψ).eval M = test (Update.disj (φ.eval M) (ψ.eval M)) := rfl

@[simp] theorem eval_imp : (φ ⟿ ψ).eval M = test (impl (φ.eval M) (ψ.eval M)) := rfl

@[simp] theorem eval_ex : (∃[x] φ).eval M = dexists x (φ.eval M) := rfl

@[simp] theorem eval_all : (∀[x] φ).eval M = test (dforall x (φ.eval M)) := rfl

@[simp] theorem eval_rel {n : ℕ} (R : L.Relations n) (ts : Fin n → L.Term V) :
    (rel R ts).eval M = test {g | Structure.RelMap R fun i => (ts i).realize g} := rfl

@[simp] theorem eval_equal (t₁ t₂ : L.Term V) :
    (t₁ ≐ t₂).eval M = test {g | t₁.realize g = t₂.realize g} := rfl

variable {φ} in
/-- A formula with no active quantifier variable is a test, since atoms, negations,
disjunctions, implications and universals are and conjunction preserves it. -/
theorem isTest_eval (h : φ.aqv = ∅) : IsTest (φ.eval M) := by
  induction φ with
  | top => exact subset_rfl
  | conj φ ψ ihφ ihψ =>
    rw [aqv_conj, Finset.union_eq_empty] at h
    exact (ihφ h.1).comp (ihψ h.2)
  | ex x φ => exact absurd h (Finset.insert_ne_empty _ _)
  | _ => exact isTest_test _

end DPL.Formula
