module

public import Linglib.Core.ModelTheory.Binders
public import Linglib.Semantics.Dynamic.DPL.Context

/-!
# Dynamic predicate logic and first-order logic

The formulas of dynamic predicate logic are those of predicate logic, so each translates into a
mathlib first-order formula over the same variables, a quantifier binding its named variable
through `FirstOrder.Language.Formula.ex₁`. The static interpretation of a formula is the
satisfaction of its translation, and so is its dynamic truth when the formula is scope-bound:
there the two logics agree, which is the sense in which [groenendijk-stokhof-1991]'s logic
extends predicate logic.

## Main definitions

* `DPL.Formula.toFormula`: the translation into `L.Formula V`.

## Main results

* `DPL.Formula.mem_static_iff`: static satisfaction is `Formula.Realize` of the translation.
* `DPL.Formula.IsScopeBound.mem_dom_eval_iff`: on a scope-bound formula, dynamic truth is
  `Formula.Realize` of the translation.

## References

* [groenendijk-stokhof-1991]
-/

@[expose] public section

open FirstOrder FirstOrder.Language DynamicSemantics SetRel CylindricAlgebra

namespace DPL.Formula

universe u v w x

variable {L : Language.{u, v}} {V : Type w} [DecidableEq V] {M : Type x} [L.Structure M]

/-- The first-order formula with the same connectives, a quantifier binding its named
variable. -/
def toFormula : DPL.Formula L V → L.Formula V
  | top => ⊤
  | rel R ts => R.formula ts
  | equal t₁ t₂ => t₁.equal t₂
  | neg φ => (toFormula φ).not
  | conj φ ψ => toFormula φ ⊓ toFormula ψ
  | disj φ ψ => toFormula φ ⊔ toFormula ψ
  | imp φ ψ => (toFormula φ).imp (toFormula ψ)
  | ex x φ => (toFormula φ).ex₁ x
  | all x φ => (toFormula φ).all₁ x

/-- The static interpretation is satisfaction of the translation. -/
theorem mem_static_iff (φ : DPL.Formula L V) {g : V → M} :
    g ∈ φ.static M ↔ φ.toFormula.Realize g := by
  induction φ generalizing g with
  | top => simp [static, toFormula]
  | rel R ts => simp [static, toFormula, Formula.realize_rel]
  | equal t₁ t₂ => simp [static, toFormula]
  | neg φ ih => simp [static, toFormula, ih]
  | conj φ ψ ihφ ihψ => simp [static, toFormula, ihφ, ihψ]
  | disj φ ψ ihφ ihψ => simp [static, toFormula, ihφ, ihψ]
  | imp φ ψ ihφ ihψ => simp [static, toFormula, ihφ, ihψ, imp_iff_not_or]
  | ex x φ ih => simp [static, toFormula, Formula.realize_ex₁, ih]
  | all x φ ih => simp [static, toFormula, Formula.realize_all₁, ih]

/-- On a scope-bound formula, dynamic truth is satisfaction of the translation. -/
theorem IsScopeBound.mem_dom_eval_iff {φ : DPL.Formula L V} (h : φ.IsScopeBound) {g : V → M} :
    g ∈ (φ.eval M).dom ↔ φ.toFormula.Realize g := by
  rw [h.dom_eval M, mem_static_iff]

end DPL.Formula
