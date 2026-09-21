module

public import Mathlib.Logic.Function.DependsOn
public import Mathlib.ModelTheory.Semantics

/-!
# Satisfaction: dependence on variables and decidability

This file shows that the value of a term depends only on its variables, and that first-order
satisfaction is decidable on a finite structure with decidable equality and decidable relations,
so that `decide` checks `Realize` facts on concrete finite models.

## Main definitions

- `FirstOrder.Language.Term.dependsOn_realize`: a term's value depends only on its variables.
- `FirstOrder.Language.BoundedFormula.decidableRealize` decides `BoundedFormula.Realize` by
  recursion on the formula.
- `FirstOrder.Language.Formula.decidableRealize` is the same for formulas.
-/

@[expose] public section

namespace FirstOrder.Language

open Structure

/-- [UPSTREAM] The value of a term depends only on the values of its variables. -/
theorem Term.dependsOn_realize {L : Language} {M : Type*} [L.Structure M] {α : Type*}
    [DecidableEq α] (t : L.Term α) : DependsOn (fun v : α → M ↦ t.realize v) t.varFinset := by
  intro v₁ v₂ h
  induction t with
  | var a => exact h a (Finset.mem_coe.2 (Finset.mem_singleton_self a))
  | func f ts ih =>
    refine congrArg _ (funext fun i ↦ ih i fun a ha ↦ h a ?_)
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ha⟩)

section DecidableRealize

variable {L : Language} {M : Type*} [L.Structure M] [Fintype M] [DecidableEq M]
  [∀ (n : ℕ) (r : L.Relations n) (x : Fin n → M), Decidable (RelMap r x)] {α : Type*}

/-- Satisfaction on a finite structure with decidable equality and decidable relations is
decidable, by recursion on the formula; `decide` reduces through it on concrete models. -/
instance BoundedFormula.decidableRealize :
    ∀ {n : ℕ} (φ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M),
      Decidable (φ.Realize v xs)
  | _, .falsum, _, _ => .isFalse id
  | _, .equal _ _, _, _ => inferInstanceAs (Decidable (_ = _))
  | _, .rel R _, _, _ => inferInstanceAs (Decidable (RelMap R _))
  | _, .imp φ ψ, v, xs =>
    haveI := decidableRealize φ v xs
    haveI := decidableRealize ψ v xs
    inferInstanceAs (Decidable (_ → _))
  | _, .all φ, v, xs =>
    haveI : ∀ a, Decidable (φ.Realize v (Fin.snoc xs a)) := fun a =>
      decidableRealize φ v (Fin.snoc xs a)
    inferInstanceAs (Decidable (∀ a, φ.Realize v (Fin.snoc xs a)))

instance Formula.decidableRealize (φ : L.Formula α) (v : α → M) : Decidable (φ.Realize v) :=
  BoundedFormula.decidableRealize φ v default

end DecidableRealize

end FirstOrder.Language
