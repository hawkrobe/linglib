import Mathlib.ModelTheory.Semantics

/-!
# Decidable satisfaction on finite structures

This file shows that first-order satisfaction is decidable on a finite structure with decidable
equality and decidable relations, so that `decide` checks `Realize` facts on concrete finite
models.

## Main definitions

- `FirstOrder.Language.BoundedFormula.decidableRealize` decides `BoundedFormula.Realize` by
  recursion on the formula.
- `FirstOrder.Language.Formula.decidableRealize` is the same for formulas.
-/

namespace FirstOrder.Language

open Structure

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
