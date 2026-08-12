import Mathlib.ModelTheory.Semantics

/-!
# Computable named-variable binders for first-order formulas

Mathlib quantification on `BoundedFormula` is de Bruijn; formalizations whose
formulas carry named free variables (trace indices in
`Semantics/Composition/Reduction.lean`, QBSML variables in
`Logic/Team/QBSML/Properties.lean`) need to close a *single named*
variable. `Formula.all₁` / `Formula.ex₁` do so computably (unlike mathlib's
`Formula.iAlls` / `iExs`), with realization phrased via `Function.update`.
Upstream candidates.

## Main declarations

* `FirstOrder.Language.Formula.all₁` / `ex₁` — close the named free variable
  `n` universally / existentially.
* `realize_all₁` / `realize_ex₁` — realization via `Function.update`.
* `toSentence` / `realize_toSentence` — a formula with no occurring free
  variables, as a sentence.
-/

universe u v

namespace FirstOrder.Language.Formula

open FirstOrder Language

variable {L : Language.{u, v}} {α : Type*} [DecidableEq α]

/-- The relabeling sending the named free variable `n` to the bound side. -/
private def toBound (n : α) : α → α ⊕ Fin 1 := fun k =>
  if k = n then Sum.inr 0 else Sum.inl k

/-- Universally close the named free variable `n`. Computable, unlike
mathlib's `Formula.iAlls`. -/
def all₁ (n : α) (φ : L.Formula α) : L.Formula α :=
  (BoundedFormula.relabel (toBound n) φ).all

/-- Existentially close the named free variable `n`. Computable, unlike
mathlib's `Formula.iExs`. -/
def ex₁ (n : α) (φ : L.Formula α) : L.Formula α :=
  (BoundedFormula.relabel (toBound n) φ).ex

variable {M : Type*} [L.Structure M]

private theorem realize_relabel_update (n : α) (φ : L.Formula α) (v : α → M)
    (x : M) :
    (BoundedFormula.relabel (toBound n) φ).Realize v
      (Fin.snoc (default : Fin 0 → M) x) ↔
      φ.Realize (Function.update v n x) := by
  rw [BoundedFormula.realize_relabel]
  refine iff_of_eq (congrArg₂ (BoundedFormula.Realize φ) ?_ ?_)
  · funext k
    by_cases hk : k = n <;> simp [hk, toBound, Fin.snoc]
  · funext i
    exact i.elim0

theorem realize_all₁ {n : α} {φ : L.Formula α} {v : α → M} :
    (all₁ n φ).Realize v ↔ ∀ x : M, φ.Realize (Function.update v n x) := by
  have h : (all₁ n φ).Realize v
      = BoundedFormula.Realize (BoundedFormula.relabel (toBound n) φ).all v
          default := rfl
  rw [h, BoundedFormula.realize_all]
  exact forall_congr' fun x => realize_relabel_update n φ v x

theorem realize_ex₁ {n : α} {φ : L.Formula α} {v : α → M} :
    (ex₁ n φ).Realize v ↔ ∃ x : M, φ.Realize (Function.update v n x) := by
  have h : (ex₁ n φ).Realize v
      = BoundedFormula.Realize (BoundedFormula.relabel (toBound n) φ).ex v
          default := rfl
  rw [h, BoundedFormula.realize_ex]
  exact exists_congr fun x => realize_relabel_update n φ v x

/-- A formula with no occurring free variables, as a sentence. -/
def toSentence (φ : L.Formula α) (h : φ.freeVarFinset = ∅) : L.Sentence :=
  φ.restrictFreeVar fun x => absurd x.2 (by simp [h])

theorem realize_toSentence (φ : L.Formula α) (h : φ.freeVarFinset = ∅)
    (v : α → M) :
    (M ⊨ φ.toSentence h) ↔ φ.Realize v :=
  BoundedFormula.realize_restrictFreeVar v (fun a => absurd a.2 (by simp [h]))

end FirstOrder.Language.Formula
