module

public import Mathlib.ModelTheory.Semantics

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

@[expose] public section

universe u v

namespace FirstOrder.Language.Formula

open FirstOrder Language

variable {L : Language.{u, v}} {α : Type*} [DecidableEq α]

/-- Universally close the named free variable `n`: relabel it to the bound variable and
quantify. Computable, unlike mathlib's `Formula.iAlls`. -/
def all₁ (n : α) (φ : L.Formula α) : L.Formula α :=
  (BoundedFormula.relabel (Function.update Sum.inl n (Sum.inr (0 : Fin 1))) φ).all

/-- Existentially close the named free variable `n`. Computable, unlike mathlib's
`Formula.iExs`. -/
def ex₁ (n : α) (φ : L.Formula α) : L.Formula α :=
  (BoundedFormula.relabel (Function.update Sum.inl n (Sum.inr (0 : Fin 1))) φ).ex

variable {M : Type*} [L.Structure M]

/-- Relabeling `n` to the bound variable and supplying `x` for it is updating the valuation
at `n`. -/
theorem realize_relabel_update (n : α) (φ : L.Formula α) (v : α → M) (x : M) :
    (BoundedFormula.relabel (Function.update Sum.inl n (Sum.inr (0 : Fin 1))) φ).Realize v
      (Fin.snoc (default : Fin 0 → M) x) ↔ φ.Realize (Function.update v n x) := by
  rw [BoundedFormula.realize_relabel, Function.comp_update]
  refine iff_of_eq (congrArg₂ (BoundedFormula.Realize φ) ?_ (funext fun i ↦ i.elim0))
  simp [Fin.snoc, Function.comp_def]

theorem realize_all₁ {n : α} {φ : L.Formula α} {v : α → M} :
    (all₁ n φ).Realize v ↔ ∀ x : M, φ.Realize (Function.update v n x) :=
  BoundedFormula.realize_all.trans <| forall_congr' <| realize_relabel_update n φ v

theorem realize_ex₁ {n : α} {φ : L.Formula α} {v : α → M} :
    (ex₁ n φ).Realize v ↔ ∃ x : M, φ.Realize (Function.update v n x) :=
  BoundedFormula.realize_ex.trans <| exists_congr <| realize_relabel_update n φ v

/-- A formula with no occurring free variables, as a sentence. -/
def toSentence (φ : L.Formula α) (h : φ.freeVarFinset = ∅) : L.Sentence :=
  φ.restrictFreeVar fun x => absurd x.2 (by simp [h])

theorem realize_toSentence (φ : L.Formula α) (h : φ.freeVarFinset = ∅)
    (v : α → M) :
    (M ⊨ φ.toSentence h) ↔ φ.Realize v :=
  BoundedFormula.realize_restrictFreeVar v (fun a => absurd a.2 (by simp [h]))

end FirstOrder.Language.Formula
