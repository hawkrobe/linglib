import Mathlib.ModelTheory.Complexity

/-!
# Quantifier rank of first-order formulas

`[UPSTREAM]` candidate. mathlib's `ModelTheory` has formula *complexity classes*
(`IsQF`, `IsPrenex`, `IsUniversal`) but no quantifier-*rank* function. `qr φ` is the
maximal nesting depth of quantifiers in `φ` — the standard measure indexing
Ehrenfeucht–Fraïssé games and `≡ₙ` n-equivalence, the foundation of every
first-order inexpressibility result (e.g. `Studies.BarwiseCooper1981`'s
`most ∉ FO`, whose ad-hoc `numQuant` this generalizes).

mathlib has the `∞`-rank apparatus (`ElementarilyEquivalent`, the unbounded
back-and-forth `IsExtensionPair`); `qr` is the bottom of the missing finite-rank
layer.

## Main definitions

* `FirstOrder.Language.BoundedFormula.qr` — quantifier rank (max quantifier nesting).
-/

namespace FirstOrder.Language.BoundedFormula

variable {L : Language} {α : Type*} {n : ℕ}

/-- Quantifier rank: the maximal nesting depth of quantifiers in a formula.
Atomic formulas have rank `0`, `imp` takes the max, and `all` adds one. -/
def qr : ∀ {n : ℕ}, L.BoundedFormula α n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp f₁ f₂ => max (qr f₁) (qr f₂)
  | _, .all f => qr f + 1

@[simp] theorem qr_falsum : (falsum : L.BoundedFormula α n).qr = 0 := rfl

@[simp] theorem qr_bot : (⊥ : L.BoundedFormula α n).qr = 0 := rfl

@[simp] theorem qr_equal (t₁ t₂ : L.Term (α ⊕ (Fin n))) :
    (equal t₁ t₂ : L.BoundedFormula α n).qr = 0 := rfl

@[simp] theorem qr_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) :
    (rel R ts).qr = 0 := rfl

@[simp] theorem qr_imp (φ ψ : L.BoundedFormula α n) : (φ.imp ψ).qr = max φ.qr ψ.qr := rfl

@[simp] theorem qr_all (φ : L.BoundedFormula α (n + 1)) : φ.all.qr = φ.qr + 1 := rfl

@[simp] theorem qr_not (φ : L.BoundedFormula α n) : φ.not.qr = φ.qr := by
  simp [BoundedFormula.not]

@[simp] theorem qr_top : (⊤ : L.BoundedFormula α n).qr = 0 := by
  simp [Top.top]

@[simp] theorem qr_inf (φ ψ : L.BoundedFormula α n) : (φ ⊓ ψ).qr = max φ.qr ψ.qr := by
  change ((φ.imp ψ.not).not).qr = _; simp

@[simp] theorem qr_sup (φ ψ : L.BoundedFormula α n) : (φ ⊔ ψ).qr = max φ.qr ψ.qr := by
  change (φ.not.imp ψ).qr = _; simp

@[simp] theorem qr_iff (φ ψ : L.BoundedFormula α n) : (φ.iff ψ).qr = max φ.qr ψ.qr := by
  simp only [BoundedFormula.iff, qr_inf, qr_imp, max_comm ψ.qr φ.qr, max_self]

@[simp] theorem qr_ex (φ : L.BoundedFormula α (n + 1)) : φ.ex.qr = φ.qr + 1 := by
  simp [BoundedFormula.ex]

/-- An atomic formula has quantifier rank `0`. -/
theorem IsAtomic.qr_eq_zero {φ : L.BoundedFormula α n} (h : φ.IsAtomic) : φ.qr = 0 := by
  cases h <;> rfl

/-- A quantifier-free formula has quantifier rank `0`. -/
theorem IsQF.qr_eq_zero {φ : L.BoundedFormula α n} (h : φ.IsQF) : φ.qr = 0 := by
  induction h with
  | falsum => rfl
  | of_isAtomic h => exact h.qr_eq_zero
  | imp _ _ ih₁ ih₂ => simp [ih₁, ih₂]

end FirstOrder.Language.BoundedFormula
