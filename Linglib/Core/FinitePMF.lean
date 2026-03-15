import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite Probability Mass Functions

`FinitePMF W` bundles a rational-valued mass function with non-negativity and
normalization proofs, eliminating the need to thread `hNN`/`hNorm` hypotheses
through probabilistic theorems.

## Relationship to Other Distribution Types

| Type | Number system | Normalized? | Usage |
|------|--------------|-------------|-------|
| `FinitePMF W` | ℚ | Yes (bundled) | Probabilistic answerhood, questions, Bayesian semantics |
| `RSAConfigData` | ℚ | No | RSA unnormalized weights |
| `RSAConfig` | ℝ | No | RSA mathematical proofs |
| `W → ℝ` | ℝ | Hypothesized | Entropy / information theory |

`FinitePMF` is the canonical type for probabilistic semantics where exact
normalized distributions are needed. RSA priors are deliberately unnormalized
and should NOT use `FinitePMF`.
-/

set_option autoImplicit false

namespace Core

/-- A normalized, non-negative probability distribution over a finite type,
using exact rational arithmetic. -/
structure FinitePMF (W : Type*) [Fintype W] where
  /-- Probability mass function -/
  mass : W → ℚ
  /-- All masses are non-negative -/
  mass_nonneg : ∀ w, 0 ≤ mass w
  /-- Masses sum to 1 -/
  mass_sum_one : ∑ w : W, mass w = 1

namespace FinitePMF

variable {W : Type*} [Fintype W]

instance : CoeFun (FinitePMF W) (fun _ => W → ℚ) where
  coe d := d.mass

/-- Coercion to bare function type, for passing to modules that take `W → ℚ`
(e.g., DTS's `condProb`, `bayesFactor`). -/
instance : Coe (FinitePMF W) (W → ℚ) where
  coe d := d.mass

@[simp] lemma coe_def (d : FinitePMF W) (w : W) : d w = d.mass w := rfl

/-- Uniform distribution over a nonempty finite type. -/
def uniform [Nonempty W] : FinitePMF W where
  mass := fun _ => 1 / (Fintype.card W : ℚ)
  mass_nonneg := fun _ => by
    have hn : (0 : ℚ) < (Fintype.card W : ℚ) := by exact_mod_cast Fintype.card_pos
    linarith [div_pos (show (0:ℚ) < 1 from by norm_num) hn]
  mass_sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
    have h : (Fintype.card W : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
    exact div_self h

variable [DecidableEq W]

/-- Point mass at a single value -/
def pure (w₀ : W) : FinitePMF W where
  mass := λ w => if w = w₀ then 1 else 0
  mass_nonneg := λ w => by split_ifs <;> decide
  mass_sum_one := by
    rw [Finset.sum_eq_single w₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact (h (Finset.mem_univ _)).elim

/-- Expected value of a function under this distribution -/
def expect (pmf : FinitePMF W) (f : W → ℚ) : ℚ :=
  Finset.sum Finset.univ λ w => pmf.mass w * f w

/-- Expected value of an indicator (probability of event) -/
def prob (pmf : FinitePMF W) (event : W → Bool) : ℚ :=
  pmf.expect λ w => if event w then 1 else 0

/-- Expected value of pure distribution is the value at that point -/
theorem expect_pure (w₀ : W) (f : W → ℚ) :
    (pure w₀).expect f = f w₀ := by
  simp only [expect, pure]
  rw [Finset.sum_eq_single w₀]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact (h (Finset.mem_univ _)).elim

end FinitePMF

end Core
