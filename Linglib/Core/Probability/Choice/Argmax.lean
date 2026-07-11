import Mathlib.Probability.Distributions.Uniform
import Linglib.Core.Order.Argmax

/-!
# Uniform-over-argmax choice rule

`PMF.uniformOfArgmax score` is the PMF uniform over the score-maximal
elements (`Finset.argmax`). It is the hard-choice sibling of `PMF.softmax`
(`Core/Probability/Softmax.lean`): as the inverse temperature inside a
softmax score grows without bound, softmax mass concentrates on the argmax
set (`Core/Probability/SoftmaxLimits.lean` proves the ℝ-level limit).
Iterated-best-response models ([franke-2011]) use this rule where RSA
([frank-goodman-2012]) uses softmax.

## Main definitions

* `PMF.uniformOfArgmax score` — uniform PMF over `Finset.univ.argmax score`.

## Main statements

* `support_uniformOfArgmax` — the support is the argmax set.
* `uniformOfArgmax_apply_pos_iff` — positive mass iff score-maximal.
* `uniformOfArgmax_comp_strictMono` — invariance under strictly monotone
  rescaling of the score (inverse-temperature invariance).
-/

set_option autoImplicit false

open scoped ENNReal

namespace PMF

variable {α β γ : Type*} [Fintype α] [Nonempty α] [LinearOrder β] [LinearOrder γ]

/-! ## Definition -/

/-- The **argmax choice rule**: uniform distribution over the score-maximal
elements. Hard-choice counterpart of `PMF.softmax`; the selection rule of
iterated-best-response models ([franke-2011]). -/
noncomputable def uniformOfArgmax (score : α → β) : PMF α :=
  uniformOfFinset (Finset.univ.argmax score)
    (Finset.argmax_nonempty Finset.univ_nonempty)

/-! ## API -/

/-- The support of the argmax choice rule is the argmax set. -/
@[simp]
theorem support_uniformOfArgmax (score : α → β) :
    (uniformOfArgmax score).support = ↑(Finset.univ.argmax score) :=
  support_uniformOfFinset _

/-- The argmax choice rule assigns positive mass exactly to the
score-maximal elements. -/
theorem uniformOfArgmax_apply_pos_iff (score : α → β) (a : α) :
    0 < uniformOfArgmax score a ↔ ∀ b, score b ≤ score a := by
  rw [pos_iff_ne_zero, ← mem_support_iff, support_uniformOfArgmax]
  simp

/-- Mass of a score-maximal element: one over the size of the argmax set. -/
theorem uniformOfArgmax_apply_of_max (score : α → β) (a : α)
    (ha : ∀ b, score b ≤ score a) :
    uniformOfArgmax score a = ((Finset.univ.argmax score).card : ℝ≥0∞)⁻¹ :=
  uniformOfFinset_apply_of_mem _
    (Finset.mem_argmax.mpr ⟨Finset.mem_univ a, fun b _ => ha b⟩)

/-- Non-maximal elements get zero mass. -/
theorem uniformOfArgmax_apply_of_not_max (score : α → β) (a : α)
    (ha : ¬ ∀ b, score b ≤ score a) :
    uniformOfArgmax score a = 0 :=
  uniformOfFinset_apply_of_notMem _ (by simpa using ha)

/-- The argmax choice rule is invariant under strictly monotone rescaling of
the score: changing the inverse temperature does not move the hard choice. -/
theorem uniformOfArgmax_comp_strictMono (score : α → β) {g : β → γ}
    (hg : StrictMono g) :
    uniformOfArgmax (g ∘ score) = uniformOfArgmax score := by
  simp only [uniformOfArgmax]
  congr 1
  exact Finset.argmax_comp_strictMono hg

/-- A constant score yields the uniform distribution. -/
theorem uniformOfArgmax_const (c : β) :
    uniformOfArgmax (fun _ : α => c) = uniformOfFintype α := by
  simp only [uniformOfArgmax, uniformOfFintype]
  congr 1
  simp

end PMF
