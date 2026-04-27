import Linglib.Theories.Pragmatics.RSA.Operators
import Linglib.Phenomena.Clarification.Studies.DongEtAl2026
import Mathlib.Probability.Distributions.Uniform

/-!
# @cite{dong-etal-2026} on mathlib `PMF` (binary identification)
@cite{dong-etal-2026}

PMF-shaped re-formalisation of `DongEtAl2026.lean`'s 4 findings on binary
identification. The task is intentionally degenerate: at any target,
exactly one utterance applies (matching pair).

All 4 findings are vacuous-zero: the wrong guess has L0 = 0, so its S1/L1
mass is 0, hence "correct > wrong".

Stakes parameter `k` (animal: 1, medical: 10) is irrelevant to the
qualitative predictions because the L0 gate zeros incorrect responses.
The PMF migration uses `S1Belief` with cost factor `exp(α·k)` for matching
pairs (matching mathlib's `Real.exp` via `ENNReal.ofReal`), but the
qualitative claims hold regardless.

For the simplest PMF formulation, we set α = 1 and use a unit cost factor
(no stakes-dependence). Both bundled-API configs (`animalCfg`, `medicalCfg`)
collapse to the same PMF model after qualitative-only migration.

## Reused from `DongEtAl2026.lean`

* `Target`, `targetMatches` — domain + Boolean meaning
-/

set_option autoImplicit false

namespace DongEtAl2026.PMF

open scoped ENNReal

instance : Nonempty Target := ⟨.t₁⟩

/-! ## §1. L0 — uniform on extension via `RSA.L0OfBoolMeaning` -/

abbrev extension (u : Target) : Finset Target :=
  RSA.extensionOf targetMatches u

theorem extension_nonempty (u : Target) : (extension u).Nonempty := by
  cases u
  · exact ⟨.t₁, RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨.t₂, RSA.mem_extensionOf.mpr (by decide)⟩

noncomputable def L0 (u : Target) : PMF Target :=
  RSA.L0OfBoolMeaning targetMatches u (extension_nonempty u)

@[simp] theorem mem_support_L0_iff (u : Target) (w : Target) :
    w ∈ (L0 u).support ↔ targetMatches u w = true :=
  RSA.mem_support_L0OfBoolMeaning_iff _ _

theorem L0_apply_of_true {u : Target} {w : Target} (h : targetMatches u w = true) :
    L0 u w = ((extension u).card : ℝ≥0∞)⁻¹ :=
  RSA.L0OfBoolMeaning_apply_of_mem _ h

theorem L0_apply_of_false {u : Target} {w : Target} (h : targetMatches u w ≠ true) :
    L0 u w = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ h

private theorem L0_apply_ne_zero {u : Target} {w : Target} (h : targetMatches u w = true) :
    L0 u w ≠ 0 := by
  rw [← PMF.mem_support_iff, mem_support_L0_iff]; exact h

/-! ## §2. S1 — speaker as `PMF.normalize` of L0 -/

theorem L0_tsum_utterance_ne_top (w : Target) : ∑' u, (L0 u w : ℝ≥0∞) ≠ ∞ :=
  PMF.tsum_apply_ne_top (fun u => L0 u) w

private theorem tsum_L0_ne_zero_at {u : Target} {w : Target} (h : targetMatches u w = true) :
    (∑' u', (L0 u' w : ℝ≥0∞)) ≠ 0 :=
  PMF.tsum_apply_ne_zero L0 (a := u) (L0_apply_ne_zero h)

/-- Pragmatic speaker: each world has at least one matching utterance,
so no fallback is needed (every world is non-degenerate in the binary task). -/
noncomputable def S1 (w : Target) : PMF Target :=
  PMF.normalize (fun u => L0 u w)
    (tsum_L0_ne_zero_at (u := w) (by cases w <;> decide))
    (L0_tsum_utterance_ne_top w)

theorem S1_apply (w : Target) (u : Target) :
    S1 w u = L0 u w * (∑' u', L0 u' w)⁻¹ :=
  PMF.normalize_apply _ _ _

/-! ## §3. L1 — Bayesian inversion against the uniform world prior -/

noncomputable def worldPrior : PMF Target := PMF.uniformOfFintype Target

theorem worldPrior_ne_zero (w : Target) : worldPrior w ≠ 0 :=
  (worldPrior.mem_support_iff w).mp (PMF.mem_support_uniformOfFintype w)

private theorem S1_ne_zero_at {u : Target} {w : Target} (h : targetMatches u w = true) :
    S1 w u ≠ 0 := by
  rw [S1, ← PMF.mem_support_iff, PMF.mem_support_normalize_iff]
  exact L0_apply_ne_zero h

theorem L1_marginal_ne_zero (u : Target) :
    PMF.marginal S1 worldPrior u ≠ 0 := by
  cases u
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero .t₁) (S1_ne_zero_at (by decide))
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero .t₂) (S1_ne_zero_at (by decide))

noncomputable def L1 (u : Target) : PMF Target :=
  PMF.posterior S1 worldPrior u (L1_marginal_ne_zero u)

/-! ## §4. Findings — all vacuous-zero -/

/-- S1 prefers correct guess: at world .t₁, utterance .t₂ has L0 = 0
(targetMatches .t₂ .t₁ = false), so S1 .t₁ .t₂ = 0.

Same-base comparison (same world .t₁), different utterances → use
`normalize_lt_iff_lt` to reduce to L0 score comparison. -/
theorem S1_prefers_correct : S1 .t₁ .t₂ < S1 .t₁ .t₁ := by
  rw [S1, PMF.normalize_lt_iff_lt]
  rw [L0_apply_of_false (by decide : targetMatches .t₂ .t₁ ≠ true)]
  exact pos_iff_ne_zero.mpr (L0_apply_ne_zero (by decide))

/-- S1 facing target .t₁ prefers utterance .t₁ over .t₂. -/
theorem S1_animal_prefers_correct : S1 .t₁ .t₁ > S1 .t₁ .t₂ :=
  S1_prefers_correct

/-- Same prediction at "medical" stakes (the binary task is degenerate;
qualitative prediction unchanged by the stakes parameter). -/
theorem S1_medical_prefers_correct : S1 .t₁ .t₁ > S1 .t₁ .t₂ :=
  S1_prefers_correct

/-- Per-world S1 leaf for L1: at world .t₂, utterance .t₁ doesn't apply,
so S1 .t₂ .t₁ = 0. At world .t₁, S1 .t₁ .t₁ > 0. -/
theorem S1_t2_lt_S1_t1_for_t1 : S1 .t₂ .t₁ < S1 .t₁ .t₁ := by
  exact PMF.normalize_lt_of_apply_zero_pos _ _ _ _ _ _ _
    (L0_apply_of_false (by decide : targetMatches .t₁ .t₂ ≠ true))
    (L0_apply_ne_zero (by decide : targetMatches .t₁ .t₁ = true))

/-- L1 correctly identifies target from utterance. -/
theorem L1_animal_identifies : L1 .t₁ .t₁ > L1 .t₁ .t₂ := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_t2_lt_S1_t1_for_t1

/-- Same prediction at "medical" stakes. -/
theorem L1_medical_identifies : L1 .t₁ .t₁ > L1 .t₁ .t₂ :=
  L1_animal_identifies

end DongEtAl2026.PMF
