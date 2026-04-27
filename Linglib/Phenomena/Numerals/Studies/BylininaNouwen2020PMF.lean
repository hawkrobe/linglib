import Linglib.Theories.Pragmatics.RSA.Operators
import Linglib.Phenomena.Numerals.Studies.BylininaNouwen2020
import Mathlib.Probability.Distributions.Uniform

/-!
# @cite{bylinina-nouwen-2020} on mathlib `PMF` (Shape A migration pilot)
@cite{bylinina-nouwen-2020}

PMF-shaped re-formalisation of `BylininaNouwen2020.lean`'s 3 findings:
- `lb_rsa_strengthens_two`: L1("two") prefers `c2` over `c3`
- `lb_rsa_strengthens_one`: L1("one") prefers `c1` over `c2`
- `lb_three_peaked`: L1("three") prefers `c3` over `c2`

All three are Shape A (uniform world prior, `Latent := Unit`, no cost factor,
α = 1 → S1 is just normalize of L0).

## Friction surface: degenerate world `.c0`

At `.c0`, NO utterance applies (`one` requires ≥1, etc.). So the speaker
score at `.c0` is identically zero — `PMF.normalize` is undefined.

We use the conditional fallback pattern (same as `Nouwen2024PMF`'s
`adjSpeaker_warmAt`): at degenerate worlds, S1 falls back to a vacuous
`PMF.pure .one`. Doesn't affect the L1 findings (which compare
non-degenerate worlds), but the bundled API silently uses a similar
guard via `if l0 = 0 then 0` in `s1Score`.

## Reused from `BylininaNouwen2020.lean`

* `NCard`, `NUtt`, `lbNuttMeaning` — domain + Boolean meaning matrix
-/

set_option autoImplicit false

namespace BylininaNouwen2020.PMF

open scoped ENNReal

/-! ## §1. L0 — uniform on extension via `RSA.L0OfBoolMeaning` -/

abbrev extension (u : NUtt) : Finset NCard :=
  RSA.extensionOf lbNuttMeaning u

theorem extension_nonempty (u : NUtt) : (extension u).Nonempty := by
  cases u
  · exact ⟨.c1, RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨.c2, RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨.c3, RSA.mem_extensionOf.mpr (by decide)⟩

noncomputable def L0 (u : NUtt) : PMF NCard :=
  RSA.L0OfBoolMeaning lbNuttMeaning u (extension_nonempty u)

@[simp] theorem mem_support_L0_iff (u : NUtt) (w : NCard) :
    w ∈ (L0 u).support ↔ lbNuttMeaning u w = true :=
  RSA.mem_support_L0OfBoolMeaning_iff _ _

theorem L0_apply_of_true {u : NUtt} {w : NCard} (h : lbNuttMeaning u w = true) :
    L0 u w = ((extension u).card : ℝ≥0∞)⁻¹ :=
  RSA.L0OfBoolMeaning_apply_of_mem _ h

theorem L0_apply_of_false {u : NUtt} {w : NCard} (h : lbNuttMeaning u w ≠ true) :
    L0 u w = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ h

/-! ## §2. S1 — speaker as `PMF.normalize` of L0, with fallback at `.c0` -/

theorem L0_tsum_utterance_ne_top (w : NCard) : ∑' u, (L0 u w : ℝ≥0∞) ≠ ∞ :=
  PMF.tsum_apply_ne_top (fun u => L0 u) w

/-- Pragmatic speaker: `PMF.normalize (L0 · w)` at non-degenerate worlds,
`PMF.pure .one` at `.c0` (where no utterance applies). -/
noncomputable def S1 (w : NCard) : PMF NUtt :=
  if h : (∑' u, (L0 u w : ℝ≥0∞)) ≠ 0 then
    PMF.normalize (fun u => L0 u w) h (L0_tsum_utterance_ne_top w)
  else
    PMF.pure .one

/-- At reachable (`w ≠ .c0`) worlds, S1 unfolds to `PMF.normalize`. -/
theorem S1_eq_normalize {w : NCard}
    (h : (∑' u, (L0 u w : ℝ≥0∞)) ≠ 0) :
    S1 w = PMF.normalize (fun u => L0 u w) h (L0_tsum_utterance_ne_top w) :=
  dif_pos h

/-! ## §3. L1 — Bayesian inversion against the uniform world prior -/

instance : Nonempty NCard := ⟨.c0⟩
instance : Nonempty NUtt := ⟨.one⟩

noncomputable def worldPrior : PMF NCard := PMF.uniformOfFintype NCard

theorem worldPrior_ne_zero (w : NCard) : worldPrior w ≠ 0 :=
  (worldPrior.mem_support_iff w).mp (PMF.mem_support_uniformOfFintype w)

/-- Helper: at a world where utterance `u` applies, L0 puts mass at `u`. -/
private theorem L0_apply_ne_zero {u : NUtt} {w : NCard} (h : lbNuttMeaning u w = true) :
    L0 u w ≠ 0 := by
  rw [← PMF.mem_support_iff, mem_support_L0_iff]; exact h

/-- Helper: at a world where utterance `u` applies, the speaker tsum is non-zero
(so the conditional fallback chooses the normalize branch). -/
private theorem tsum_L0_ne_zero_at {u : NUtt} {w : NCard} (h : lbNuttMeaning u w = true) :
    (∑' u', (L0 u' w : ℝ≥0∞)) ≠ 0 :=
  PMF.tsum_apply_ne_zero L0 (a := u) (L0_apply_ne_zero h)

/-- Helper: at a world where utterance `u` applies, S1 puts non-zero mass on `u`. -/
private theorem S1_ne_zero_at {u : NUtt} {w : NCard} (h : lbNuttMeaning u w = true) :
    S1 w u ≠ 0 := by
  rw [S1_eq_normalize (tsum_L0_ne_zero_at h), ← PMF.mem_support_iff,
      PMF.mem_support_normalize_iff]
  exact L0_apply_ne_zero h

/-- Each utterance has an applicable world, so the L1 marginal is positive. -/
theorem L1_marginal_ne_zero (u : NUtt) :
    PMF.marginal S1 worldPrior u ≠ 0 := by
  cases u
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero .c1) (S1_ne_zero_at (by decide))
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero .c2) (S1_ne_zero_at (by decide))
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero .c3) (S1_ne_zero_at (by decide))

noncomputable def L1 (u : NUtt) : PMF NCard :=
  PMF.posterior S1 worldPrior u (L1_marginal_ne_zero u)

/-! ## §4. Findings (per-world S1 leaves sorry'd; structural shell complete) -/

/-- Per-world S1 leaf for `lb_rsa_strengthens_two`: at `.c3` the speaker has
3 applicable utterances (one, two, three), reducing the share for "two";
at `.c2` only "one" and "two" apply. So `S1 .c3 .two < S1 .c2 .two`.

**Discharge via partition-strict-monotonicity** (same pattern as
`S1_c2_lt_S1_c1_for_one`):
- Numerator equality: `L0 .two .c3 = L0 .two .c2`
- Partition strict: `tsum g .c2 < tsum f .c3` via strict witness at `.three`
  (L0 .three .c2 = 0 < 1 = L0 .three .c3). -/
theorem S1_c3_lt_S1_c2_for_two : S1 .c3 .two < S1 .c2 .two := by
  rw [S1_eq_normalize (tsum_L0_ne_zero_at (u := .two) (by decide)),
      S1_eq_normalize (tsum_L0_ne_zero_at (u := .two) (by decide))]
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt
  · -- L0 .two .c3 = L0 .two .c2: both = ((extension .two).card)⁻¹
    rw [L0_apply_of_true (by decide : lbNuttMeaning .two .c3 = true),
        L0_apply_of_true (by decide : lbNuttMeaning .two .c2 = true)]
  · exact L0_apply_ne_zero (by decide : lbNuttMeaning .two .c2 = true)
  · exact PMF.apply_ne_top (L0 .two) .c2
  · -- tsum g < tsum f via tsum_lt_tsum + strict witness at .three
    apply ENNReal.tsum_lt_tsum (PMF.tsum_apply_ne_top _ _) (i := .three)
    · intro u
      cases u
      · rw [L0_apply_of_true (by decide), L0_apply_of_true (by decide)]
      · rw [L0_apply_of_true (by decide), L0_apply_of_true (by decide)]
      · rw [L0_apply_of_false (by decide : lbNuttMeaning .three .c2 ≠ true)]
        exact zero_le _
    · -- strict at .three: 0 < L0 .three .c3 = 1
      rw [L0_apply_of_false (by decide : lbNuttMeaning .three .c2 ≠ true),
          L0_apply_of_true (by decide : lbNuttMeaning .three .c3 = true)]
      rw [show extension .three = {NCard.c3} from rfl]
      simp

/-- Headline: L1("two") prefers `.c2` over `.c3`. -/
theorem lb_rsa_strengthens_two : L1 .two .c2 > L1 .two .c3 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_c3_lt_S1_c2_for_two

/-- Per-world S1 leaf for `lb_rsa_strengthens_one`.

**Discharge via partition-strict-monotonicity** (the structural shape):
- Numerator equality: `L0 .one .c1 = L0 .one .c2` (both `= ((extension .one).card)⁻¹`)
- Numerator positive: `L0 .one .c1 ≠ 0`
- Partition strict: `Σ' u, L0 u .c1 < Σ' u, L0 u .c2`
  via pointwise `tsum_lt_tsum` with strict witness at `u = .two`
  (L0 .two .c1 = 0 < 1/2 = L0 .two .c2). -/
theorem S1_c2_lt_S1_c1_for_one : S1 .c2 .one < S1 .c1 .one := by
  rw [S1_eq_normalize (tsum_L0_ne_zero_at (u := .one) (by decide)),
      S1_eq_normalize (tsum_L0_ne_zero_at (u := .one) (by decide))]
  apply PMF.normalize_lt_of_apply_eq_of_sum_lt
  · -- L0 .one .c2 = L0 .one .c1: both = ((extension .one).card)⁻¹
    rw [L0_apply_of_true (by decide : lbNuttMeaning .one .c2 = true),
        L0_apply_of_true (by decide : lbNuttMeaning .one .c1 = true)]
  · -- g .one ≠ 0
    exact L0_apply_ne_zero (by decide : lbNuttMeaning .one .c1 = true)
  · -- g .one ≠ ⊤
    exact PMF.apply_ne_top (L0 .one) .c1
  · -- tsum g < tsum f via tsum_lt_tsum + strict witness at .two
    apply ENNReal.tsum_lt_tsum (PMF.tsum_apply_ne_top _ _) (i := .two)
    · -- pointwise: L0 u .c1 ≤ L0 u .c2
      intro u
      cases u
      · -- .one: equal
        rw [L0_apply_of_true (by decide), L0_apply_of_true (by decide)]
      · -- .two: 0 ≤ positive
        rw [L0_apply_of_false (by decide : lbNuttMeaning .two .c1 ≠ true)]
        exact zero_le _
      · -- .three: 0 ≤ 0
        rw [L0_apply_of_false (by decide : lbNuttMeaning .three .c1 ≠ true),
            L0_apply_of_false (by decide : lbNuttMeaning .three .c2 ≠ true)]
    · -- strict witness at .two: 0 < ((extension .two).card)⁻¹
      rw [L0_apply_of_false (by decide : lbNuttMeaning .two .c1 ≠ true),
          L0_apply_of_true (by decide : lbNuttMeaning .two .c2 = true)]
      -- Goal: 0 < ((extension .two).card : ℝ≥0∞)⁻¹
      -- extension .two = {.c2, .c3} (card 2); (2)⁻¹ > 0
      rw [show extension .two = {NCard.c2, NCard.c3} from rfl]
      simp

/-- Headline: L1("one") prefers `.c1` over `.c2`. -/
theorem lb_rsa_strengthens_one : L1 .one .c1 > L1 .one .c2 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_c2_lt_S1_c1_for_one

/-- Per-world S1 leaf for `lb_three_peaked`: `.three` doesn't apply at `.c2`
(since 2 < 3), so S1 .c2 .three = 0. At `.c3`, S1 .c3 .three > 0.

Discharged via `PMF.normalize_lt_of_apply_zero_pos` (vacuous-zero pattern).
The conditional fallback unfolds via `S1_eq_normalize` since both `.c2` and
`.c3` are non-degenerate (other utterances do apply). -/
theorem S1_c2_lt_S1_c3_for_three : S1 .c2 .three < S1 .c3 .three := by
  rw [S1_eq_normalize (tsum_L0_ne_zero_at (u := .one) (by decide)),
      S1_eq_normalize (tsum_L0_ne_zero_at (u := .three) (by decide))]
  exact PMF.normalize_lt_of_apply_zero_pos _ _ _ _ _ _ _
    (L0_apply_of_false (by decide)) (L0_apply_ne_zero (by decide))

/-- Headline: L1("three") trivially peaks at `.c3`. -/
theorem lb_three_peaked : L1 .three .c3 > L1 .three .c2 := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_c2_lt_S1_c3_for_three

end BylininaNouwen2020.PMF
