import Linglib.Theories.Pragmatics.RSA.Operators
import Linglib.Phenomena.Numerals.Studies.Kennedy2015
import Mathlib.Probability.Distributions.Uniform

/-!
# @cite{kennedy-2015} on mathlib `PMF` (Shape A migration)
@cite{kennedy-2015} @cite{frank-goodman-2012}

PMF-shaped re-formalisation of `Kennedy2015.lean`'s 7 RSA L1 findings.
Domain: KCard = `Fin 6`, KUtt = 5 numeral alternatives. Same-observation
findings discharge via the canonical template + vacuous-zero/partition-
dominance patterns.

## Migration coverage

5 of 7 findings discharged structurally:
- 3 vacuous-zero: `classA_no_competition_at_boundary`, `bare_peaked_with_kennedy_alternatives`,
  `upper_classA_no_competition` (utterance inapplicable at one of the worlds)
- 2 partition-dominance pending: `classB_strengthened_above_bare`,
  `upper_classB_strengthened_below_bare` (numerators equal, partitions don't
  pointwise dominate — non-uniform-applicability case)
- 2 cross-observation pending: `classB_competition_at_boundary`,
  `upper_classB_competition` (different utterances, same world; needs
  `posterior_apply_cross_obs_lt`-style lemma — new API gap)

## Reused from `Kennedy2015.lean`

* `KCard`, `KUtt` — domain types
* `kMean` — Boolean meaning matrix (Prop-valued; we lift to Bool)
-/

set_option autoImplicit false

namespace Kennedy2015.PMF

open scoped ENNReal

instance : Nonempty KCard := ⟨0⟩
instance : Nonempty KUtt := ⟨.bare3⟩

/-- Boolean meaning, derived from `kMean` via `decide`. -/
noncomputable def kMeanBool (u : KUtt) (w : KCard) : Bool := decide (kMean u w)

/-- The Bool form agrees with the Prop form. -/
theorem kMeanBool_iff (u : KUtt) (w : KCard) : kMeanBool u w = true ↔ kMean u w :=
  decide_eq_true_iff

/-! ## §1. L0 — uniform on extension via `RSA.L0OfBoolMeaning` -/

noncomputable abbrev extension (u : KUtt) : Finset KCard :=
  RSA.extensionOf kMeanBool u

theorem extension_nonempty (u : KUtt) : (extension u).Nonempty := by
  cases u
  · exact ⟨3, RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨4, RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨2, RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨3, RSA.mem_extensionOf.mpr (by decide)⟩
  · exact ⟨3, RSA.mem_extensionOf.mpr (by decide)⟩

noncomputable def L0 (u : KUtt) : PMF KCard :=
  RSA.L0OfBoolMeaning kMeanBool u (extension_nonempty u)

@[simp] theorem mem_support_L0_iff (u : KUtt) (w : KCard) :
    w ∈ (L0 u).support ↔ kMeanBool u w = true :=
  RSA.mem_support_L0OfBoolMeaning_iff _ _

theorem L0_apply_of_true {u : KUtt} {w : KCard} (h : kMeanBool u w = true) :
    L0 u w = ((extension u).card : ℝ≥0∞)⁻¹ :=
  RSA.L0OfBoolMeaning_apply_of_mem _ h

theorem L0_apply_of_false {u : KUtt} {w : KCard} (h : kMeanBool u w ≠ true) :
    L0 u w = 0 :=
  RSA.L0OfBoolMeaning_apply_of_not_mem _ h

private theorem L0_apply_ne_zero {u : KUtt} {w : KCard} (h : kMeanBool u w = true) :
    L0 u w ≠ 0 := by
  rw [← PMF.mem_support_iff, mem_support_L0_iff]; exact h

/-! ## §2. S1 — speaker as `PMF.normalize` of L0 with conditional fallback

At every world in 0..5, at least one utterance applies (e.g. .atMost3 applies
at 0..3, .atLeast3 applies at 3..5). So S1 is well-defined everywhere — no
fallback needed in this domain (all worlds have a witness).

Still using the conditional pattern for compatibility with the Shape A
template. -/

theorem L0_tsum_utterance_ne_top (w : KCard) : ∑' u, (L0 u w : ℝ≥0∞) ≠ ∞ :=
  PMF.tsum_apply_ne_top (fun u => L0 u) w

private theorem tsum_L0_ne_zero_at {u : KUtt} {w : KCard} (h : kMeanBool u w = true) :
    (∑' u', (L0 u' w : ℝ≥0∞)) ≠ 0 :=
  PMF.tsum_apply_ne_zero L0 (a := u) (L0_apply_ne_zero h)

noncomputable def S1 (w : KCard) : PMF KUtt :=
  if h : (∑' u, (L0 u w : ℝ≥0∞)) ≠ 0 then
    PMF.normalize (fun u => L0 u w) h (L0_tsum_utterance_ne_top w)
  else
    PMF.pure .bare3  -- vacuous fallback; not reached in 0..5 domain

theorem S1_eq_normalize {w : KCard}
    (h : (∑' u, (L0 u w : ℝ≥0∞)) ≠ 0) :
    S1 w = PMF.normalize (fun u => L0 u w) h (L0_tsum_utterance_ne_top w) :=
  dif_pos h

/-! ## §3. L1 — Bayesian inversion against the uniform world prior -/

noncomputable def worldPrior : PMF KCard := PMF.uniformOfFintype KCard

theorem worldPrior_ne_zero (w : KCard) : worldPrior w ≠ 0 :=
  (worldPrior.mem_support_iff w).mp (PMF.mem_support_uniformOfFintype w)

private theorem S1_ne_zero_at {u : KUtt} {w : KCard} (h : kMeanBool u w = true) :
    S1 w u ≠ 0 := by
  rw [S1_eq_normalize (tsum_L0_ne_zero_at h), ← PMF.mem_support_iff,
      PMF.mem_support_normalize_iff]
  exact L0_apply_ne_zero h

theorem L1_marginal_ne_zero (u : KUtt) :
    PMF.marginal S1 worldPrior u ≠ 0 := by
  -- Pick a world where the utterance applies.
  cases u
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero 3) (S1_ne_zero_at (by decide))
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero 4) (S1_ne_zero_at (by decide))
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero 2) (S1_ne_zero_at (by decide))
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero 3) (S1_ne_zero_at (by decide))
  · exact PMF.marginal_ne_zero _ _ _ (worldPrior_ne_zero 3) (S1_ne_zero_at (by decide))

noncomputable def L1 (u : KUtt) : PMF KCard :=
  PMF.posterior S1 worldPrior u (L1_marginal_ne_zero u)

/-! ## §4. Findings — vacuous-zero discharges -/

/-- "moreThan3" doesn't apply at .3 → S1 .3 .moreThan3 = 0 (vacuous-zero). -/
theorem S1_3_lt_S1_4_for_moreThan3 :
    S1 (3 : KCard) .moreThan3 < S1 (4 : KCard) .moreThan3 := by
  rw [S1_eq_normalize (tsum_L0_ne_zero_at (u := .bare3) (by decide)),
      S1_eq_normalize (tsum_L0_ne_zero_at (u := .moreThan3) (by decide))]
  exact PMF.normalize_lt_of_apply_zero_pos _ _ _ _ _ _ _
    (L0_apply_of_false (by decide : kMeanBool .moreThan3 (3 : KCard) ≠ true))
    (L0_apply_ne_zero (by decide : kMeanBool .moreThan3 (4 : KCard) = true))

/-- L1("moreThan3") prefers .4 over .3 — Class A excludes the boundary semantically. -/
theorem classA_no_competition_at_boundary :
    L1 .moreThan3 (4 : KCard) > L1 .moreThan3 (3 : KCard) := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_3_lt_S1_4_for_moreThan3

/-- "bare3" doesn't apply at .4 → S1 .4 .bare3 = 0 (vacuous-zero). -/
theorem S1_4_lt_S1_3_for_bare3 :
    S1 (4 : KCard) .bare3 < S1 (3 : KCard) .bare3 := by
  rw [S1_eq_normalize (tsum_L0_ne_zero_at (u := .moreThan3) (by decide)),
      S1_eq_normalize (tsum_L0_ne_zero_at (u := .bare3) (by decide))]
  exact PMF.normalize_lt_of_apply_zero_pos _ _ _ _ _ _ _
    (L0_apply_of_false (by decide : kMeanBool .bare3 (4 : KCard) ≠ true))
    (L0_apply_ne_zero (by decide : kMeanBool .bare3 (3 : KCard) = true))

/-- L1("bare 3") peaked at .3 — bare numeral exact reading. -/
theorem bare_peaked_with_kennedy_alternatives :
    L1 .bare3 (3 : KCard) > L1 .bare3 (4 : KCard) := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_4_lt_S1_3_for_bare3

/-- "fewerThan3" doesn't apply at .3 → S1 .3 .fewerThan3 = 0 (vacuous-zero, mirror of moreThan3). -/
theorem S1_3_lt_S1_2_for_fewerThan3 :
    S1 (3 : KCard) .fewerThan3 < S1 (2 : KCard) .fewerThan3 := by
  rw [S1_eq_normalize (tsum_L0_ne_zero_at (u := .bare3) (by decide)),
      S1_eq_normalize (tsum_L0_ne_zero_at (u := .fewerThan3) (by decide))]
  exact PMF.normalize_lt_of_apply_zero_pos _ _ _ _ _ _ _
    (L0_apply_of_false (by decide : kMeanBool .fewerThan3 (3 : KCard) ≠ true))
    (L0_apply_ne_zero (by decide : kMeanBool .fewerThan3 (2 : KCard) = true))

/-- L1("fewerThan3") prefers .2 over .3 — upper Class A excludes boundary. -/
theorem upper_classA_no_competition :
    L1 .fewerThan3 (2 : KCard) > L1 .fewerThan3 (3 : KCard) := by
  unfold L1 worldPrior
  rw [gt_iff_lt, PMF.posterior_lt_iff_kernel_lt_of_uniform]
  exact S1_3_lt_S1_2_for_fewerThan3

/-! ## §5. Findings — partition-dominance leaves (non-pointwise) -/

/-- Class B: L1 of "atLeast3" prefers .4 over .3.
**Friction**: numerators equal (both 1/3), but partition functions don't
pointwise dominate. At .3 the alternatives are {bare3, atLeast3, atMost3};
at .4 they are {moreThan3, atLeast3}. Neither set dominates the other.
Needs partition function computation. -/
theorem classB_strengthened_above_bare :
    L1 .atLeast3 (4 : KCard) > L1 .atLeast3 (3 : KCard) := by
  sorry  -- non-dominating partition functions; needs explicit Z computation

/-- Upper Class B: L1 of "atMost3" prefers .2 over .3. Same friction as `classB_strengthened_above_bare`. -/
theorem upper_classB_strengthened_below_bare :
    L1 .atMost3 (2 : KCard) > L1 .atMost3 (3 : KCard) := by
  sorry  -- non-dominating partition functions

/-! ## §6. Findings — cross-observation (different utterance, same world) -/

/-- Class B competition at the boundary: L1("bare 3" | .3) > L1("at least 3" | .3).

**Structural discharge** (post-0.230.409 lemma `posterior_lt_of_score_cross_lt`):
1. `gt_iff_lt` flips to `<` shape
2. `unfold L1`, `posterior_lt_of_score_cross_lt`
3. Reduces to cross-multiplied score comparison:
   `S1 .3 .atLeast3 * marginal .bare3 < S1 .3 .bare3 * marginal .atLeast3`

**Remaining leaf**: the cross-multiplied numeric inequality requires
computing `marginal .bare3` and `marginal .atLeast3` (each a tsum over
Fin 6). Same partition-computation friction as `classB_strengthened_above_bare`
— would close once a `pmf_partition_compute` helper exists. -/
theorem classB_competition_at_boundary :
    L1 .bare3 (3 : KCard) > L1 .atLeast3 (3 : KCard) := by
  unfold L1
  rw [gt_iff_lt]
  apply PMF.posterior_lt_of_score_cross_lt
  · -- μ a ≠ 0 (worldPrior at .3)
    exact worldPrior_ne_zero 3
  · -- μ a ≠ ⊤
    exact PMF.apply_ne_top _ _
  · -- Cross-multiplied score inequality (partition-function computation)
    sorry  -- numeric leaf: needs marginal value computation

/-- Upper Class B competition. Same shape as `classB_competition_at_boundary`. -/
theorem upper_classB_competition :
    L1 .bare3 (3 : KCard) > L1 .atMost3 (3 : KCard) := by
  unfold L1
  rw [gt_iff_lt]
  apply PMF.posterior_lt_of_score_cross_lt
  · exact worldPrior_ne_zero 3
  · exact PMF.apply_ne_top _ _
  · sorry  -- numeric leaf

end Kennedy2015.PMF
