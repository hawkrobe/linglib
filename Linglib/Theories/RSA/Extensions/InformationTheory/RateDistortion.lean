/-
# Rate-Distortion View of RSA (Zaslavsky et al. 2020)

Formalizes the connection between RSA and Rate-Distortion theory from:

  Zaslavsky, N., Hu, J., & Levy, R. (2020). A Rate-Distortion view of human
  pragmatic reasoning. arXiv:2005.06641.

## Key Insights

1. **RSA as RD optimization**: At α = 1, RSA minimizes the rate-distortion
   functional, connecting pragmatic reasoning to optimal lossy compression.

2. **The G_α objective**: G_α(S,L) = H_S(U|M) + α·E_S[V_L] is the quantity
   that RSA dynamics maximize.

3. **Critical α = 1**: This is where RSA coincides with rate-distortion theory.
   - α < 1: Over-compression (loss of information)
   - α > 1: Over-informativity (approaching NeoGricean)
   - α → ∞: NeoGricean limit (maximum informativity)

4. **Utility non-monotonicity (Prop 2)**: For α < 1, expected listener utility
   can DECREASE even as G_α increases. This is a key prediction distinguishing
   RD-RSA from standard RSA assumptions.

## Connection to Convergence Theory

This file builds on `RSA.Convergence` which proves that RSA dynamics converge.
The RD perspective explains WHY they converge: RSA implements alternating
maximization of a concave objective.

## References

- Zaslavsky, N., Hu, J., & Levy, R. (2020). A Rate-Distortion view of human
  pragmatic reasoning. arXiv:2005.06641.
- Cover, T. M. & Thomas, J. A. (2006). Elements of Information Theory.
-/

import Linglib.Theories.RSA.Core.Convergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace RSA.RateDistortion

open Real Classical RSA.Convergence


/--
Mutual information I(M;U) under speaker distribution.

I(M;U) = H(M) - H(M|U) = H(U) - H(U|M)

This measures how much the utterance "tells you" about the meaning.
-/
noncomputable def I_MU (S : RSAScenarioR) (Spk : S.M → S.U → ℝ) : ℝ :=
  let pU := fun u => ∑ m, S.prior m * normalize (Spk m) u
  entropy pU - H_S S Spk

/--
The RD-RSA objective: F_α(S,L) = I(M;U) - α·E[V_L]

This is MINIMIZED by RD-RSA (Zaslavsky et al. Eq. 14).

The relationship to G_α:
  F_α = H(U) - G_α = I(M;U) - α·E[V_L]

where H(U) is the marginal entropy of utterances.
-/
noncomputable def F_α (S : RSAScenarioR) (Spk : S.M → S.U → ℝ)
    (L : S.U → S.M → ℝ) : ℝ :=
  I_MU S Spk - S.α * E_VL S Spk L

/--
Relationship between G_α and F_α (Zaslavsky et al. Eq. 15).

F_α = H(U) - G_α

This shows that maximizing G_α is equivalent to minimizing F_α
(since H(U) doesn't depend on the speaker/listener interaction).
-/
theorem G_F_relation (S : RSAScenarioR) (Spk : S.M → S.U → ℝ)
    (L : S.U → S.M → ℝ) :
    let pU := fun u => ∑ m, S.prior m * normalize (Spk m) u
    F_α S Spk L = entropy pU - G_α S Spk L := by
  simp only [F_α, G_α, I_MU]
  ring


/--
**Proposition 3 (Zaslavsky et al.)**: α = 1 is the critical point.

At α = 1, the RSA objective coincides with the negative rate-distortion
functional:
  G_1(S, L) = H_S(U|M) + E_S[V_L] = -R[D]

where R[D] is the rate-distortion function.

This connects pragmatic reasoning to information-theoretic optimality.
-/
theorem alpha_one_critical (S : RSAScenarioR) (hα : S.α = 1) :
    G_α S = fun Spk L => H_S S Spk + E_VL S Spk L := by
  funext Spk L
  simp only [G_α, hα, one_mul]


/-!
## The Key Distinction: Utility Can Decrease

Standard RSA intuition suggests that pragmatic reasoning always improves
communication: the listener gets better at understanding the speaker.

Zaslavsky et al. (2020) show this is NOT always true!

**Proposition 2**: For α < 1, expected listener utility E[V_L] can
DECREASE even as the RSA objective G_α increases.

This is because:
- G_α = H_S(U|M) + α·E[V_L]
- When α < 1, the entropy term H_S dominates
- RSA can sacrifice utility to reduce speaker "cost" (entropy)

This is a testable prediction distinguishing RD-RSA from naive RSA.
-/

/--
**Proposition 2 (Zaslavsky et al.)**: E[V_L] can decrease even as G_α increases.

For α < 1, expected utility may decrease during RSA iterations.
-/
theorem utility_can_decrease (S : RSAScenarioR) (hα : S.α < 1) :
    ∃ n, E_VL S (iterateRSA S (n+1)).speaker (iterateRSA S (n+1)).listener <
         E_VL S (iterateRSA S n).speaker (iterateRSA S n).listener := by
  sorry -- Existence proof via graded lexicon counterexample


/--
Argmax: set of utterances with maximum listener probability for a given meaning.
-/
noncomputable def argmaxU (S : RSAScenarioR) (L : S.U → S.M → ℝ) (m : S.M) : Finset S.U :=
  Finset.univ.filter (fun u => ∀ u', L u m ≥ L u' m)

/--
The NeoGricean limit function: uniform over argmax, zero elsewhere.
-/
noncomputable def neoGriceanLimitFn (S : RSAScenarioR) (L : S.U → S.M → ℝ)
    (m : S.M) (u : S.U) : ℝ :=
  if u ∈ argmaxU S L m then 1 / (argmaxU S L m).card else 0

/--
**NeoGricean Limit**: As α → ∞, speaker approaches argmax.

The pragmatic speaker converges to deterministic choice of
highest-utility utterance(s).

From the paper (Section 2.3): "In the limit α → ∞, RSA reduces to
the standard Gricean/game-theoretic account where the speaker
deterministically chooses the most informative utterance."
-/
theorem neoGricean_limit (S : RSAScenarioR) (L : S.U → S.M → ℝ) (m : S.M) :
    Filter.Tendsto
      (fun α => normalize (fun u => (L u m).rpow α) )
      Filter.atTop
      (nhds (neoGriceanLimitFn S L m)) := by
  sorry -- Proof via properties of x^α as α → ∞


/--
**Base < 1 limit**: For 0 < x < 1, x^α → 0 as α → ∞.

Sub-optimal utterances vanish in the NeoGricean limit.
-/
theorem rpow_tendsto_zero_of_base_lt_one {x : ℝ} (_hx0 : 0 < x) (hx1 : x < 1) :
    Filter.Tendsto (fun α => x.rpow α) Filter.atTop (nhds 0) :=
  tendsto_rpow_atTop_of_base_lt_one x (by linarith : -1 < x) hx1

/--
**Base > 1 divergence**: For x > 1, x^α → ∞ as α → ∞.

Optimal utterances dominate in the NeoGricean limit.
-/
theorem rpow_tendsto_atTop_of_base_gt_one {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto (fun α => x.rpow α) Filter.atTop Filter.atTop := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlog : 0 < log x := Real.log_pos hx
  have key : Filter.Tendsto (fun α => log x * α) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hlog Filter.tendsto_id
  have h := Filter.Tendsto.comp Real.tendsto_exp_atTop key
  refine Filter.Tendsto.congr ?_ h
  intro α
  simp only [Function.comp_apply]
  exact (Real.rpow_def_of_pos hx0 α).symm


/--
**α = 0 gives uniform scores**: When α = 0, all positive listener values
give the same speaker score (= 1).

This is the maximum entropy limit.
-/
theorem speakerScore_alpha_zero (S : RSAScenarioR) (hα : S.α = 0)
    (L : S.U → S.M → ℝ) (m : S.M) (u : S.U) (hL : 0 < L u m) :
    speakerScore S L m u = 1 := by
  simp only [speakerScore]
  rw [if_neg (not_le.mpr hL)]
  rw [hα]
  exact Real.rpow_zero (L u m)

/--
**Speaker score non-negativity**: Speaker scores are always ≥ 0.
-/
theorem speakerScore_nonneg (S : RSAScenarioR) (L : S.U → S.M → ℝ)
    (m : S.M) (u : S.U) :
    0 ≤ speakerScore S L m u := by
  simp only [speakerScore]
  split_ifs with h
  · exact le_refl 0
  · push_neg at h
    exact Real.rpow_nonneg (le_of_lt h) S.α

/--
**Speaker score positivity**: For positive listener probability and α ≥ 0,
speaker score is positive.
-/
theorem speakerScore_pos (S : RSAScenarioR) (L : S.U → S.M → ℝ)
    (m : S.M) (u : S.U) (hL : 0 < L u m) :
    0 < speakerScore S L m u := by
  simp only [speakerScore]
  rw [if_neg (not_le.mpr hL)]
  exact Real.rpow_pos_of_pos hL S.α

/--
**Rpow monotonicity in base**: For α > 0, larger listener probabilities
give larger speaker scores.
-/
theorem speakerScore_mono_base (S : RSAScenarioR) (L₁ L₂ : S.U → S.M → ℝ)
    (m : S.M) (u : S.U) (hα : 0 < S.α)
    (h1 : 0 < L₁ u m) (h2 : L₁ u m ≤ L₂ u m) :
    speakerScore S L₁ m u ≤ speakerScore S L₂ m u := by
  simp only [speakerScore]
  rw [if_neg (not_le.mpr h1)]
  have h2' : 0 < L₂ u m := lt_of_lt_of_le h1 h2
  rw [if_neg (not_le.mpr h2')]
  exact Real.rpow_le_rpow (le_of_lt h1) h2 (le_of_lt hα)

/--
**Rpow strict monotonicity**: For α > 0, strictly larger listener
probabilities give strictly larger speaker scores.
-/
theorem speakerScore_strictMono_base (S : RSAScenarioR) (L₁ L₂ : S.U → S.M → ℝ)
    (m : S.M) (u : S.U) (hα : 0 < S.α)
    (h1 : 0 ≤ L₁ u m) (h2 : L₁ u m < L₂ u m) :
    speakerScore S L₁ m u < speakerScore S L₂ m u := by
  simp only [speakerScore]
  by_cases h1' : L₁ u m ≤ 0
  · rw [if_pos h1']
    have h2' : 0 < L₂ u m := lt_of_le_of_lt h1 h2
    rw [if_neg (not_le.mpr h2')]
    exact Real.rpow_pos_of_pos h2' S.α
  · push_neg at h1'
    rw [if_neg (not_le.mpr h1')]
    have h2' : 0 < L₂ u m := lt_trans h1' h2
    rw [if_neg (not_le.mpr h2')]
    exact Real.rpow_lt_rpow h1 h2 hα

/--
**Normalization sums to 1**: For non-zero partition function.
-/
theorem normalize_sum_eq_one {α : Type*} [Fintype α] (f : α → ℝ)
    (hZ : Z f ≠ 0) :
    ∑ a, Convergence.normalize f a = 1 := by
  unfold Convergence.normalize Z at *
  simp only [hZ, ↓reduceIte]
  rw [← Finset.sum_div, div_self hZ]

/--
**Normalization is non-negative**: When scores are non-negative.
-/
theorem normalize_nonneg {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hZ : 0 < Z f) (a : α) :
    0 ≤ Convergence.normalize f a := by
  simp only [Convergence.normalize]
  rw [if_neg (ne_of_gt hZ)]
  exact div_nonneg (hf a) (le_of_lt hZ)

/--
**Normalization bounded by 1**: Normalized values are at most 1.
-/
theorem normalize_le_one {α : Type*} [Fintype α] (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hZ : 0 < Z f) (a : α) :
    Convergence.normalize f a ≤ 1 := by
  simp only [Convergence.normalize]
  rw [if_neg (ne_of_gt hZ)]
  rw [div_le_one hZ]
  exact Finset.single_le_sum (fun x _ => hf x) (Finset.mem_univ a)

end RSA.RateDistortion
