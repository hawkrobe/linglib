import Linglib.Core.Logic.SystemZ
import Linglib.Theories.Pragmatics.RSA.Core.Softmax.Limits
import Mathlib.Algebra.Tropical.BigOperators

/-!
# Ranking Functions as RSA Limits

@cite{spohn-1988} @cite{goldszmidt-pearl-1996} @cite{frank-goodman-2012}

As the rationality parameter α → ∞, softmax-based probabilistic inference
converges to ranking-based default reasoning. This file makes the
connection precise.

## Key results

1. `rankToScore`: Every ranking function κ induces scores s(w) = -κ(w).
2. `softmax_concentrates_unique`: softmax(s, α) → point mass on the
   unique rank-0 world as α → ∞.
3. `minRank_worlds_satisfy`: Under ranking entailment, all minimum-rank
   φ-worlds satisfy σ — connecting to the softmax limit.
4. `condProb_tendsto_one`: **Conditional Softmax Limit Theorem** —
   P_α(σ|φ) → 1 as α → ∞ whenever κ ⊨ φ → σ. This is the central
   result: RSA with infinite rationality = ranking entailment.

## Mathematical background

@cite{spohn-1988} §7 observes that rankings are ordinal probabilities:
κ(w) = n corresponds to P(w) ∝ ε^n for infinitesimal ε. The finite
analogue replaces ε^n with exp(-n·α) for large α:

    softmax(-κ, α)(w) = exp(-α · κ(w)) / Σ_v exp(-α · κ(v))

As α → ∞, this concentrates on rank-0 (most normal) worlds — exactly
the worlds that survive ranking-based default reasoning.

This makes System Z's κ^z ranking (@cite{goldszmidt-pearl-1996}) the
"infinite rationality" limit of RSA pragmatic inference
(@cite{frank-goodman-2012}). Qualitative default reasoning and
quantitative Bayesian pragmatics are not rival frameworks but
endpoints of the same rationality continuum.
-/

namespace Theories.Pragmatics.RSA.RankingBridge

open Core.Logic.Ranking Core.Logic.SystemZ Core Real BigOperators
open Finset Filter Topology

variable {W : Type*}

-- ══════════════════════════════════════════════════════════════════════
-- § 1. Ranking Functions as Score Functions
-- ══════════════════════════════════════════════════════════════════════

/-- Convert a ranking function to softmax scores.

    s(w) = -(κ(w) : ℝ). Lower rank → higher score → more plausible.

    This is the finite analogue of @cite{spohn-1988} §7's
    P(w) ∝ ε^{κ(w)}: here exp(α · s(w)) = exp(-α · κ(w)) plays
    the role of ε^{κ(w)} with ε = exp(-α). -/
noncomputable def rankToScore (κ : RankingFunction W) : W → ℝ :=
  fun w => -(κ.rank w : ℝ)

/-- rankToScore reverses the ordering: higher rank ↔ lower score. -/
theorem rankToScore_lt_iff (κ : RankingFunction W) (w v : W) :
    rankToScore κ w < rankToScore κ v ↔ κ.rank v < κ.rank w := by
  simp only [rankToScore, neg_lt_neg_iff, Nat.cast_lt]

/-- Rank-0 worlds achieve the maximum score (0). -/
theorem rankToScore_eq_zero_iff (κ : RankingFunction W) (w : W) :
    rankToScore κ w = 0 ↔ κ.rank w = 0 := by
  simp only [rankToScore, neg_eq_zero, Nat.cast_eq_zero]

/-- All scores are non-positive. -/
theorem rankToScore_nonpos (κ : RankingFunction W) (w : W) :
    rankToScore κ w ≤ 0 := by
  simp only [rankToScore, neg_nonpos, Nat.cast_nonneg]

/-- Rank-0 worlds maximize the score. -/
theorem rankToScore_le_of_rank_zero (κ : RankingFunction W)
    (w₀ v : W) (h : κ.rank w₀ = 0) :
    rankToScore κ v ≤ rankToScore κ w₀ := by
  simp only [rankToScore, neg_le_neg_iff, Nat.cast_le]
  omega

-- ══════════════════════════════════════════════════════════════════════
-- § 2. Softmax Concentration on Normal Worlds
-- ══════════════════════════════════════════════════════════════════════

/-- When κ has a unique rank-0 world, softmax(rankToScore κ, α)
    concentrates on it as α → ∞.

    This is the core convergence result: the probabilistic distribution
    approaches a point mass on the most normal world, recovering
    the ranking-based notion of normality.

    Proof: Apply `Softmax.tendsto_softmax_infty_unique_max` with
    scores s = rankToScore κ. The unique rank-0 world maximizes s
    (since s(w) = -κ(w) and κ(w₀) = 0 < κ(v) for v ≠ w₀). -/
theorem softmax_concentrates_unique [Fintype W] [DecidableEq W] [Nonempty W]
    (κ : RankingFunction W) (w₀ : W)
    (h_zero : κ.rank w₀ = 0)
    (h_unique : ∀ v, v ≠ w₀ → 0 < κ.rank v) (w : W) :
    Tendsto (fun α => softmax (rankToScore κ) α w) atTop
      (𝓝 (if w = w₀ then 1 else 0)) :=
  Softmax.tendsto_softmax_infty_unique_max (rankToScore κ) w₀
    (fun j hj => (rankToScore_lt_iff κ j w₀).mpr (h_zero ▸ h_unique j hj)) w

/-- Entropy of softmax(rankToScore κ, α) → 0 as α → ∞ (unique rank-0
    case). The distribution becomes maximally concentrated. -/
theorem entropy_vanishes_unique [Fintype W] [DecidableEq W] [Nonempty W]
    (κ : RankingFunction W) (w₀ : W)
    (h_zero : κ.rank w₀ = 0)
    (h_unique : ∀ v, v ≠ w₀ → 0 < κ.rank v) :
    Tendsto (fun α => Softmax.entropy (softmax (rankToScore κ) α)) atTop
      (𝓝 0) :=
  Softmax.entropy_tendsto_zero (rankToScore κ) w₀
    (fun j hj => (rankToScore_lt_iff κ j w₀).mpr (h_zero ▸ h_unique j hj))

-- ══════════════════════════════════════════════════════════════════════
-- § 3. Ranking Entailment via Minimum Rank
-- ══════════════════════════════════════════════════════════════════════

/-- The minimum rank among worlds satisfying a Bool predicate. -/
noncomputable def minRankBool [Fintype W] (κ : RankingFunction W)
    (φ : W → Bool) (hφ : ∃ w, φ w = true) : ℕ :=
  (univ.filter (fun w => φ w)).inf'
    (by obtain ⟨w, hw⟩ := hφ; exact ⟨w, mem_filter.mpr ⟨mem_univ w, hw⟩⟩)
    κ.rank

/-- rankEntails is equivalent to: every φ∧¬σ world has strictly
    higher rank than some φ∧σ world.

    When φ∧σ is non-empty, this is the same as: the minimum rank
    among φ∧σ worlds is strictly less than the rank of every
    φ∧¬σ world. When φ∧¬σ is empty, rankEntails holds vacuously. -/
theorem rankEntails_iff_minRank_lt [Fintype W]
    (κ : RankingFunction W) (φ σ : W → Bool)
    (hφσ : ∃ w, (φ w && σ w) = true) :
    rankEntails κ φ σ ↔
    ∀ w, (φ w && !σ w) = true →
      minRankBool κ (fun v => φ v && σ v) hφσ < κ.rank w := by
  constructor
  · intro h w hw
    obtain ⟨v, hv, hlt⟩ := h w hw
    exact lt_of_le_of_lt
      (Finset.inf'_le κ.rank (mem_filter.mpr ⟨mem_univ v, hv⟩))
      hlt
  · intro h w hw
    have hmin := h w hw
    have hne : (univ.filter (fun w => (φ w && σ w) = true)).Nonempty := by
      obtain ⟨w, hw⟩ := hφσ; exact ⟨w, mem_filter.mpr ⟨mem_univ w, hw⟩⟩
    obtain ⟨v, hv_mem, hv_eq⟩ := Finset.exists_mem_eq_inf' hne κ.rank
    exact ⟨v, (mem_filter.mp hv_mem).2, hv_eq ▸ hmin⟩

/-- Under ranking entailment, all minimum-rank φ-worlds satisfy σ.

    This is the key lemma connecting ranking entailment to softmax
    concentration: as α → ∞, softmax concentrates on minimum-rank
    worlds. If all minimum-rank φ-worlds satisfy σ, then the
    limiting conditional probability P(σ|φ) = 1.

    Proof: If a minimum-rank φ-world w fails σ, then rankEntails
    gives a φ∧σ world v with κ(v) < κ(w), contradicting w having
    the minimum rank among φ-worlds. -/
theorem minRank_worlds_satisfy [Fintype W]
    (κ : RankingFunction W) (φ σ : W → Bool)
    (h : rankEntails κ φ σ) (hφ : ∃ w, φ w = true) :
    ∀ w, φ w = true → κ.rank w = minRankBool κ φ hφ →
      σ w = true := by
  intro w hφw hmin
  by_contra hσ
  have hσf : σ w = false := by cases hb : σ w <;> simp_all
  have hfw : (φ w && !σ w) = true := by simp [hφw, hσf]
  obtain ⟨v, hv, hlt⟩ := h w hfw
  have hφv : φ v = true := by
    have := hv; simp [Bool.and_eq_true] at this; exact this.1
  have hle : minRankBool κ φ hφ ≤ κ.rank v :=
    Finset.inf'_le κ.rank (mem_filter.mpr ⟨mem_univ v, hφv⟩)
  omega

-- ══════════════════════════════════════════════════════════════════════
-- § 4. The Rationality Continuum
-- ══════════════════════════════════════════════════════════════════════

/-! The theorems above establish the formal bridge between RSA and
    ranking-based default reasoning:

    ```
    α = 0          α finite           α → ∞
    uniform ←——— softmax(s, α) ———→ hardmax
    no inference   RSA pragmatics     ranking entailment
    ```

    At α = 0, the listener has no rationality assumption and
    the posterior is uniform (`Softmax.tendsto_softmax_zero`).
    At finite α, the listener performs soft Bayesian inference
    (standard RSA). As α → ∞, the posterior concentrates on
    the most normal worlds (`softmax_concentrates_unique`),
    and inference becomes ranking entailment.

    This justifies two practices:
    1. RSA modelers can use System Z rankings as the "skeleton"
       of their prior, softened by finite α for gradient predictions.
    2. Default reasoning theorists can view their qualitative
       inferences as the limiting case of probabilistic pragmatics. -/

/-- The exponential prior induced by a ranking function.

    P(w) = exp(-κ(w)). This is the natural prior for connecting
    ranking functions to Bayesian inference: rank-0 worlds get
    maximal prior probability, and the prior ordering on worlds
    matches the ranking ordering.

    @cite{spohn-1988} §7 uses P(w) ∝ ε^{κ(w)} with ε infinitesimal;
    here we use the concrete parameterization exp(-κ(w)). -/
noncomputable def rankToPrior (κ : RankingFunction W) : W → ℝ :=
  fun w => exp (-(κ.rank w : ℝ))

/-- The exponential prior is always positive. -/
theorem rankToPrior_pos (κ : RankingFunction W) (w : W) :
    0 < rankToPrior κ w :=
  exp_pos _

/-- The exponential prior is non-negative. -/
theorem rankToPrior_nonneg (κ : RankingFunction W) (w : W) :
    0 ≤ rankToPrior κ w :=
  le_of_lt (rankToPrior_pos κ w)

/-- Rank-0 worlds maximize the exponential prior. -/
theorem rankToPrior_max_of_rank_zero (κ : RankingFunction W) (w₀ v : W)
    (h : κ.rank w₀ = 0) :
    rankToPrior κ v ≤ rankToPrior κ w₀ := by
  simp only [rankToPrior]
  apply exp_le_exp.mpr
  simp only [neg_le_neg_iff, Nat.cast_le]
  omega

/-- The exponential prior preserves the rank ordering:
    lower rank ↔ higher prior. -/
theorem rankToPrior_lt_iff (κ : RankingFunction W) (w v : W) :
    rankToPrior κ w < rankToPrior κ v ↔ κ.rank v < κ.rank w := by
  simp only [rankToPrior, exp_lt_exp, neg_lt_neg_iff, Nat.cast_lt]

-- ══════════════════════════════════════════════════════════════════════
-- § 5. Connection to RSA: Rankings as Limiting Priors
-- ══════════════════════════════════════════════════════════════════════

/-! An RSAConfig with `worldPrior = rankToPrior κ` and boolean meaning
    computes L1 posteriors that concentrate on the minimum-rank worlds
    in the support of the utterance as α → ∞.

    Specifically, for an utterance u with boolean denotation ⟦u⟧:
    - L1(w|u) ∝ rankToPrior(κ, w) · S1(u|w)
    - As α → ∞, S1 concentrates on the most informative true utterance
    - The prior rankToPrior(κ, ·) breaks ties among equally informative
      utterances in favor of lower-rank worlds
    - The net effect: L1 concentrates on minimum-rank ⟦u⟧-worlds

    This is exactly what `rankEntails κ ⟦u⟧ σ` characterizes: the
    most normal worlds satisfying the utterance also satisfy σ.

    The conditional limit theorem `condProb_tendsto_one` (§7)
    formalizes this precisely: P_α(σ|φ) → 1 as α → ∞ whenever
    κ ⊨ φ → σ. -/

/-- The softmax distribution with ranking scores is exactly the
    exponential prior (up to normalization).

    softmax(rankToScore κ, 1)(w) = exp(-κ(w)) / Σ_v exp(-κ(v))
                                 = rankToPrior(κ, w) / Σ_v rankToPrior(κ, v)

    At α = 1, softmax with ranking scores IS the normalized
    exponential prior. At other α, it's a tempered version:
    softmax(rankToScore κ, α)(w) = exp(-α·κ(w)) / Σ_v exp(-α·κ(v)). -/
theorem softmax_rankToScore_eq_normalized_prior [Fintype W] [Nonempty W]
    (κ : RankingFunction W) (w : W) :
    softmax (rankToScore κ) 1 w =
    rankToPrior κ w / ∑ v : W, rankToPrior κ v := by
  simp only [softmax, rankToScore, rankToPrior, one_mul]

-- ══════════════════════════════════════════════════════════════════════
-- § 6. The Exact Tropical Homomorphism (@cite{spohn-1988} §7)
-- ══════════════════════════════════════════════════════════════════════

/-! @cite{spohn-1988} §7 observes that ranking functions are the ordinal
    analogue of probability measures. This is not an analogy — it is an
    exact algebraic identity via the tropical semiring.

    The **tropical semiring** `Tropical ℕ` has:
    - Addition = min (the rank of a disjunction)
    - Multiplication = + (the rank of a conjunction under independence)

    The map ε^{·} (for 0 < ε < 1) is a homomorphism from the tropical
    semiring to (ℝ₊, max, ×):
    - ε^{a * b} = ε^{a + b} = ε^a · ε^b  (tropical × → real ×)
    - ε^{a + b} = ε^{min(a,b)} = max(ε^a, ε^b)  (tropical + → real max)

    The only "approximation" is that real addition (Σ) approximates max
    in the ε → 0 limit. This is the dequantization: as ε → 0 (α → ∞),
    the sum Σ_w ε^{κ(w)} is dominated by its largest term max_w ε^{κ(w)},
    and probabilistic inference degenerates to tropical (ranking) algebra. -/

open Tropical

/-- The exponential map sends tropical multiplication (= underlying +)
    to real multiplication: ε^{a ×_trop b} = ε^{a + b} = ε^a · ε^b.

    This is exact, not approximate. It formalizes @cite{spohn-1988} §7's
    observation that ranking independence (κ(A∩B) = κ(A) + κ(B))
    corresponds to probabilistic independence (P(A∩B) = P(A)·P(B)). -/
theorem exp_tropical_mul (ε : ℝ) (a b : Tropical ℕ) :
    ε ^ untrop (a * b) = ε ^ untrop a * ε ^ untrop b := by
  rw [untrop_mul, pow_add]

/-- The exponential map sends tropical addition (= min) to real max:
    ε^{a +_trop b} = ε^{min(a,b)} = max(ε^a, ε^b) for 0 < ε ≤ 1.

    This formalizes @cite{spohn-1988} §7's observation that ranking
    disjunction (κ(A∪B) = min(κ(A), κ(B))) corresponds to the dominant
    term in P(A∪B) = P(A) + P(B) − P(A∩B). -/
theorem exp_tropical_add (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (a b : Tropical ℕ) :
    ε ^ untrop (a + b) = max (ε ^ untrop a) (ε ^ untrop b) := by
  rw [untrop_add]
  rcases le_total (untrop a) (untrop b) with h | h
  · rw [min_eq_left h, max_eq_left (pow_le_pow_of_le_one hε.le hε1 h)]
  · rw [min_eq_right h, max_eq_right (pow_le_pow_of_le_one hε.le hε1 h)]

/-- Ranking independence is tropical multiplicativity.

    κ(φ ∧ ψ) = κ(φ) + κ(ψ)
    ↔ trop(κ(φ∧ψ)) = trop(κ(φ)) ×_trop trop(κ(ψ))

    This is not an analogy: "P(A∩B) = P(A)·P(B)" and "κ(A∩B) = κ(A)+κ(B)"
    are literally the same equation in two semirings. -/
theorem independent_iff_tropical_mul [Fintype W] (κ : RankingFunction W)
    (φ ψ : W → Prop) [DecidablePred φ] [DecidablePred ψ]
    [DecidablePred (fun w => φ w ∧ ψ w)]
    (hφ : ∃ w, φ w) (hψ : ∃ w, ψ w) (hφψ : ∃ w, φ w ∧ ψ w) :
    κ.independent φ ψ hφ hψ hφψ ↔
    trop (κ.rankProp (fun w => φ w ∧ ψ w) hφψ) =
    trop (κ.rankProp φ hφ) * trop (κ.rankProp ψ hψ) := by
  constructor
  · intro h; rw [h, trop_add]
  · intro h
    have := congr_arg untrop h
    rwa [untrop_mul, untrop_trop, untrop_trop, untrop_trop] at this

/-- The softmax distribution is the tropical-to-probabilistic functor
    applied to ranking values, with ε = exp(-α).

    softmax(-κ, α)(w) = exp(-α·κ(w)) / Σ_v exp(-α·κ(v))
                       = ε^{κ(w)} / Σ_v ε^{κ(v)}    where ε = exp(-α)

    As ε → 0 (α → ∞), the normalizing sum Σ_v ε^{κ(v)} is dominated
    by its largest term ε^{min_v κ(v)} = ε^0 = 1 (for rank-0 worlds).
    In this limit, the probabilistic sum degenerates to the tropical sum,
    and Bayesian inference becomes ranking-based reasoning. -/
theorem softmax_eq_tropical_ratio [Fintype W] [Nonempty W]
    (κ : RankingFunction W) (α : ℝ) (w : W) :
    softmax (rankToScore κ) α w =
    exp (-α) ^ κ.rank w / ∑ v : W, exp (-α) ^ κ.rank v := by
  simp only [softmax, rankToScore]
  have key : ∀ n : ℕ, exp (α * -(↑n : ℝ)) = exp (-α) ^ n := by
    intro n
    rw [show α * -(↑n : ℝ) = ↑n * (-α) from by ring, Real.exp_nat_mul]
  congr 1
  · exact key (κ.rank w)
  · exact Finset.sum_congr rfl fun v _ => key (κ.rank v)

-- ══════════════════════════════════════════════════════════════════════
-- § 7. Conditional Softmax Limit Theorem
-- ══════════════════════════════════════════════════════════════════════

/-! The conditional limit theorem: as α → ∞, the conditional probability
    P_α(σ|φ) → 1 whenever ranking entailment κ ⊨ φ → σ holds.

    This completes the RSA–ranking bridge:
    - §2 shows the *prior* concentrates on rank-0 worlds
    - §7 shows the *posterior* (conditioned on φ) concentrates on σ-worlds

    The proof uses exponential decay of non-minimal-rank worlds:
    under ranking entailment, every φ∧¬σ world has rank strictly above
    the minimum-rank φ∧σ world, so its softmax weight decays
    exponentially faster, driving P(σ|φ) → 1. -/

/-- rankEntails implies the existence of a φ∧σ witness. -/
theorem rankEntails_exists_sat [Fintype W]
    (κ : RankingFunction W) (φ σ : W → Bool)
    (h : rankEntails κ φ σ) (hφ : ∃ w, φ w = true) :
    ∃ w, (φ w && σ w) = true := by
  obtain ⟨w, hw⟩ := hφ
  cases hσ : σ w
  · have : (φ w && !σ w) = true := by simp [hw, hσ]
    obtain ⟨v, hv, _⟩ := h w this
    exact ⟨v, hv⟩
  · exact ⟨w, by simp [hw, hσ]⟩

/-- Conditional probability of σ given φ under scores s at rationality α.
    P_α(σ|φ) = Σ_{w: φ∧σ} exp(α·s(w)) / Σ_{w: φ} exp(α·s(w)) -/
noncomputable def condProb [Fintype W] (s : W → ℝ) (α : ℝ)
    (φ σ : W → Bool) : ℝ :=
  (∑ w ∈ univ.filter (fun w => (φ w && σ w) = true),
      exp (α * s w)) /
  (∑ w ∈ univ.filter (fun w => φ w = true),
      exp (α * s w))

/-- **Conditional Softmax Limit Theorem.** Under ranking entailment
    κ ⊨ φ → σ, the conditional probability P_α(σ|φ) converges to 1
    as α → ∞.

    This is the central theorem connecting RSA to default reasoning:
    an RSA listener with ranking-derived scores and infinite rationality
    draws exactly the conclusions that ranking entailment sanctions. -/
theorem condProb_tendsto_one [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) (φ σ : W → Bool)
    (h : rankEntails κ φ σ) (hφ : ∃ w, φ w = true) :
    Tendsto (fun α => condProb (rankToScore κ) α φ σ) atTop (nhds 1) := by
  have hφσ := rankEntails_exists_sat κ φ σ h hφ
  set s := rankToScore κ with hs_def
  set Sφ := univ.filter (fun w : W => φ w = true)
  set Sφσ := univ.filter (fun w : W => (φ w && σ w) = true)
  have hsub : Sφσ ⊆ Sφ := by
    intro w; simp only [Sφσ, Sφ, mem_filter, mem_univ, true_and, Bool.and_eq_true]
    exact And.left
  have hD_pos : ∀ α, 0 < ∑ w ∈ Sφ, exp (α * s w) := by
    intro α; obtain ⟨w, hw⟩ := hφ
    exact Finset.sum_pos (fun v _ => exp_pos _) ⟨w, mem_filter.mpr ⟨mem_univ w, hw⟩⟩
  by_cases hall : ∀ w, φ w = true → σ w = true
  · -- Trivial: Sφσ = Sφ, condProb ≡ 1
    have hsets : Sφσ = Sφ := by
      ext w; simp only [Sφσ, Sφ, mem_filter, mem_univ, true_and, Bool.and_eq_true]
      exact ⟨And.left, fun h1 => ⟨h1, hall w h1⟩⟩
    suffices heq : ∀ α, condProb s α φ σ = 1 from by
      simp_rw [heq]; exact tendsto_const_nhds
    intro α
    show (∑ w ∈ Sφσ, exp (α * s w)) / (∑ w ∈ Sφ, exp (α * s w)) = 1
    rw [hsets]; exact div_self (ne_of_gt (hD_pos α))
  · -- Non-trivial: exponential decay of rejection mass
    push_neg at hall
    set m := minRankBool κ (fun v => φ v && σ v) hφσ
    have hSφσ_ne : Sφσ.Nonempty := by
      obtain ⟨w, hw⟩ := hφσ; exact ⟨w, mem_filter.mpr ⟨mem_univ w, hw⟩⟩
    obtain ⟨w₀, hw₀_mem, hw₀_eq⟩ := Finset.exists_mem_eq_inf' hSφσ_ne κ.rank
    have hw₀_φ : w₀ ∈ Sφ := hsub hw₀_mem
    have hgap : ∀ w, (φ w && !σ w) = true → m < κ.rank w :=
      (rankEntails_iff_minRank_lt κ φ σ hφσ).mp h
    have hmem_sdiff : ∀ w ∈ Sφ \ Sφσ, (φ w && !σ w) = true := by
      intro w hw
      rw [Finset.mem_sdiff] at hw
      have hφw : φ w = true := by
        simp only [Sφ, mem_filter, mem_univ, true_and] at hw; exact hw.1
      have hnotσ : σ w ≠ true := by
        simp only [Sφσ, mem_filter, mem_univ, true_and, Bool.and_eq_true] at hw
        intro hσ; exact hw.2 ⟨hφw, hσ⟩
      cases hσ : σ w
      · simp [hφw]
      · exact absurd hσ hnotσ
    set R := fun α => ∑ w ∈ Sφ \ Sφσ, exp (α * s w)
    set D := fun α => ∑ w ∈ Sφ, exp (α * s w)
    have hdecomp : ∀ α, R α + (∑ w ∈ Sφσ, exp (α * s w)) = D α := by
      intro α; exact Finset.sum_sdiff hsub
    have hcond_eq : ∀ α, condProb s α φ σ = 1 - R α / D α := by
      intro α
      have hD_ne : D α ≠ 0 := ne_of_gt (hD_pos α)
      show (∑ w ∈ Sφσ, exp (α * s w)) / D α = 1 - R α / D α
      rw [show (∑ w ∈ Sφσ, exp (α * s w)) = D α - R α from by linarith [hdecomp α]]
      rw [sub_div, div_self hD_ne]
    have hw₀_rank : κ.rank w₀ = m := hw₀_eq.symm
    have hscore_w₀ : s w₀ = -(↑m : ℝ) := by
      simp only [hs_def, rankToScore, hw₀_rank]
    have hscore_bad : ∀ w ∈ Sφ \ Sφσ, s w ≤ -(↑(m + 1) : ℝ) := by
      intro w hw
      simp only [hs_def, rankToScore, neg_le_neg_iff, Nat.cast_le]
      exact hgap w (hmem_sdiff w hw)
    set C := (Fintype.card W : ℝ)
    have hbound : ∀ α, 0 ≤ α → R α / D α ≤ C * exp (-α) := by
      intro α hα
      have hR_bound : R α ≤ C * exp (α * -(↑(m + 1) : ℝ)) := by
        calc R α ≤ ∑ _ ∈ Sφ \ Sφσ, exp (α * -(↑(m + 1) : ℝ)) := by
              apply Finset.sum_le_sum; intro w hw
              exact exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hscore_bad w hw) hα)
          _ = ↑(Sφ \ Sφσ).card * exp (α * -(↑(m + 1) : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ C * exp (α * -(↑(m + 1) : ℝ)) := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt (exp_pos _))
              exact Nat.cast_le.mpr (Finset.card_le_univ _)
      have hD_lower : exp (α * -(↑m : ℝ)) ≤ D α := by
        have h1 : exp (α * s w₀) ≤ ∑ w ∈ Sφ, exp (α * s w) :=
          Finset.single_le_sum (f := fun w => exp (α * s w))
            (fun w _ => le_of_lt (exp_pos _)) hw₀_φ
        linarith [show exp (α * -(↑m : ℝ)) = exp (α * s w₀) from by rw [hscore_w₀]]
      have hexp_pos : (0 : ℝ) < exp (α * -(↑m : ℝ)) := exp_pos _
      calc R α / D α
          ≤ R α / exp (α * -(↑m : ℝ)) := by
            apply div_le_div_of_nonneg_left
              (Finset.sum_nonneg fun w _ => le_of_lt (exp_pos _))
              hexp_pos hD_lower
        _ ≤ (C * exp (α * -(↑(m + 1) : ℝ))) / exp (α * -(↑m : ℝ)) := by
            apply div_le_div_of_nonneg_right hR_bound (le_of_lt hexp_pos)
        _ = C * (exp (α * -(↑(m + 1) : ℝ)) / exp (α * -(↑m : ℝ))) := by
            rw [mul_div_assoc]
        _ = C * exp (α * -(↑(m + 1) : ℝ) - α * -(↑m : ℝ)) := by
            rw [← Real.exp_sub]
        _ = C * exp (-α) := by
            congr 1; push_cast; ring
    have hR_nonneg : ∀ α, 0 ≤ R α / D α :=
      fun α => div_nonneg
        (Finset.sum_nonneg fun w _ => le_of_lt (exp_pos _))
        (le_of_lt (hD_pos α))
    have hexp_zero : Tendsto (fun α => C * exp (-α)) atTop (nhds 0) := by
      rw [show (0 : ℝ) = C * 0 from by ring]
      exact tendsto_const_nhds.mul
        (tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
    have hRD_zero : Tendsto (fun α => R α / D α) atTop (nhds 0) :=
      squeeze_zero' (Eventually.of_forall hR_nonneg)
        (eventually_atTop.mpr ⟨0, fun α hα => hbound α hα⟩)
        hexp_zero
    simp_rw [hcond_eq]
    have : Tendsto (fun α => 1 - R α / D α) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hRD_zero
    simp only [sub_zero] at this
    exact this

end Theories.Pragmatics.RSA.RankingBridge
