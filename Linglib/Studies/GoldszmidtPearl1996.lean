import Linglib.Core.Logic.SystemZ
import Linglib.Core.Logic.TweetyNixon
import Linglib.Core.Probability.SoftmaxLimits
import Linglib.Studies.Veltman1996
import Mathlib.Algebra.Tropical.BigOperators

/-!
# Goldszmidt & Pearl (1996): Qualitative Probabilities for Default Reasoning

[goldszmidt-pearl-1996]

This study demonstrates System Z — the constructive derivation of
minimal ranking functions from a knowledge base of default rules.
Where [spohn-1988] defines ranking functions as primitive objects,
G&P show how to *compute* the unique minimal admissible ranking κ^z
from a set of defaults, using tolerance-based stratification.

## Key demonstrations

1. **Tolerance stratification**: Rules are partitioned by iteratively
   peeling off tolerated rules (Consistency-Test, Fig. 2). In the
   3-rule subset of the Tweety scenario (r₁–r₃ from Example 17),
   "birds fly" is tolerated first (Z = 0), while "penguins are birds"
   and "penguins don't fly" are tolerated only after removing the
   first stratum (Z = 1).

2. **κ^z ranking** (Definition 12): The minimal admissible ranking
   assigns each world the lowest possible rank. Worlds verifying all
   rules get rank 0; worlds falsifying only low-priority rules get
   low ranks.

3. **Specificity**: More specific defaults automatically override
   general ones — penguinNoFly outranks penguinFlies because the
   penguin-specific rule has higher Z-priority.

4. **Bridge to Veltman**: The κ^z ranking derives the same specificity
   result that [veltman-1996] obtains by stipulating orderings.
   We prove the agreement directly.

## Ranking Functions as RSA Limits

As the rationality parameter α → ∞, softmax-based probabilistic
inference converges to ranking-based default reasoning
([spohn-1988], [frank-goodman-2012]). We formalize the substrate
of this connection (`rankToScore`, `softmax_concentrates_unique`,
`condProb_tendsto_one`) and apply it to the Tweety scenario:
RSA with infinite rationality assigns probability 1 to the most
normal worlds under κ^z.

## Scenario

We formalize rules r₁–r₃ from Example 17 (the paper's full example
has 5 rules including r₄: b→w and r₅: f→a, which would require
extending TweetyWorld with wings/airborne features). The 3-rule
subset is sufficient to demonstrate tolerance stratification, κ^z
construction, admissibility, and specificity.
-/

namespace GoldszmidtPearl1996

open Core.Logic.SystemZ Core.Logic.Ranking Core.Logic.TweetyNixon
open Core Real Finset Filter Topology Tropical BigOperators

/-! ### Knowledge Base (rules r₁–r₃ from Example 17) -/

/-- r₁: "Birds fly" (b → f). -/
def r₁ : DefaultRule TweetyWorld := ⟨isBird, flies⟩

/-- r₂: "Penguins are birds" (p → b). Strict: no world falsifies it
    in TweetyWorld since all penguins are birds by construction. -/
def r₂ : DefaultRule TweetyWorld := ⟨isPenguin, isBird⟩

/-- r₃: "Penguins don't fly" (p → ¬f). -/
def r₃ : DefaultRule TweetyWorld := ⟨isPenguin, fun w => ¬ flies w⟩

/-- The penguin-bird knowledge base Δ_pb (rules r₁–r₃). -/
def Δ_pb : KnowledgeBase TweetyWorld := [r₁, r₂, r₃]

/-! ### Tolerance and Z-Ordering (Consistency-Test, Fig. 2)

Stratum 0: r₁ is tolerated by Δ_pb (birdFlies verifies r₁ and all
material counterparts). r₂ and r₃ are not tolerated (no world
satisfies their antecedent + consequent while also satisfying
b → f as a material conditional).

Stratum 1: After removing r₁, both r₂ and r₃ are tolerated
(penguinNoFly verifies both and satisfies the remaining material
counterparts).

Z-priorities: Z(r₁) = 0, Z(r₂) = 1, Z(r₃) = 1. -/

theorem r₁_tolerated_by_Δ : tolerated r₁ Δ_pb := by
  refine ⟨.birdFlies, trivial, trivial, ?_⟩
  decide

theorem r₂_not_tolerated_by_Δ : ¬tolerated r₂ Δ_pb := by
  intro ⟨w, ha, hc, hall⟩; cases w <;> simp_all [r₂, isPenguin, isBird, Δ_pb,
    r₁, r₂, r₃, DefaultRule.verified, flies]

theorem r₃_not_tolerated_by_Δ : ¬tolerated r₃ Δ_pb := by
  intro ⟨w, ha, hc, hall⟩; cases w <;> simp_all [r₃, isPenguin, flies, Δ_pb,
    r₁, r₂, r₃, DefaultRule.verified, isBird]

/-- After removing stratum 0 (r₁), both r₂ and r₃ are tolerated. -/
def Δ₁ : KnowledgeBase TweetyWorld := [r₂, r₃]

theorem r₂_tolerated_by_Δ₁ : tolerated r₂ Δ₁ := by
  refine ⟨.penguinNoFly, trivial, trivial, ?_⟩
  decide

theorem r₃_tolerated_by_Δ₁ : tolerated r₃ Δ₁ := by
  refine ⟨.penguinNoFly, trivial, ?_, ?_⟩
  · decide
  · decide

/-! ### Minimal Ranking κ^z (Definition 12) -/

/-- Z-prioritized rules: Z(r₁) = 0, Z(r₂) = 1, Z(r₃) = 1. -/
def prioritized : List (DefaultRule TweetyWorld × ℕ) :=
  [(r₁, 0), (r₂, 1), (r₃, 1)]

/-- The minimal ranking κ^z for the Tweety knowledge base.

    κ^z values (Definition 12):
    - birdFlies:    falsifies nothing → 0
    - birdNoFly:    falsifies r₁ (Z=0) → max(0)+1 = 1
    - penguinFlies: falsifies r₃ (Z=1) → max(1)+1 = 2
    - penguinNoFly: falsifies r₁ (Z=0) → max(0)+1 = 1 -/
def κ_z : RankingFunction TweetyWorld :=
  zRanking prioritized ⟨.birdFlies, by decide⟩

-- Verify rank values
theorem κz_birdFlies : κ_z.rank .birdFlies = 0 := by decide
theorem κz_birdNoFly : κ_z.rank .birdNoFly = 1 := by decide
theorem κz_penguinFlies : κ_z.rank .penguinFlies = 2 := by decide
theorem κz_penguinNoFly : κ_z.rank .penguinNoFly = 1 := by decide

/-! ### Admissibility Verification (Definition 2) -/

/-- r₁ (b → f) is admissible: every world falsifying it (birdNoFly,
    penguinNoFly, both rank 1) is outranked by birdFlies (rank 0). -/
theorem r₁_admissible : ∀ w : TweetyWorld, r₁.falsified w →
    ∃ v, r₁.ante v ∧ r₁.cons v ∧ κ_z.rank v < κ_z.rank w := by
  intro w hw
  cases w <;> simp_all [r₁, DefaultRule.falsified, isBird, flies]
  all_goals exact ⟨.birdFlies, trivial, trivial, by decide⟩

/-- r₂ (p → b) is vacuously admissible: no world falsifies it. -/
theorem r₂_admissible : ∀ w : TweetyWorld, r₂.falsified w →
    ∃ v, r₂.ante v ∧ r₂.cons v ∧ κ_z.rank v < κ_z.rank w := by
  intro w hw
  cases w <;> simp_all [r₂, DefaultRule.falsified, isPenguin, isBird]

/-- r₃ (p → ¬f) is admissible: the only falsifying world is
    penguinFlies (rank 2), outranked by penguinNoFly (rank 1). -/
theorem r₃_admissible : ∀ w : TweetyWorld, r₃.falsified w →
    ∃ v, r₃.ante v ∧ r₃.cons v ∧ κ_z.rank v < κ_z.rank w := by
  intro w hw
  cases w <;> simp_all [r₃, DefaultRule.falsified, isPenguin, flies]
  exact ⟨.penguinNoFly, trivial, by decide, by decide⟩

/-- κ^z is admissible relative to the full knowledge base Δ_pb
    (Definition 2). -/
theorem κz_admissible : admissible κ_z Δ_pb := by
  intro r hr
  simp [Δ_pb] at hr
  rcases hr with rfl | rfl | rfl
  · exact r₁_admissible
  · exact r₂_admissible
  · exact r₃_admissible

/-! ### Entailment Queries

z-entailment queries on Δ_pb. These cover two of the five queries
in Table 2 (the remaining three — red birds fly, birds airborne,
penguins winged — require r₄/r₅ and a richer world type). -/

/-- "Do penguin-birds fly?" → NO (z-entailment). penguinNoFly (rank 1)
    outranks penguinFlies (rank 2). The more specific default wins. -/
theorem penguin_birds_dont_fly :
    rankEntails κ_z (fun w => isPenguin w ∧ isBird w)
                     (fun w => ¬ flies w) := by
  intro w hw hσ
  cases w <;> simp_all [isPenguin, isBird, flies]
  exact ⟨.penguinNoFly, ⟨trivial, trivial⟩, by decide, by decide⟩

/-- "Are birds typically penguins?" → NO (z-entailment). birdFlies
    (rank 0) is a non-penguin bird, outranking all penguin worlds. -/
theorem birds_not_typically_penguins :
    ¬rankEntails κ_z isBird isPenguin := by
  intro h
  have := h .birdFlies trivial (by decide)
  obtain ⟨v, _, hpv, hlt⟩ := this
  cases v <;> simp_all [isPenguin, isBird] <;>
    simp [κ_z, zRanking, zRankValue, zRankValue.maxFalsifiedPriority,
      prioritized, r₁, r₂, r₃, DefaultRule.falsified, isBird, flies, isPenguin] at hlt

/-- "Do birds fly?" → YES (z-entailment). birdFlies (rank 0) is the
    most normal bird world and it flies. -/
theorem birds_fly :
    rankEntails κ_z isBird flies := by
  intro w hw hσ
  cases w <;> simp_all [isBird, flies]
  all_goals exact ⟨.birdFlies, trivial, trivial, by decide⟩

/-! ### Specificity: κ^z Derives What Veltman Stipulates -/

/-- The κ^z ranking makes penguinNoFly strictly more plausible than
    penguinFlies. -/
theorem specificity_penguinNoFly_beats_penguinFlies :
    κ_z.rank .penguinNoFly < κ_z.rank .penguinFlies := by decide

/-- The κ^z ranking preserves the general default: among non-penguin
    birds, flying is more normal than not flying. -/
theorem general_default_preserved :
    κ_z.rank .birdFlies < κ_z.rank .birdNoFly := by decide

/-- The induced plausibility ordering is connected (total), so
    Rational Monotonicity holds. -/
theorem κz_connected :
    Core.Order.Normality.connected κ_z.toPlausibilityOrder.toPreorder :=
  κ_z.ranking_connected

/-! ### Bridge to Veltman 1996

[veltman-1996] manually stipulates subdomain orderings to
resolve the Tweety Triangle: `birdOrd` promotes flying,
`penguinOrd` promotes not-flying. The key result is
`penguinFlies_not_normal_in_birds` — penguinFlies fails the
normality test because the penguin subdomain ordering demotes it.

G&P's System Z *derives* the same specificity result from the
rules alone, without any stipulated orderings. The following
theorem makes this derivation-vs-stipulation relationship explicit
by combining both papers' conclusions. -/

open Veltman1996 in

/-- What [veltman-1996] stipulates about penguin normality,
    [goldszmidt-pearl-1996]'s System Z derives:
    - Veltman: penguinFlies is not normal among birds (via stipulated
      penguin subdomain ordering)
    - G&P: penguinFlies has strictly higher κ^z rank than birdFlies
      (derived from tolerance stratification alone)
    Both reach the same conclusion: flying penguins are less normal
    than non-flying penguins in a bird context. -/
theorem gp_derives_veltman_specificity :
    TweetyWorld.penguinFlies ∉ tweetyFrame.normal birdDomain ∧
    κ_z.rank .penguinFlies > κ_z.rank .birdFlies :=
  ⟨penguinFlies_not_normal_in_birds, by decide⟩

/-! ### RSA Bridge Substrate: Rankings as Softmax Limits

[spohn-1988] §7 observes that rankings are ordinal probabilities:
κ(w) = n corresponds to P(w) ∝ ε^n for infinitesimal ε. The finite
analogue replaces ε^n with exp(-n·α) for large α:

    softmax(-κ, α)(w) = exp(-α · κ(w)) / Σ_v exp(-α · κ(v))

As α → ∞, this concentrates on rank-0 (most normal) worlds — exactly
the worlds that survive ranking-based default reasoning. This makes
System Z's κ^z the "infinite rationality" limit of RSA pragmatic
inference ([frank-goodman-2012]). Qualitative default reasoning and
quantitative Bayesian pragmatics are not rival frameworks but
endpoints of the same rationality continuum. -/

section RankingLimits

variable {W : Type*}

/-! #### Ranking Functions as Score Functions -/

/-- Convert a ranking function to softmax scores.

    s(w) = -(κ(w) : ℝ). Lower rank → higher score → more plausible.

    This is the finite analogue of [spohn-1988] §7's
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

/-! #### Softmax Concentration on Normal Worlds -/

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
    Tendsto (fun (α : ℝ) => softmax (α • rankToScore κ) w) atTop
      (𝓝 (if w = w₀ then 1 else 0)) :=
  Softmax.tendsto_softmax_infty_unique_max (rankToScore κ) w₀
    (fun j hj => (rankToScore_lt_iff κ j w₀).mpr (h_zero ▸ h_unique j hj)) w

/-- Entropy of softmax(rankToScore κ, α) → 0 as α → ∞ (unique rank-0
    case). The distribution becomes maximally concentrated. -/
theorem entropy_vanishes_unique [Fintype W] [DecidableEq W] [Nonempty W]
    (κ : RankingFunction W) (w₀ : W)
    (h_zero : κ.rank w₀ = 0)
    (h_unique : ∀ v, v ≠ w₀ → 0 < κ.rank v) :
    Tendsto (fun (α : ℝ) => Softmax.entropy (softmax (α • rankToScore κ))) atTop
      (𝓝 0) :=
  Softmax.entropy_tendsto_zero (rankToScore κ) w₀
    (fun j hj => (rankToScore_lt_iff κ j w₀).mpr (h_zero ▸ h_unique j hj))

/-! #### Ranking Entailment via Minimum Rank -/

/-- rankEntails is equivalent to: every φ∧¬σ world has strictly
    higher rank than some φ∧σ world.

    When φ∧σ is non-empty, this is the same as: the minimum rank
    among φ∧σ worlds is strictly less than the rank of every
    φ∧¬σ world. When φ∧¬σ is empty, rankEntails holds vacuously. -/
theorem rankEntails_iff_minRank_lt [Fintype W]
    (κ : RankingFunction W) (φ σ : W → Prop)
    [DecidablePred φ] [DecidablePred σ]
    [DecidablePred (fun w => φ w ∧ σ w)]
    (hφσ : ∃ w, φ w ∧ σ w) :
    rankEntails κ φ σ ↔
    ∀ w, φ w → ¬ σ w →
      κ.rankProp (fun v => φ v ∧ σ v) hφσ < κ.rank w := by
  constructor
  · intro h w hφw hσw
    obtain ⟨v, hφv, hσv, hlt⟩ := h w hφw hσw
    exact lt_of_le_of_lt
      (Finset.inf'_le κ.rank (mem_filter.mpr ⟨mem_univ v, ⟨hφv, hσv⟩⟩))
      hlt
  · intro h w hφw hσw
    have hmin := h w hφw hσw
    have hne : (univ.filter (fun w => φ w ∧ σ w)).Nonempty := by
      obtain ⟨w, hw⟩ := hφσ; exact ⟨w, mem_filter.mpr ⟨mem_univ w, hw⟩⟩
    obtain ⟨v, hv_mem, hv_eq⟩ := Finset.exists_mem_eq_inf' hne κ.rank
    have ⟨hφv, hσv⟩ := (mem_filter.mp hv_mem).2
    exact ⟨v, hφv, hσv, hv_eq ▸ hmin⟩

/-- Under ranking entailment, all minimum-rank φ-worlds satisfy σ.

    This is the key lemma connecting ranking entailment to softmax
    concentration: as α → ∞, softmax concentrates on minimum-rank
    worlds. If all minimum-rank φ-worlds satisfy σ, then the
    limiting conditional probability P(σ|φ) = 1.

    Proof: If a minimum-rank φ-world w fails σ, then rankEntails
    gives a φ∧σ world v with κ(v) < κ(w), contradicting w having
    the minimum rank among φ-worlds. -/
theorem minRank_worlds_satisfy [Fintype W]
    (κ : RankingFunction W) (φ σ : W → Prop)
    [DecidablePred φ] [DecidablePred σ]
    (h : rankEntails κ φ σ) (hφ : ∃ w, φ w) :
    ∀ w, φ w → κ.rank w = κ.rankProp φ hφ → σ w := by
  intro w hφw hmin
  by_contra hσ
  obtain ⟨v, hφv, _, hlt⟩ := h w hφw hσ
  have hle : κ.rankProp φ hφ ≤ κ.rank v :=
    Finset.inf'_le κ.rank (mem_filter.mpr ⟨mem_univ v, hφv⟩)
  omega

/-! #### The Rationality Continuum

The theorems above establish the formal bridge between RSA and
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

    [spohn-1988] §7 uses P(w) ∝ ε^{κ(w)} with ε infinitesimal;
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

/-! #### Rankings as Limiting Priors

An RSA chain with world prior `rankToPrior κ` and boolean meaning
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

The conditional limit theorem `condProb_tendsto_one` below
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
    softmax (rankToScore κ) w =
    rankToPrior κ w / ∑ v : W, rankToPrior κ v := by
  simp only [softmax, rankToScore, rankToPrior]

/-! #### The Exact Tropical Homomorphism ([spohn-1988] §7)

[spohn-1988] §7 observes that ranking functions are the ordinal
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

/-- The exponential map sends tropical multiplication (= underlying +)
    to real multiplication: ε^{a ×_trop b} = ε^{a + b} = ε^a · ε^b.

    This is exact, not approximate. It formalizes [spohn-1988] §7's
    observation that ranking independence (κ(A∩B) = κ(A) + κ(B))
    corresponds to probabilistic independence (P(A∩B) = P(A)·P(B)). -/
theorem exp_tropical_mul (ε : ℝ) (a b : Tropical ℕ) :
    ε ^ untrop (a * b) = ε ^ untrop a * ε ^ untrop b := by
  rw [untrop_mul, pow_add]

/-- The exponential map sends tropical addition (= min) to real max:
    ε^{a +_trop b} = ε^{min(a,b)} = max(ε^a, ε^b) for 0 < ε ≤ 1.

    This formalizes [spohn-1988] §7's observation that ranking
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
    softmax (α • rankToScore κ) w =
    exp (-α) ^ κ.rank w / ∑ v : W, exp (-α) ^ κ.rank v := by
  simp only [softmax, rankToScore, Pi.smul_apply, smul_eq_mul]
  have key : ∀ n : ℕ, exp (α * -(↑n : ℝ)) = exp (-α) ^ n := by
    intro n
    rw [show α * -(↑n : ℝ) = ↑n * (-α) from by ring, Real.exp_nat_mul]
  congr 1
  · exact key (κ.rank w)
  · exact Finset.sum_congr rfl fun v _ => key (κ.rank v)

/-! #### Conditional Softmax Limit Theorem

The conditional limit theorem: as α → ∞, the conditional probability
P_α(σ|φ) → 1 whenever ranking entailment κ ⊨ φ → σ holds.

This completes the RSA–ranking bridge:
- Softmax concentration shows the *prior* concentrates on rank-0 worlds
- The conditional limit shows the *posterior* (conditioned on φ)
  concentrates on σ-worlds

The proof uses exponential decay of non-minimal-rank worlds:
under ranking entailment, every φ∧¬σ world has rank strictly above
the minimum-rank φ∧σ world, so its softmax weight decays
exponentially faster, driving P(σ|φ) → 1. -/

/-- rankEntails implies the existence of a φ∧σ witness. -/
theorem rankEntails_exists_sat [Fintype W]
    (κ : RankingFunction W) (φ σ : W → Prop)
    [DecidablePred φ] [DecidablePred σ]
    (h : rankEntails κ φ σ) (hφ : ∃ w, φ w) :
    ∃ w, φ w ∧ σ w := by
  obtain ⟨w, hw⟩ := hφ
  by_cases hσ : σ w
  · exact ⟨w, hw, hσ⟩
  · obtain ⟨v, hφv, hσv, _⟩ := h w hw hσ
    exact ⟨v, hφv, hσv⟩

/-- Conditional probability of σ given φ under scores s at rationality α.
    P_α(σ|φ) = Σ_{w: φ∧σ} exp(α·s(w)) / Σ_{w: φ} exp(α·s(w)) -/
noncomputable def condProb [Fintype W] (s : W → ℝ) (α : ℝ)
    (φ σ : W → Prop) [DecidablePred φ] [DecidablePred σ]
    [DecidablePred (fun w => φ w ∧ σ w)] : ℝ :=
  (∑ w ∈ univ.filter (fun w => φ w ∧ σ w),
      exp (α * s w)) /
  (∑ w ∈ univ.filter (fun w => φ w),
      exp (α * s w))

/-- **Conditional Softmax Limit Theorem.** Under ranking entailment
    κ ⊨ φ → σ, the conditional probability P_α(σ|φ) converges to 1
    as α → ∞.

    This is the central theorem connecting RSA to default reasoning:
    an RSA listener with ranking-derived scores and infinite rationality
    draws exactly the conclusions that ranking entailment sanctions. -/
theorem condProb_tendsto_one [Fintype W] [DecidableEq W]
    (κ : RankingFunction W) (φ σ : W → Prop)
    [DecidablePred φ] [DecidablePred σ]
    (h : rankEntails κ φ σ) (hφ : ∃ w, φ w) :
    Tendsto (fun α => condProb (rankToScore κ) α φ σ) atTop (nhds 1) := by
  have hφσ := rankEntails_exists_sat κ φ σ h hφ
  set s := rankToScore κ with hs_def
  set Sφ := univ.filter (fun w : W => φ w)
  set Sφσ := univ.filter (fun w : W => φ w ∧ σ w)
  have hsub : Sφσ ⊆ Sφ := by
    intro w; simp only [Sφσ, Sφ, mem_filter, mem_univ, true_and]
    exact And.left
  have hD_pos : ∀ α, 0 < ∑ w ∈ Sφ, exp (α * s w) := by
    intro α; obtain ⟨w, hw⟩ := hφ
    exact Finset.sum_pos (fun v _ => exp_pos _) ⟨w, mem_filter.mpr ⟨mem_univ w, hw⟩⟩
  by_cases hall : ∀ w, φ w → σ w
  · -- Trivial: Sφσ = Sφ, condProb ≡ 1
    have hsets : Sφσ = Sφ := by
      ext w; simp only [Sφσ, Sφ, mem_filter, mem_univ, true_and]
      exact ⟨And.left, fun h1 => ⟨h1, hall w h1⟩⟩
    suffices heq : ∀ α, condProb s α φ σ = 1 from by
      simp_rw [heq]; exact tendsto_const_nhds
    intro α
    show (∑ w ∈ Sφσ, exp (α * s w)) / (∑ w ∈ Sφ, exp (α * s w)) = 1
    rw [hsets]; exact div_self (ne_of_gt (hD_pos α))
  · -- Non-trivial: exponential decay of rejection mass
    push Not at hall
    set m := κ.rankProp (fun v => φ v ∧ σ v) hφσ
    have hSφσ_ne : Sφσ.Nonempty := by
      obtain ⟨w, hw⟩ := hφσ; exact ⟨w, mem_filter.mpr ⟨mem_univ w, hw⟩⟩
    obtain ⟨w₀, hw₀_mem, hw₀_eq⟩ := Finset.exists_mem_eq_inf' hSφσ_ne κ.rank
    have hw₀_φ : w₀ ∈ Sφ := hsub hw₀_mem
    have hgap : ∀ w, φ w → ¬ σ w → m < κ.rank w :=
      (rankEntails_iff_minRank_lt κ φ σ hφσ).mp h
    have hmem_sdiff : ∀ w ∈ Sφ \ Sφσ, φ w ∧ ¬ σ w := by
      intro w hw
      rw [Finset.mem_sdiff] at hw
      have hφw : φ w := by
        simp only [Sφ, mem_filter, mem_univ, true_and] at hw; exact hw.1
      have hnotσ : ¬ σ w := by
        simp only [Sφσ, mem_filter, mem_univ, true_and] at hw
        intro hσ; exact hw.2 ⟨hφw, hσ⟩
      exact ⟨hφw, hnotσ⟩
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
      have ⟨hφw, hnotσ⟩ := hmem_sdiff w hw
      exact hgap w hφw hnotσ
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
            congr 1; push_cast; ring_nf
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

end RankingLimits

/-! ### Bridge to RSA: κ^z as Infinite-Rationality Limit

[frank-goodman-2012]'s RSA framework uses softmax-based
Bayesian inference with a finite rationality parameter α.
[goldszmidt-pearl-1996]'s System Z uses ranking functions
for qualitative default reasoning.

The two frameworks are endpoints of the same continuum: as
α → ∞, softmax concentrates on the most normal (rank-0) worlds,
recovering ranking-based entailment from probabilistic inference.

We demonstrate this concretely: the softmax distribution with
scores derived from κ^z concentrates on birdFlies (the unique
rank-0 world) as α → ∞. This means RSA's pragmatic listener
with infinite rationality reasons exactly like System Z. -/

instance : Nonempty TweetyWorld := ⟨.birdFlies⟩

/-- birdFlies is the unique rank-0 world under κ^z. -/
theorem κz_unique_rank_zero :
    ∀ v : TweetyWorld, v ≠ .birdFlies → 0 < κ_z.rank v := by
  intro v hv; cases v <;> simp_all <;> decide

/-- The softmax distribution softmax(-κ^z, α) concentrates on
    birdFlies as α → ∞. This is the core RSA–ranking bridge for
    the Tweety scenario: an RSA listener with infinite rationality
    assigns probability 1 to the most normal world. -/
theorem κz_softmax_concentrates :
    ∀ w, Tendsto (fun (α : ℝ) => Core.softmax (α • rankToScore κ_z) w)
      atTop (nhds (if w = .birdFlies then 1 else 0)) :=
  softmax_concentrates_unique κ_z .birdFlies κz_birdFlies κz_unique_rank_zero

/-- Under κ^z, all minimum-rank bird-worlds fly. This connects
    the ranking entailment `birds_fly` to the softmax limit:
    as α → ∞, the softmax listener restricted to bird-worlds
    assigns all probability to flying worlds. -/
theorem minRank_birds_fly :
    ∀ w : TweetyWorld, isBird w →
      κ_z.rank w = κ_z.rankProp isBird ⟨.birdFlies, trivial⟩ →
      flies w :=
  minRank_worlds_satisfy κ_z isBird flies birds_fly ⟨.birdFlies, trivial⟩

/-- Under κ^z, all minimum-rank penguin-worlds don't fly. The
    specificity result — penguins override the general bird default —
    is precisely the α → ∞ limit of RSA inference restricted to
    the penguin domain. -/
theorem minRank_penguins_dont_fly :
    ∀ w : TweetyWorld, (isPenguin w ∧ isBird w) →
      κ_z.rank w = κ_z.rankProp
        (fun w => isPenguin w ∧ isBird w) ⟨.penguinNoFly, trivial, trivial⟩ →
      ¬ flies w :=
  minRank_worlds_satisfy κ_z
    (fun w => isPenguin w ∧ isBird w)
    (fun w => ¬ flies w)
    penguin_birds_dont_fly
    ⟨.penguinNoFly, trivial, trivial⟩

/-- **Conditional limit: "Do birds fly?" → probability 1.**
    As α → ∞, the conditional probability P_α(flies|bird) → 1
    under κ^z scores. This is the full conditional softmax limit
    theorem applied to the Tweety scenario. -/
theorem condProb_birds_fly :
    Tendsto
      (fun α => condProb (rankToScore κ_z) α isBird flies)
      atTop (nhds 1) :=
  condProb_tendsto_one κ_z isBird flies birds_fly ⟨.birdFlies, trivial⟩

/-- **Conditional limit: "Do penguin-birds fly?" → probability 0.**
    As α → ∞, the conditional probability P_α(flies|penguin∧bird) → 0,
    because ranking entailment says penguin-birds *don't* fly.
    We prove this by showing P_α(¬flies|penguin∧bird) → 1. -/
theorem condProb_penguins_dont_fly :
    Tendsto
      (fun α => condProb (rankToScore κ_z) α
        (fun w => isPenguin w ∧ isBird w) (fun w => ¬ flies w))
      atTop (nhds 1) :=
  condProb_tendsto_one κ_z
    (fun w => isPenguin w ∧ isBird w) (fun w => ¬ flies w)
    penguin_birds_dont_fly ⟨.penguinNoFly, trivial, trivial⟩

/-! ### Computed Consistency-Test -/

/-- The Consistency-Test (Fig. 2) computes the same Z-priorities as
    our manually-verified `prioritized` list: Z(r₁)=0, Z(r₂)=1, Z(r₃)=1. -/
theorem Δ_pb_computed :
    (zPriorities Δ_pb).map Prod.snd = [0, 1, 1] := by decide

/-! ### System Z⁺: Variable-Strength Defaults (Definition 18)

System Z⁺ augments each rule with a strength parameter δ, requiring
a wider gap between verifying and falsifying worlds. The Z⁺-priority
of a rule accounts for δ, giving stronger rules higher priority and
thus wider separation in the ranking. -/

/-- Strength-augmented rules: δ₁=1, δ₂=1, δ₃=2.
    "Penguins don't fly" (r₃) is strongest. -/
def sr₁ : StrengthRule TweetyWorld := ⟨r₁, 1⟩
def sr₂ : StrengthRule TweetyWorld := ⟨r₂, 1⟩
def sr₃ : StrengthRule TweetyWorld := ⟨r₃, 2⟩

def Δ_pb_plus : StrengthKB TweetyWorld := [sr₁, sr₂, sr₃]

/-- Z⁺ priorities computed via the Z⁺_order procedure (Fig. 4) to
    satisfy δ-admissibility constraints.
    z⁺(r₁) = 1, z⁺(r₂) = 3, z⁺(r₃) = 4.

    The constraint for r₃ (δ=2) is κ(penguinNoFly) + 2 < κ(penguinFlies).
    Since penguinNoFly falsifies r₁ giving rank z⁺(r₁)+1 = 2,
    we need 2 + 2 < z⁺(r₃) + 1, so z⁺(r₃) ≥ 4.

    Note: z⁺(r₂) = 3 because the verifying world for r₂ (penguinNoFly)
    has κ = z⁺(r₁) + 1 = 2, so z⁺(r₂) = 2 + δ₂ = 2 + 1 = 3. r₂ is
    never falsified in TweetyWorld, so its priority doesn't affect ranks. -/
def zPlus_prioritized : List (DefaultRule TweetyWorld × ℕ) :=
  [(r₁, 1), (r₂, 3), (r₃, 4)]

/-- κ⁺: the Z⁺ ranking with wider gaps than κ^z.
    - birdFlies:    falsifies nothing → 0
    - birdNoFly:    falsifies r₁ (z⁺=1) → 2
    - penguinFlies: falsifies r₃ (z⁺=4) → 5
    - penguinNoFly: falsifies r₁ (z⁺=1) → 2 -/
def κ_plus : RankingFunction TweetyWorld :=
  zRanking zPlus_prioritized ⟨.birdFlies, by decide⟩

theorem κplus_birdFlies : κ_plus.rank .birdFlies = 0 := by decide
theorem κplus_birdNoFly : κ_plus.rank .birdNoFly = 2 := by decide
theorem κplus_penguinFlies : κ_plus.rank .penguinFlies = 5 := by decide
theorem κplus_penguinNoFly : κ_plus.rank .penguinNoFly = 2 := by decide

/-- κ⁺ is δ-admissible relative to the strength rules. -/
theorem κplus_strength_admissible : strengthAdmissible κ_plus Δ_pb_plus := by
  intro sr hsr
  simp [Δ_pb_plus] at hsr
  rcases hsr with rfl | rfl | rfl
  · -- sr₁ (b→f, δ=1): birdFlies (rank 0) witnesses 0+1 < 2
    intro w hw
    cases w <;> simp_all [sr₁, r₁, DefaultRule.falsified, isBird, flies]
    all_goals exact ⟨.birdFlies, trivial, trivial, by decide⟩
  · -- sr₂ (p→b, δ=1): vacuously true
    intro w hw
    cases w <;> simp_all [sr₂, r₂, DefaultRule.falsified, isPenguin, isBird]
  · -- sr₃ (p→¬f, δ=2): penguinNoFly (rank 2) witnesses 2+2 < 5
    intro w hw
    cases w <;> simp_all [sr₃, r₃, DefaultRule.falsified, isPenguin, flies]
    exact ⟨.penguinNoFly, trivial, by decide, by decide⟩

/-- κ^z's gap for r₃ is too small for δ₃=2: 1 + 2 ≥ 2.
    This motivates Z⁺ — the minimal ranking κ^z doesn't provide
    enough separation for variable-strength defaults. -/
theorem κz_gap_too_small_for_sr₃ :
    κ_z.rank .penguinNoFly + sr₃.strength ≥ κ_z.rank .penguinFlies := by decide

end GoldszmidtPearl1996
