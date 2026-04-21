import Linglib.Core.Agent.RationalAction
import Linglib.Core.Agent.BToM
import Linglib.Theories.Pragmatics.RSA.Defs

/-!
# RSAConfig — Unified RSA Configuration
@cite{degen-2023} @cite{frank-goodman-2012} @cite{bergen-levy-goodman-2016} @cite{kao-etal-2014-hyperbole} @cite{qing-franke-2013}

A streamlined RSA configuration grounded in rational action theory. Each RSA
model decomposes into two orthogonal dimensions:

1. **What the agent optimizes** — the scoring rule (`s1Score`)
2. **What the observer marginalizes over** — the latent structure (`Latent`)

## Architecture

All three RSA levels are `RationalAction` instances:

    L0agent(l) : RationalAction U W score(u, w) = meaning(l, u, w)
    S1agent(l) : RationalAction W U score(w, u) = s1Score(L0.policy, α, l, w, u)
    L1agent : RationalAction U W score(u, w) = prior(w) · Σ_l prior(l|w) · S1(u|w,l)

L0 scores are just the meaning function — any prior the paper wants in L0
is baked into `meaning`. The empirical `worldPrior` (object salience, base
rates) enters only at L1, keeping L0 fixed under iterated updates.

Latent variables (QUDs, lexicons, thresholds) can enter at two levels:
- **L0 (meaning)**: e.g., lexical uncertainty
- **S1 (s1Score)**: e.g., QUD projection

The `s1Score` field takes the latent variable `l` so each paper can specify
exactly where its latent variables enter:

| Model | meaning uses latent? | s1Score uses latent? |
|-------|---------------------|---------------------|
| @cite{frank-goodman-2012} | no (Unit) | no (Unit) |
| @cite{kao-etal-2014-hyperbole} (QUD) | no (ignores q) | yes (cell aggregation) |
| @cite{bergen-levy-goodman-2016} (lex) | yes (lexicon) | no (standard rpow) |

S1 score examples:
- Belief-based (@cite{frank-goodman-2012}): score = rpow(L0(w|u), α). rpow(0,α)=0.
- Action-based (@cite{qing-franke-2013}): score = exp(α · (L0(w|u) - cost(u)))
- QUD-based: score = exp(α · (ln L0(g(s,a)|u) - C(u)))

## BToM Grounding (§5)

Every RSAConfig gives rise to a BToM generative model via `toBToM`. The
pragmatic listener (L1) IS a BToM observer: `L1_eq_btom_worldMarginal`
proves that L1's score equals the BToM world marginal. See
`BToMGrounding.lean` for latent classification (Gricean vs channel-theoretic).
-/

namespace RSA

open BigOperators Core Core.BToM

variable {U W : Type*} [Fintype U] [Fintype W]

-- ============================================================================
-- L0: Literal Listener
-- ============================================================================

namespace RSAConfig

/-- L0 at a specific context (for sequential models).

Scores each world w by meaning(ctx, l, u, w). For one-shot models,
use `L0agent` which fixes ctx = initial. -/
noncomputable def L0agent_at (cfg : RSAConfig U W) (ctx : cfg.Ctx) (l : cfg.Latent) :
    RationalAction U W where
  score u w := cfg.meaning ctx l u w
  score_nonneg u w := cfg.meaning_nonneg ctx l u w

/-- L0 as a RationalAction (one per latent value), at initial context.

L0 is the literal listener: given utterance u, score each world w by
meaning(initial, l, u, w). The policy gives the normalized posterior L0(w|u, l).

The meaning function IS the score — any prior the paper wants in L0
is baked into `meaning`, not applied separately. This keeps L0 fixed
under iterated prior updates at L1. -/
noncomputable def L0agent (cfg : RSAConfig U W) (l : cfg.Latent) :
    RationalAction U W where
  score u w := cfg.meaning cfg.initial l u w
  score_nonneg u w := cfg.meaning_nonneg cfg.initial l u w

/-- L0 posterior: P(w|u, l) = meaning(initial,l,u,w) / Σ_w' meaning(initial,l,u,w'). -/
noncomputable def L0 (cfg : RSAConfig U W) (l : cfg.Latent) (u : U) (w : W) : ℝ :=
  (cfg.L0agent l).policy u w

/-- L0 marginal: P(P|u, l) = Σ_{w : P(w)} L0(w|u, l).
    Sums the L0 posterior over worlds satisfying a decidable predicate. -/
noncomputable def L0_marginal (cfg : RSAConfig U W) (l : cfg.Latent) (u : U)
    (P : W → Prop) [DecidablePred P] : ℝ :=
  ∑ w ∈ Finset.univ.filter P, cfg.L0 l u w

-- ============================================================================
-- S1: Pragmatic Speaker
-- ============================================================================

/-- S1 at a specific context (for sequential models).

Uses L0_at(ctx) as the literal listener, so the speaker's informativity
computation reflects the context-dependent meaning. -/
noncomputable def S1agent_at (cfg : RSAConfig U W) (ctx : cfg.Ctx) (l : cfg.Latent) :
    RationalAction W U where
  score w u := cfg.s1Score (cfg.L0agent_at ctx l).policy cfg.α l w u
  score_nonneg _ _ := cfg.s1Score_nonneg _ _ _ _ _
    (fun u' w' => (cfg.L0agent_at ctx l).policy_nonneg u' w') cfg.α_pos

/-- S1 as a RationalAction, at initial context.

S1's score is computed by `s1Score`, which takes L0's normalized posterior,
the rationality parameter α, and the latent variable value. The score
function is pluggable — different papers provide different scoring rules:

- Belief-based: score = rpow(L0(w|u), α). Correct: rpow(0, α) = 0.
- Action-based: score = exp(α · L0(w|u)).
- QUD-based: score = rpow(qudProject(q, L0(u), w), α).

The latent parameter `l` enters `s1Score` so that latent variables like
QUDs can affect S1 scoring without being forced into L0's meaning. -/
noncomputable def S1agent (cfg : RSAConfig U W) (l : cfg.Latent) :
    RationalAction W U where
  score w u := cfg.s1Score (cfg.L0agent l).policy cfg.α l w u
  score_nonneg _ _ := cfg.s1Score_nonneg _ _ _ _ _
    (fun u' w' => (cfg.L0agent l).policy_nonneg u' w') cfg.α_pos

/-- S1 policy at initial context: P(u|w, l). -/
noncomputable def S1 (cfg : RSAConfig U W) (l : cfg.Latent) (w : W) (u : U) : ℝ :=
  (cfg.S1agent l).policy w u

/-- S1 policy at a specific context. -/
noncomputable def S1_at (cfg : RSAConfig U W) (ctx : cfg.Ctx) (l : cfg.Latent)
    (w : W) (u : U) : ℝ :=
  (cfg.S1agent_at ctx l).policy w u

theorem S1_nonneg (cfg : RSAConfig U W) (l : cfg.Latent) (w : W) (u : U) :
    0 ≤ cfg.S1 l w u :=
  (cfg.S1agent l).policy_nonneg w u

theorem S1_sum_eq_one (cfg : RSAConfig U W) (l : cfg.Latent) (w : W)
    (h : (cfg.S1agent l).totalScore w ≠ 0) :
    ∑ u : U, cfg.S1 l w u = 1 :=
  (cfg.S1agent l).policy_sum_eq_one w h

-- ============================================================================
-- L1: Pragmatic Listener
-- ============================================================================

/-- L1 as a RationalAction.

The pragmatic listener inverts S1 via Bayes' rule, marginalizing over
latent variables. Score = prior(w) · Σ_l prior(l|w) · S1(u|w,l).

The empirical `worldPrior` enters here (not at L0), so L0 stays fixed
under iterated prior updates.

In reference games, L1 is choosing a target object.
In other settings, L1 is updating beliefs about the world.
Either way, the math is the same. -/
noncomputable def L1agent (cfg : RSAConfig U W) :
    RationalAction U W where
  score u w := cfg.worldPrior w * ∑ l : cfg.Latent, cfg.latentPrior w l * cfg.S1 l w u
  score_nonneg u w := mul_nonneg (cfg.worldPrior_nonneg w)
    (Finset.sum_nonneg fun l _ => mul_nonneg (cfg.latentPrior_nonneg w l) (cfg.S1_nonneg l w u))

/-- L1 posterior: P(w|u) ∝ prior(w) · Σ_l prior(l) · S1(u|w,l). -/
noncomputable def L1 (cfg : RSAConfig U W) (u : U) (w : W) : ℝ :=
  cfg.L1agent.policy u w

/-- L1 posterior over latent variables: P(l|u) ∝ Σ_w prior(w) · prior(l|w) · S1(u|w,l). -/
noncomputable def L1_latent (cfg : RSAConfig U W) (u : U) (l : cfg.Latent) : ℝ :=
  let score := ∑ w : W, cfg.worldPrior w * cfg.latentPrior w l * cfg.S1 l w u
  let total := ∑ l' : cfg.Latent, ∑ w : W, cfg.worldPrior w * cfg.latentPrior w l' * cfg.S1 l' w u
  if total = 0 then 0 else score / total

/-- L1 latent inference as a RationalAction.

The pragmatic listener's posterior over latent variables, viewed as a
Luce choice rule. Score for latent value l is:
  Σ_w worldPrior(w) · latentPrior(w,l) · S1(l,w,u)

This mirrors `L1_latent` but packages the computation as a `RationalAction`,
enabling `policy_lt_of_score_lt` for compositional proofs. -/
noncomputable def L1_latent_agent (cfg : RSAConfig U W) (u : U) :
    RationalAction Unit cfg.Latent where
  score _ l := ∑ w : W, cfg.worldPrior w * cfg.latentPrior w l * cfg.S1 l w u
  score_nonneg _ l := Finset.sum_nonneg fun w _ =>
    mul_nonneg (mul_nonneg (cfg.worldPrior_nonneg w) (cfg.latentPrior_nonneg w l))
      (cfg.S1_nonneg l w u)

/-- Bridge: `L1_latent` equals `L1_latent_agent.policy`.

Both sides unfold to `if total = 0 then 0 else score / total` with the
same score function, so equality is definitional up to unfolding. -/
theorem L1_latent_eq_policy (cfg : RSAConfig U W) (u : U) (l : cfg.Latent) :
    cfg.L1_latent u l = (cfg.L1_latent_agent u).policy () l := by
  simp only [L1_latent, L1_latent_agent, RationalAction.policy, RationalAction.totalScore]

/-- Score ordering implies L1_latent ordering. Denominator cancellation
    for latent comparisons: since `L1_latent u l = L1_latent_agent.policy () l`,
    comparing L1_latent reduces to comparing L1_latent_agent scores.

    Used by `rsa_predict` to eliminate the shared normalization constant
    when comparing `L1_latent u l₁ < L1_latent u l₂`. -/
@[gcongr]
theorem L1_latent_lt_of_score_lt (cfg : RSAConfig U W) (u : U)
    (l₁ l₂ : cfg.Latent)
    (h : (cfg.L1_latent_agent u).score () l₁ < (cfg.L1_latent_agent u).score () l₂) :
    cfg.L1_latent u l₁ < cfg.L1_latent u l₂ := by
  rw [L1_latent_eq_policy, L1_latent_eq_policy]
  exact RationalAction.policy_lt_of_score_lt _ () l₁ l₂ h

/-- L1 marginal: P(P|u) = Σ_{w : P(w)} L1(w|u).
    Sums the L1 posterior over worlds satisfying a decidable predicate. -/
noncomputable def L1_marginal (cfg : RSAConfig U W) (u : U)
    (P : W → Prop) [DecidablePred P] : ℝ :=
  ∑ w ∈ Finset.univ.filter P, cfg.L1 u w

/-- Score-sum ordering implies L1_marginal ordering. Denominator cancellation
    for marginal comparisons: since all L1(u,w) share the same totalScore(u),
    comparing marginal sums reduces to comparing score sums.

    Used by `rsa_predict` to eliminate the shared normalization constant
    when comparing `L1_marginal u P < L1_marginal u Q`. -/
@[gcongr]
theorem L1_marginal_lt_of_score_sum_lt (cfg : RSAConfig U W) (u : U)
    (P Q : W → Prop) [DecidablePred P] [DecidablePred Q]
    (h : (Finset.univ.filter P).sum (cfg.L1agent.score u) <
         (Finset.univ.filter Q).sum (cfg.L1agent.score u)) :
    cfg.L1_marginal u P < cfg.L1_marginal u Q := by
  unfold L1_marginal L1
  exact RationalAction.finset_sum_policy_lt_of_sum_score_lt cfg.L1agent u _ _ h

-- ============================================================================
-- S2: Pragmatic Speaker (endorsement)
-- ============================================================================

/-- S2 agent: pragmatic speaker conditioning on observed world.

    S2 inverts L1 via Bayes' rule over utterances (eq 8, @cite{scontras-pearl-2021}):
    S2(u|w) ∝ P_{L1}(w|u) = L1(u, w) [the normalized L1 posterior]

    Used for endorsement tasks: "would you endorse utterance u given that
    you observed world w?" This differs from L1 because L1 conditions on
    the heard utterance (shared denominator across worlds), while S2
    conditions on the observed world (different denominator per world).

    The score is the **normalized** L1 posterior P(w|u), not the unnormalized
    L1 score. This matters: worldPrior enters through L1's normalization
    denominator, so different worldPriors produce different S2 values. -/
noncomputable def S2agent (cfg : RSAConfig U W) : RationalAction W U where
  score w u := cfg.L1 u w
  score_nonneg w u := cfg.L1agent.policy_nonneg u w

/-- S2 policy: P(u|w) = L1(u,w) / Σ_{u'} L1(u',w). -/
noncomputable def S2 (cfg : RSAConfig U W) (w : W) (u : U) : ℝ :=
  cfg.S2agent.policy w u

theorem S2_nonneg (cfg : RSAConfig U W) (w : W) (u : U) :
    0 ≤ cfg.S2 w u :=
  cfg.S2agent.policy_nonneg w u

theorem L1_nonneg (cfg : RSAConfig U W) (u : U) (w : W) :
    0 ≤ cfg.L1 u w :=
  cfg.L1agent.policy_nonneg u w

theorem L1_latent_nonneg (cfg : RSAConfig U W) (u : U) (l : cfg.Latent) :
    0 ≤ cfg.L1_latent u l := by
  simp only [L1_latent]
  split
  · exact le_refl 0
  · exact div_nonneg
      (Finset.sum_nonneg fun w _ =>
        mul_nonneg (mul_nonneg (cfg.worldPrior_nonneg w) (cfg.latentPrior_nonneg w l))
          (cfg.S1_nonneg l w u))
      (Finset.sum_nonneg fun l' _ =>
        Finset.sum_nonneg fun w _ =>
          mul_nonneg (mul_nonneg (cfg.worldPrior_nonneg w) (cfg.latentPrior_nonneg w l'))
            (cfg.S1_nonneg l' w u))

-- ============================================================================
-- Stack: Composing RSA Levels
-- ============================================================================

/-- Build a higher-level RSAConfig from a lower-level one.

The lower-level per-lexicon listener l₁(w|u,L) becomes the new L0 meaning.
The new S1 scoring rule applies `rpow(l₁(w|u,L), α₂)` times an optional
`bonus` (e.g., L₁(L|u)^β for expertise) and `costFactor` (e.g., exp(-C(u))).

This gives `S₂(u|w,L) ∝ l₁(w|u,L)^α₂ · bonus(L,u) · costFactor(u)`,
matching eq 15 of @cite{potts-levy-2015} when `bonus = L₁(L|u)` and
`costFactor = exp(-C(u))`.

The stacked config's L1 = L₂ (world posterior) and L1_latent = L₂_latent
(lexicon posterior), all provable with `rsa_predict`. -/
noncomputable def stack (cfg : RSAConfig U W)
    (α₂ : ℝ) (hα₂ : 0 < α₂)
    (bonus : cfg.Latent → U → ℝ := fun _ _ => 1)
    (bonus_nonneg : ∀ l u, 0 ≤ bonus l u := by intros; norm_num)
    (costFactor : U → ℝ := fun _ => 1)
    (costFactor_nonneg : ∀ u, 0 ≤ costFactor u := by intros; norm_num)
    : RSAConfig U W where
  Latent := cfg.Latent
  meaning _ l u w := cfg.worldPrior w * cfg.S1 l w u
  meaning_nonneg _ l u w := mul_nonneg (cfg.worldPrior_nonneg w) (cfg.S1_nonneg l w u)
  s1Score l0 α l w u := Real.rpow (l0 u w) α * bonus l u * costFactor u
  s1Score_nonneg _ _ l _ u hl0 hα :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (hl0 _ _) _) (bonus_nonneg l u))
      (costFactor_nonneg u)
  α := α₂
  α_pos := hα₂
  latentPrior := cfg.latentPrior
  latentPrior_nonneg := cfg.latentPrior_nonneg
  worldPrior := cfg.worldPrior
  worldPrior_nonneg := cfg.worldPrior_nonneg

-- ============================================================================
-- Sequential RSA: Trajectory Probabilities
-- ============================================================================

/-- S1 probability of producing utterance `u` in context `ctx`, for world `w`
    and latent value `l`. This is one step of the sequential chain rule. -/
noncomputable def S1_at_nonneg (cfg : RSAConfig U W) (ctx : cfg.Ctx)
    (l : cfg.Latent) (w : W) (u : U) : 0 ≤ cfg.S1_at ctx l w u :=
  (cfg.S1agent_at ctx l).policy_nonneg w u

/-- Trajectory probability starting from an arbitrary context. -/
noncomputable def trajectoryProbFrom (cfg : RSAConfig U W)
    (ctx : cfg.Ctx) (l : cfg.Latent) (w : W) : List U → ℝ
  | [] => 1
  | u :: us => cfg.S1_at ctx l w u *
               cfg.trajectoryProbFrom (cfg.transition ctx u) l w us

/-- Trajectory probability: the probability that S1 produces the sequence
    `traj = [u₁, u₂, ..., uₙ]` word-by-word, starting from `initial`.

    S1(traj | w, l) = ∏ⱼ S1_at(ctxⱼ, l, w, uⱼ)

    where ctx₀ = initial and ctxⱼ₊₁ = transition(ctxⱼ, uⱼ).

    This is the chain rule for incremental production
    (@cite{cohn-gordon-goodman-potts-2019}, @cite{waldon-degen-2021}). -/
noncomputable def trajectoryProb (cfg : RSAConfig U W)
    (l : cfg.Latent) (w : W) (traj : List U) : ℝ :=
  cfg.trajectoryProbFrom cfg.initial l w traj

theorem trajectoryProbFrom_nil (cfg : RSAConfig U W) (ctx : cfg.Ctx)
    (l : cfg.Latent) (w : W) :
    cfg.trajectoryProbFrom ctx l w [] = 1 := rfl

theorem trajectoryProbFrom_cons (cfg : RSAConfig U W) (ctx : cfg.Ctx)
    (l : cfg.Latent) (w : W) (u : U) (us : List U) :
    cfg.trajectoryProbFrom ctx l w (u :: us) =
    cfg.S1_at ctx l w u * cfg.trajectoryProbFrom (cfg.transition ctx u) l w us := rfl

theorem trajectoryProbFrom_nonneg (cfg : RSAConfig U W) (ctx : cfg.Ctx)
    (l : cfg.Latent) (w : W) (traj : List U) :
    0 ≤ cfg.trajectoryProbFrom ctx l w traj := by
  induction traj generalizing ctx with
  | nil => exact one_pos.le
  | cons u us ih =>
    exact mul_nonneg (cfg.S1_at_nonneg ctx l w u) (ih (cfg.transition ctx u))

-- ============================================================================
-- §4b. Action-Oriented Listener (L1_action)
-- ============================================================================

/-- Action-oriented listener: applies a second softmax to L1 beliefs.

    ρ_a(w | u) = softmax(L1(u, ·), α_L)(w)

    Models a listener who soft-maximizes over Bayesian beliefs rather than
    reporting beliefs directly (@cite{qing-franke-2015}). Provides an additional
    degree of freedom (α_L) for fitting listener data. -/
noncomputable def L1_action (cfg : RSAConfig U W) (αL : ℝ) (u : U) (w : W) : ℝ :=
  softmax (cfg.L1 u) αL w

/-- The action-oriented listener always assigns positive probability. -/
theorem L1_action_pos [Nonempty W] (cfg : RSAConfig U W) (αL : ℝ) (u : U) (w : W) :
    0 < cfg.L1_action αL u w :=
  softmax_pos _ _ _

/-- The action-oriented listener produces a valid probability distribution. -/
theorem L1_action_sum_eq_one [Nonempty W] (cfg : RSAConfig U W) (αL : ℝ) (u : U) :
    ∑ w : W, cfg.L1_action αL u w = 1 :=
  softmax_sum_eq_one _ _

/-- Higher α_L sharpens the action-oriented listener's distribution:
    if L1 prefers w₁ over w₂, ρ_a amplifies this preference. -/
theorem L1_action_amplifies [Nonempty W] (cfg : RSAConfig U W)
    {αL : ℝ} (hα : 0 < αL) (u : U) (w₁ w₂ : W)
    (h : cfg.L1 u w₁ > cfg.L1 u w₂) :
    cfg.L1_action αL u w₁ > cfg.L1_action αL u w₂ :=
  softmax_strict_mono _ hα _ _ h

end RSAConfig

-- ============================================================================
-- §5. BToM Grounding: RSAConfig → BToMModel
-- ============================================================================

namespace RSAConfig

variable {U W : Type*} [Fintype U] [Fintype W]

/-- Map an RSAConfig to a BToM generative model.

The mapping from RSA to BToM ontology:
- **Action** = U (utterance)
- **Percept** = W (speaker perceives the world directly — perfect perception)
- **Belief** = W (speaker's belief matches the world — perfect knowledge)
- **Desire** = cfg.Latent (speaker's latent state: goals, interpretations, etc.)
- **Shared** = Unit (single-utterance models have fixed common ground)
- **Medium** = Unit (channel properties not separately modeled)
- **World** = W

The perception/belief chain uses Kronecker deltas `[p = w]` and `[b = p]`,
reflecting the standard RSA assumption that the speaker knows the true world
state. RSA's world-conditioned latent prior `latentPrior(w, l)` maps directly
to BToM's world-conditioned desire prior `desirePrior(w, d)`, making the
correspondence transparent.

See `L1_eq_btom_worldMarginal` for the proof that this BToM model's
world marginal equals `cfg.L1agent.score`. -/
noncomputable def toBToM (cfg : RSAConfig U W) [DecidableEq W] :
    BToMModel ℝ U W W cfg.Latent Unit Unit W where
  perceptModel w p := if p = w then 1 else 0
  beliefModel p b := if b = p then 1 else 0
  planModel b d _ _ a := cfg.S1 d b a
  worldPrior := cfg.worldPrior
  desirePrior := cfg.latentPrior
  sharedPrior _ := 1
  mediumPrior _ := 1

set_option maxHeartbeats 1600000 in
/-- RSA's pragmatic listener IS BToM world-marginal inference.

L1's score function — `worldPrior(w) · Σ_l latentPrior(w,l) · S1(u|w,l)` —
equals the world marginal of the BToM model constructed by `toBToM`. This
makes RSA's listener a genuine instance of BToM observer inference, not
merely an analogy.

Proof sketch: The delta functions in `perceptModel` and `beliefModel` collapse
the sums over `Percept = W` and `Belief = W` to the single term where
`p = w` and `b = w`. The sums over `Shared = Unit` and `Medium = Unit`
contribute factor 1. The remaining sum over `Desire = Latent` matches
`cfg.L1agent.score` by definition of `planModel` and `desirePrior`. -/
theorem L1_eq_btom_worldMarginal [DecidableEq W]
    (cfg : RSAConfig U W) (u : U) (w : W) :
    cfg.L1agent.score u w = (cfg.toBToM).worldMarginal u w := by
  unfold L1agent toBToM BToMModel.worldMarginal BToMModel.jointScore
  simp only [Fintype.sum_unique, mul_one]
  have key : ∀ (c : Prop) [Decidable c] (a : ℝ),
      a * (if c then (1 : ℝ) else 0) = if c then a else 0 := by
    intros c _ a; split <;> simp
  simp_rw [key]
  simp_rw [ite_mul, zero_mul]
  simp [Finset.sum_ite_eq']
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

end RSAConfig

end RSA
