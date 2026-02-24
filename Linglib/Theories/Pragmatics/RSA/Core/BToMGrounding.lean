import Linglib.Core.BToM
import Linglib.Theories.Pragmatics.RSA.Core.Config

/-!
# RSA-BToM Grounding

Every RSAConfig gives rise to a BToM model. The pragmatic listener (L1) IS
a BToM observer: it inverts the pragmatic speaker (S1) via Bayesian inference,
jointly inferring the speaker's latent states and the world.

## Latent Classification

RSAConfig bundles all non-world latent variables into a single `Latent` type.
A `LatentClassification` assigns each component to a BToM ontological category,
making the cognitive interpretation explicit. Different theoretical positions
correspond to different classifications:

- **Strong Gricean**: Everything is mental state attribution. Interp → desire
  (speaker's intended meaning), Lexicon → belief (speaker's word knowledge),
  BeliefState → belief, Goal → desire.
- **Channel-theoretic**: Some variables are medium properties. Interp → medium
  (structural ambiguity), Lexicon → medium (language convention),
  BeliefState → belief, Goal → desire.
- **Clarkian**: Some variables are shared state. QUD → shared (jointly maintained
  question stack), common ground → shared, Lexicon → shared (conventions).

## Behavioral Equivalence

Different classifications of the same RSAConfig yield identical behavioral
predictions. This follows because marginalization doesn't care about labels:
`Σ_l f(l)` is the same whether `l` is called a belief or a medium property.
The classifications diverge only on cognitive-level claims about what kind
of inference the listener is performing.

## References

- Baker, Jara-Ettinger, Saxe & Tenenbaum (2017). Rational quantitative
  attribution of beliefs, desires and percepts in human mentalizing.
- Goodman & Frank (2016). Pragmatic Language Interpretation as
  Probabilistic Inference.
- Clark, H. (1996). Using Language. Cambridge University Press.
-/

open Core.BToM BigOperators

-- ============================================================================
-- §1. Latent Classification
-- ============================================================================

namespace RSA.BToMGrounding

/-- A classification of RSA latent variables into BToM ontological categories.

This is a cognitive-level commitment: it says what *kind* of thing each
latent variable represents. The classification does not affect behavioral
predictions: the classify function is never called by `toBToM` or the
inference machinery, so different classifications yield identical BToM
world marginals. -/
structure LatentClassification (Latent : Type*) where
  /-- Assign each latent variable value to a BToM category. -/
  classify : Latent → LatentCategory
  /-- Assign each latent variable a temporal dynamics.
      Default: episodic (each observation is independent). -/
  dynamics : Latent → FactorDynamics := fun _ => .episodic

/-- The strong Gricean classification: all latent variables are mental states.
    L1's inference is entirely Theory of Mind. -/
def griceanClassification (Latent : Type*) : LatentClassification Latent where
  classify _ := .mental

/-- The channel-theoretic classification: all latent variables are medium
    properties (structural ambiguity, conventions, channel noise).
    L1's inference is entirely signal disambiguation. -/
def channelClassification (Latent : Type*) : LatentClassification Latent where
  classify _ := .medium

end RSA.BToMGrounding

-- ============================================================================
-- §2. Structural Mapping: RSAConfig → BToMModel
-- ============================================================================

namespace RSA.RSAConfig

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

-- ============================================================================
-- §3. Bridge Theorems
-- ============================================================================

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

end RSA.RSAConfig
