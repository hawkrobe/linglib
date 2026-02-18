import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Bayesian Theory of Mind (BToM) @cite{baker-jaraettinger-saxe-tenenbaum-2017}

General framework for inverse rational agent models.

## The Core Principle

An observer attributes mental states (beliefs, desires) to an agent by
inverting a generative model of rational action (Baker et al. 2017):

```
World → Perception → Beliefs
                       ↓
                  Beliefs × Desires → Planning → Actions
                       ↑
                    Observer (inverts via Bayes' rule)
```

The observer's joint posterior over beliefs, desires, and world states:

  P(b, d, w | a) ∝ P(a | b, d) · P(b) · P(d) · P(w)

where P(a | b, d) is the agent's rational action model (softmax policy).

## Linguistic Specialization

In RSA (Goodman & Frank 2016), BToM specializes to:

| BToM Component | RSA Realization |
|----------------|-----------------|
| Agent          | Speaker         |
| Actions        | Utterances      |
| Observer       | Listener (L1)   |
| Beliefs        | Speaker's private assumptions (dcS) |
| Desires        | Communicative goals (QUD) |
| Planning       | S1 (softmax over informativity) |

L1 inverts S1's generative model, jointly inferring the speaker's
beliefs, goals, and the world state from the observed utterance.

## References

- Baker, Jara-Ettinger, Saxe & Tenenbaum (2017). Rational quantitative
  attribution of beliefs, desires and percepts in human mentalizing.
  Nature Human Behaviour 1, 0064.
- Goodman & Frank (2016). Pragmatic Language Interpretation as
  Probabilistic Inference. Trends in Cognitive Sciences 20(11).
-/

namespace Core.BToM

-- The BToM Generative Model

/--
A BToM generative model: an agent chooses actions rationally given
beliefs and desires; an observer inverts this to attribute mental states.

The four type parameters correspond to the components of the generative model:
- `Action`: the agent's observable behavior (utterances in RSA)
- `Belief`: the agent's epistemic state (private assumptions in RSA)
- `Desire`: the agent's goals (QUD in RSA)
- `World`: the state of the environment
-/
structure BToMModel (Action Belief Desire World : Type*) where
  /-- The agent's rational action model: P(a | b, d).
      In Baker et al., this is the softmax policy over Q-values:
      P(a | b, x, y) ∝ exp(β · Q^LA(b, x, y, a)).
      In RSA, this is S1: P(u | w, belief, qud). -/
  actionModel : Action → Belief → Desire → World → ℚ
  /-- Prior over beliefs: P(b). -/
  beliefPrior : Belief → ℚ
  /-- Prior over desires/goals: P(d). -/
  desirePrior : Desire → ℚ
  /-- Prior over world states: P(w). -/
  worldPrior : World → ℚ

variable {A B D W : Type*}

/--
The observer's unnormalized joint posterior over (belief, desire, world)
given an observed action:

  P(b, d, w | a) ∝ P(a | b, d, w) · P(b) · P(d) · P(w)

This is Equation 1 of Baker et al. (2017), adapted to the single-action
case. The observer jointly infers the agent's beliefs, desires, and
the world state from the observed action.
-/
def BToMModel.jointScore (m : BToMModel A B D W) (a : A) (b : B) (d : D) (w : W) : ℚ :=
  m.actionModel a b d w * m.beliefPrior b * m.desirePrior d * m.worldPrior w

-- Marginal Posteriors

section WorldMarginal
variable {A B D W : Type*} [Fintype B] [Fintype D]

/--
World marginal: P(w | a) ∝ Σ_{b,d} joint(a, b, d, w).
-/
def BToMModel.worldMarginal (m : BToMModel A B D W) (a : A) (w : W) : ℚ :=
  ∑ b : B, ∑ d : D, m.jointScore a b d w

/--
The world marginal factors as: P(w) · Σ_{b,d} P(a|b,d,w) · P(b) · P(d).

This shows that the world prior multiplies a sum that depends only on the
action model and the belief/desire priors — the standard factoring used
when deriving marginal posteriors from Bayes' rule.
-/
theorem BToMModel.worldMarginal_eq (m : BToMModel A B D W) (a : A) (w : W) :
    m.worldMarginal a w =
    m.worldPrior w * ∑ b : B, ∑ d : D,
      m.actionModel a b d w * m.beliefPrior b * m.desirePrior d := by
  simp only [worldMarginal, jointScore]
  trans (∑ b : B, ∑ d : D,
    m.worldPrior w * (m.actionModel a b d w * m.beliefPrior b * m.desirePrior d))
  · apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro d _
    ring
  · simp_rw [← Finset.mul_sum]

end WorldMarginal

section OtherMarginals
variable {A B D W : Type*} [Fintype B] [Fintype D] [Fintype W]

/--
Belief marginal: P(b | a) ∝ Σ_{d,w} joint(a, b, d, w).
-/
def BToMModel.beliefMarginal (m : BToMModel A B D W) (a : A) (b : B) : ℚ :=
  ∑ d : D, ∑ w : W, m.jointScore a b d w

/--
Desire marginal: P(d | a) ∝ Σ_{b,w} joint(a, b, d, w).
-/
def BToMModel.desireMarginal (m : BToMModel A B D W) (a : A) (d : D) : ℚ :=
  ∑ b : B, ∑ w : W, m.jointScore a b d w

end OtherMarginals

end Core.BToM
