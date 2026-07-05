import Linglib.Core.Probability.DataProcessing
import Linglib.Core.Probability.Entropy
import Linglib.Core.Probability.Posterior
import Linglib.Pragmatics.RSA.Operators

/-!
# Cancellation theorems for RSA models with noisy observation

[goodman-stuhlmuller-2013]'s **cancellation principle** (informal):
as a speaker's observation kernel becomes noisier, the listener's posterior
given an utterance moves closer to the prior.

This file states the **structural information-theoretic content** that follows
from the data processing inequality (DPI), and **honestly scopes** what's
universal vs paper-specific.

## What IS structurally provable (Path B from session audit)

* **Observation-level cancellation** (`mutualInformation_state_obs_le`):
  `MI(state; obs_noisy) ≤ MI(state; obs_informative)` when
  `κ_noisy = κ_informative.bind noise`. Direct corollary of `PMF.klDiv_bind_le`
  applied per-state with the noise kernel.

## What IS NOT structurally provable

* **Utterance-level cancellation** `MI(state; utt_noisy) ≤ MI(state; utt_informative)`:
  this is **not** a clean DPI corollary. The Markov chain `state → Y_i → (U_i, U_n) → U_n`
  gives `MI(state; U_n) ≤ MI(state; Y_i)`, but no direct comparison between `U_n` and
  `U_i` because `U_i` and `U_n` share `Y_i` as a common parent — there's no chain
  `state → U_i → U_n`. May or may not hold depending on `S1g` shape.

* **Per-(world-pair) ordering** (e.g. GS2013's "L1(s2 | u) > L1(s3 | u) weakens with
  noise"): this is per-paper, depends on lex shape, and requires numerical evaluation.

## Architectural framing

- **Universal substrate** (here): the obs-level MI cancellation — a real theorem
  any RSA paper with a noisy obs chain can use.
- **Per-paper findings**: numerical evaluations of model behavior, illustrations
  of how the structural inequality manifests for specific lex / kernel shapes.
- **Anti-pattern**: claiming a single "cancellation theorem" that yields all the
  per-cell numerical orderings as corollaries. (No such theorem; the per-paper
  orderings depend on more than just kernel informativity.)
-/

set_option autoImplicit false

namespace RSA

open InformationTheory PMF
open scoped ENNReal

/-! ## §1. Observation-level mutual information

Define `MI(state; obs) = ∑_s prior(s) · KL(κ s ‖ marg)`. This is the standard
chain-rule decomposition (Cover-Thomas Eq 2.61): the average information about
the state contained in an observation, equivalent to `KL(joint ‖ product)`.

Working with this form rather than `PMF.mutualInformation` directly because the
per-state decomposition is what makes DPI applicable: each `KL(κ_n s ‖ marg_n)`
vs `KL(κ_i s ‖ marg_i)` term reduces by `klDiv_bind_le` per-state with kernel
`noise : Obs → PMF Obs`. The state component never enters the kernel, so the
state-preservation support issue vanishes.
-/

variable {W Obs : Type*} [Fintype W] [Fintype Obs]
  [MeasurableSpace W] [MeasurableSingletonClass W]
  [MeasurableSpace Obs] [MeasurableSingletonClass Obs]

/-- The observation marginal `marg_o(o) = ∑_s prior(s) · κ(s)(o)`. -/
noncomputable def obsMarginal (prior : PMF W) (κ : W → PMF Obs) : PMF Obs :=
  prior.bind κ

/-- **Per-state-decomposed mutual information** between state and observation:
`MI(state; obs) = ∑_s prior(s) · KL(κ s ‖ marg)`.

This is the conditional-relative-entropy form (Cover-Thomas Eq 2.61). For any
joint `J(s, o) = prior(s) · κ(s)(o)` with marginal `marg(o) = ∑_s J(s, o)`,
the standard MI `KL(J ‖ prior × marg)` equals this per-state weighted sum.
The decomposition is what makes the DPI argument tractable. -/
noncomputable def mutualInfoStateObs (prior : PMF W) (κ : W → PMF Obs) : ℝ≥0∞ :=
  ∑ s, prior s * (κ s).klDiv (obsMarginal prior κ)

/-! ## §2. Observation-level DPI cancellation

**Theorem**: if `κ_n s = (κ_i s).bind noise` for all states `s` (the noisy
observation kernel is a post-processing of the informative one through some
noise channel), then `MI(state; obs_n) ≤ MI(state; obs_i)`.

The proof applies `PMF.klDiv_bind_le` per-state. For each `s`, we have
`κ_n s = (κ_i s).bind noise` AND `obsMarginal prior κ_n = (obsMarginal prior κ_i).bind noise`
(since bind distributes over outer bind). The per-state KL inequality lifts
to the prior-weighted sum.
-/

/-- **Observation marginal under noisy kernel = noise-bind of informative marginal**.
This is the fact that lets the per-state DPI lift to the marginal level. -/
theorem obsMarginal_bind_noise (prior : PMF W) (κ_i : W → PMF Obs)
    (noise : Obs → PMF Obs) :
    obsMarginal prior (fun s => (κ_i s).bind noise)
      = (obsMarginal prior κ_i).bind noise := by
  unfold obsMarginal
  exact (PMF.bind_bind prior κ_i noise).symm

/-- **Observation-level cancellation theorem (DPI form)**.

If the noisy observation kernel is a post-processing of the informative kernel
through a noise channel (`κ_n s = (κ_i s).bind noise`), then the mutual
information between state and observation decreases.

Reduces to `PMF.klDiv_bind_le` applied per-state; the hypothesis `h_ac` is
per-state absolute continuity of `κ_i s` w.r.t. `obsMarginal prior κ_i`.

This is the structural information-theoretic content of "less informative
observation kernel → less information about state in the observation". -/
theorem mutualInfoStateObs_bind_noise_le
    (prior : PMF W) (κ_i : W → PMF Obs) (noise : Obs → PMF Obs)
    (h_ac : ∀ s, MeasureTheory.Measure.AbsolutelyContinuous
              (κ_i s).toMeasure (obsMarginal prior κ_i).toMeasure) :
    mutualInfoStateObs prior (fun s => (κ_i s).bind noise)
      ≤ mutualInfoStateObs prior κ_i := by
  unfold mutualInfoStateObs
  rw [obsMarginal_bind_noise]
  refine Finset.sum_le_sum (fun s _ => ?_)
  -- For each state s: the noisy term `KL((κ_i s).bind noise ‖ marg.bind noise)`
  -- is ≤ informative term `KL(κ_i s ‖ marg)` by `klDiv_bind_le`.
  -- Need: prior(s) · KL_n ≤ prior(s) · KL_i (left-mult preserves ≤ in ℝ≥0∞)
  have h_kl := klDiv_bind_le (κ_i s) (obsMarginal prior κ_i) noise (h_ac s)
  -- mul_le_mul_left needs left arg as `(a : ℝ≥0∞)`, returns `b ≤ c → a * b ≤ a * c`
  exact mul_le_mul' (le_refl _) h_kl

/-! ## §3. Honest scoping note

The utterance-level form (`MI(state; utt_n) ≤ MI(state; utt_i)`) does NOT follow
from §2 by composing with `S1g : Obs → PMF U`. The natural composition gives:

```
MI(state; utt_x) ≤ MI(state; obs_x) ≤ MI(state; obs_i)   for x ∈ {n, i}
```

So both `MI(state; utt_n)` and `MI(state; utt_i)` are bounded by `MI(state; obs_i)`
— no direct comparison between them. The Markov chain `state → Y_i → (U_i, U_n)`
gives `MI(state; U_n) ≤ MI(state; Y_i)` but there's no chain `state → U_i → U_n`
because `U_n` depends on `Y_i` directly via `noise(Y_i)`, not just on `U_i`.

GS2013's per-(world-pair) findings (e.g. "L1(s2 | u) > L1(s3 | u) weakens at
lower access") are NOT corollaries of any clean MI cancellation. They are
specific numerical evaluations of the model — see
`Studies/GoodmanStuhlmuller2013.lean` for the
illustrative computations.

The proper architectural framing: §2 above is the universal structural theorem
about RSA models with noisy observation chains. Per-paper findings are
illustrations of how that structural fact manifests for specific (lex, kernel)
shapes — not corollaries provable from §2 alone. -/

end RSA
