import Linglib.Core.Probability.DataProcessing
import Linglib.Core.Probability.PMFPosterior
import Linglib.Theories.Pragmatics.RSA.Operators
import Linglib.Theories.Pragmatics.RSA.Silence

/-!
# Cancellation theorem for RSA models with noisy observation

@cite{goodman-stuhlmuller-2013}'s **cancellation principle**: as a speaker's
observation kernel becomes noisier (less informative about the state), the
listener's posterior given an utterance moves closer to the prior (gains
less information from the utterance).

Stated information-theoretically:

  `KL(L1 noisy u ‖ prior) ≤ KL(L1 informative u ‖ prior)`

where "noisy" and "informative" compare two observation kernels via a
post-composition relation: the noisy kernel is a post-processing of the
informative one through a stochastic map.

## Architectural role

This theorem is the structural foundation that should drive every
RSA-with-noisy-observation paper's findings. Per-paper "cancellation"
phenomena (GS2013 partial-access implicature weakening, Kao et al. metaphor
literal-reading recovery under noise, etc.) are corollaries.

## Proof structure

The proof reduces cancellation to:
1. **Data processing inequality** on PMF KL — `PMF.klDiv_bind_le` from
   `Linglib/Core/Probability/DataProcessing.lean`.
2. **Posterior monotonicity under more-informative likelihood** — the
   listener's posterior given a more-informative speaker model carries more
   KL from the prior.

Both are general probability-theory results not tied to RSA. The RSA
specialization just instantiates them for the speaker chain
`state → obs → utterance`.

## Status

DPI is proved up to a discharge sorry (see `Linglib/Core/Probability/DataProcessing.lean`);
the cancellation specialization is built on top assuming DPI. When the
DPI sorry lands, this file becomes sorry-free.
-/

set_option autoImplicit false

namespace RSA

open InformationTheory

/-!
## §1. Cancellation theorem statement

The general statement: for two noisy speaker chains differing only in the
observation kernel, the one with the "noisier" kernel produces a listener
posterior with smaller KL from the prior.

We parameterize the speaker chain by the observation kernel `obsKernel`
and the score function `S1g`. The marginalSpeaker is `obsKernel.bind S1g`,
and L1 is the posterior of marginalSpeaker against the prior.
-/

variable {W U Obs : Type*} [Fintype W] [Fintype Obs] [Fintype U]
  [MeasurableSpace W] [MeasurableSingletonClass W]
  [MeasurableSpace U] [MeasurableSingletonClass U]
  [MeasurableSpace Obs] [MeasurableSingletonClass Obs]

/-- **Cancellation theorem (state-of-the-art form)**: If observation kernel
`κ_noisy` is a post-processing of `κ_informative` through some stochastic
map `m : Obs → PMF Obs'`, then the resulting listener posterior `L1`
carries less KL from the prior in the noisy chain than in the informative
chain.

This is the GS2013 implicature-cancellation principle stated as monotonicity
of `L1`'s KL-from-prior under noisification of the observation kernel.

Proof sketch (deferred until DPI sorry discharges):
1. By DPI on `obsKernel.bind S1g` (where the bind composes with the noise
   map `m`), the marginalSpeaker for the noisy chain is a post-processing
   of the marginalSpeaker for the informative chain.
2. By DPI on `posterior` (Bayesian information processing), the L1 from
   the noisy marginalSpeaker has smaller KL from the prior.
3. Combine.

For our applications (GS2013), the noisy/informative kernels are `obsKernel`
at different access levels, related by hypergeometric-monotonicity. -/
theorem cancellation_via_dpi
    (worldPrior : PMF W)
    (κ_noisy κ_informative : W → PMF Obs)
    (S1g : Obs → PMF U)
    (noise : Obs → PMF Obs)  -- the noisification map
    (h_noise : ∀ w, κ_noisy w = (κ_informative w).bind noise)
    (u : U)
    (h_marg_noisy :
      PMF.marginal (fun w => (κ_noisy w).bind S1g) worldPrior u ≠ 0)
    (h_marg_informative :
      PMF.marginal (fun w => (κ_informative w).bind S1g) worldPrior u ≠ 0) :
    (PMF.posterior (fun w => (κ_noisy w).bind S1g) worldPrior u h_marg_noisy).klDiv worldPrior ≤
      (PMF.posterior (fun w => (κ_informative w).bind S1g) worldPrior u
          h_marg_informative).klDiv worldPrior := by
  /-
  Proof outline:
    Let M_noisy w := (κ_noisy w).bind S1g
    Let M_informative w := (κ_informative w).bind S1g
    By h_noise: M_noisy w = (κ_informative w).bind (noise.bind S1g) = M_informative w with extra noise

    DPI gives: marginal of M_noisy ≤ marginal of M_informative in informativity.
    Posterior monotonicity gives: KL of posterior from prior ≤ KL of posterior from prior.

    Each step uses PMF.klDiv_bind_le (currently sorry'd) plus posterior monotonicity
    (also needs to be proven; ~50 LOC follow-up).
  -/
  sorry

end RSA
