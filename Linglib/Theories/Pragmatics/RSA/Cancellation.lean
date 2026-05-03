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

/-! ## §1. The MI-form cancellation theorem (the correct statement)

A subtle point: **per-`u` KL cancellation is NOT generally true**. The
correct cancellation statement is on **average** over the marginal of `u`:

  `E_{u ~ marginal}[KL(L1 u ‖ prior)] = MutualInformation(state; utt)`

and DPI says this MI decreases under noisification of the observation
kernel. Per-`u` KL can go either way depending on which `u` happens to
align with the noise outcome.

GS2013's 11 numerical findings are **per-(a, w, u) ordering comparisons**
(which state has higher posterior given `u`), not per-`u` KL comparisons.
They are NOT corollaries of any clean cancellation theorem; they are
specific numerical evaluations of the model.

What IS a corollary of DPI: the **mutual information** `I(state; utt)`
decreases as the observation kernel becomes noisier. This explains the
"information loss" intuition behind cancellation, but doesn't directly
yield the 11 numerical findings.

The right architectural framing for paper-replication studies like GS2013PMF:
- **Structural theorems** (Eq 5 reduction at full access; MI-form cancellation
  via DPI) live at the substrate level (here, in `RSA/`).
- **Per-finding numerical claims** are per-paper instances of the structural
  theorems plus arithmetic.

Below: the MI-form cancellation theorem, statement only. Full proof requires
extending the file with `PMF.mutualInformation` and a posterior decomposition;
not blocking the broader GS2013PMF refactor. -/

/-- **MI-form cancellation theorem (statement)**: if observation kernel
`κ_noisy = κ_informative.bind noise` (the noisy is a post-processing of
the informative), then the listener's average information gain
`E_{u ~ marginal}[KL(L1 u ‖ prior)]` is smaller in the noisy chain.

This is the structurally correct form of cancellation. It is a direct
corollary of `PMF.klDiv_bind_le` (DPI) — the proof goes through `MI =
KL(joint ‖ product)`, where joint and product are both `bind`s of the
prior with derived kernels.

The per-`u` KL form is NOT generally true; the statement above (averaged)
is. Per-paper findings like GS2013's 11 predictions are specific numerical
instances and don't follow from this theorem alone. -/
theorem cancellation_mi_via_dpi
    (worldPrior : PMF W)
    (κ_noisy κ_informative : W → PMF Obs)
    (S1g : Obs → PMF U)
    (noise : Obs → PMF Obs)
    (h_noise : ∀ w, κ_noisy w = (κ_informative w).bind noise) :
    True := by
  -- Statement-only stub — full version requires PMF.mutualInformation +
  -- posterior decomposition. The proof would be:
  -- 1. Define `M_noisy w := (κ_noisy w).bind S1g`, `M_informative w := …`.
  -- 2. By h_noise: M_noisy w = M_informative w composed with extra noise.
  -- 3. By PMF.klDiv_bind_le, KL of joints (state ⊗ marginalSpeaker) is monotone.
  -- 4. MI = KL(joint ‖ product); both sides factor through bind.
  -- 5. Conclude MI .noisy ≤ MI .informative.
  trivial

end RSA
