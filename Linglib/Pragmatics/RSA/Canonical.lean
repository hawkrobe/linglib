import Linglib.Core.Probability.Softmax
import Linglib.Core.Probability.JointPosterior
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Canonical RSA pipeline

The single `L0 → S1 → L1` pipeline for Rational Speech Act models
[frank-goodman-2012] [degen-2023], built directly on the `Core/Probability`
shell with no bundled configuration. The pragmatic speaker `S1` is the softmax
of an RSA utility; the pragmatic listener `L1` is the joint Bayesian posterior
over `world × latent`, with world/latent marginals recovered as `.fst`/`.snd`.

A prediction about a model is stated in the `*_prefers_iff` vocabulary, each of
which is a thin wrapper over a decomposition lemma from `Core/Probability`
(`PMF.softmax_lt_iff_score_lt`, `PMF.posterior_fst_lt_iff`): the partition
function and the marginal cancel, leaving a comparison of pre-normalisation
scores.

## Main definitions

* `RSA.Canonical.rsaUtility` — the utility `α · (log L0 − cost)`, EReal-valued so
  an inapplicable utterance (`L0 = 0`, hence `log = ⊥`) gets softmax weight `0`.
* `RSA.Canonical.S1` — pragmatic speaker, `PMF.softmax` of `rsaUtility`.
* `RSA.Canonical.L1` — pragmatic listener, joint `PMF.posterior` over `world × latent`.

## Main statements

* `RSA.Canonical.S1_utterance_prefers_iff` — speaker preference between utterances
  reduces to comparing their utilities.
* `RSA.Canonical.L1_world_prefers_iff` / `L1_latent_prefers_iff` — listener marginal
  preference reduces to comparing conditional-joint sums.

## Implementation notes

Positivity hypotheses (`h_no_top`, `h_some_finite`, `marginal ≠ 0`) are threaded
explicitly. A covering-style typeclass discharging them as instances is deferred.
The rpow speaker `RSA.S1Belief` is the cost-free log special case of `S1`
(bridge: `PMF.softmaxWeight_natMul_log_eq_pow`).
-/

set_option autoImplicit false

namespace RSA.Canonical

open scoped ENNReal

/-! ### Pragmatic speaker -/

section Speaker

variable {W Lat U : Type*} [Fintype U]

/-- RSA utility of utterance `u` at joint state `s = (world, latent)`:
`α · (log L0(u | s) − cost u)`. EReal-valued, so an inapplicable utterance
(`L0 = 0 ⇒ log = ⊥`) receives softmax weight `EReal.exp ⊥ = 0`. -/
noncomputable def rsaUtility (L0 : U → W × Lat → ℝ≥0∞) (cost : U → ℝ) (α : ℝ)
    (s : W × Lat) (u : U) : EReal :=
  (α : EReal) * (ENNReal.log (L0 u s) - (cost u : EReal))

/-- The **canonical pragmatic speaker** at state `s`: the softmax of `rsaUtility`.
This is the single speaker the library instantiates; `RSA.S1Belief`'s rpow form
is its cost-free log special case. -/
noncomputable def S1 (L0 : U → W × Lat → ℝ≥0∞) (cost : U → ℝ) (α : ℝ) (s : W × Lat)
    (h_no_top : ∀ u, rsaUtility L0 cost α s u ≠ ⊤)
    (h_some_finite : ∃ u, rsaUtility L0 cost α s u ≠ ⊥) : PMF U :=
  PMF.softmax (rsaUtility L0 cost α s) h_no_top h_some_finite

/-- **Cross-utterance prediction**: at state `s` the speaker prefers `u₂` to `u₁`
iff `u₂` has the higher RSA utility. The partition function cancels. -/
theorem S1_utterance_prefers_iff (L0 : U → W × Lat → ℝ≥0∞) (cost : U → ℝ) (α : ℝ)
    (s : W × Lat) (h_no_top : ∀ u, rsaUtility L0 cost α s u ≠ ⊤)
    (h_some_finite : ∃ u, rsaUtility L0 cost α s u ≠ ⊥) (u₁ u₂ : U) :
    S1 L0 cost α s h_no_top h_some_finite u₁ < S1 L0 cost α s h_no_top h_some_finite u₂
      ↔ rsaUtility L0 cost α s u₁ < rsaUtility L0 cost α s u₂ :=
  PMF.softmax_lt_iff_score_lt (rsaUtility L0 cost α s) h_no_top h_some_finite u₁ u₂

/-- `≤` companion of `S1_utterance_prefers_iff`. -/
theorem S1_utterance_prefers_le_iff (L0 : U → W × Lat → ℝ≥0∞) (cost : U → ℝ) (α : ℝ)
    (s : W × Lat) (h_no_top : ∀ u, rsaUtility L0 cost α s u ≠ ⊤)
    (h_some_finite : ∃ u, rsaUtility L0 cost α s u ≠ ⊥) (u₁ u₂ : U) :
    S1 L0 cost α s h_no_top h_some_finite u₁ ≤ S1 L0 cost α s h_no_top h_some_finite u₂
      ↔ rsaUtility L0 cost α s u₁ ≤ rsaUtility L0 cost α s u₂ :=
  PMF.softmax_le_iff_score_le (rsaUtility L0 cost α s) h_no_top h_some_finite u₁ u₂

end Speaker

/-! ### Pragmatic listener -/

section Listener

variable {W Lat U : Type*} [Fintype W] [Fintype Lat]

/-- The **canonical pragmatic listener**: the joint Bayesian posterior over
`world × latent` given the observed utterance `u`. World and latent marginals
are `.fst` and `.snd`. -/
noncomputable def L1 (S : W × Lat → PMF U) (joint : PMF (W × Lat)) (u : U)
    (h : PMF.marginal S joint u ≠ 0) : PMF (W × Lat) :=
  PMF.posterior S joint u h

/-- **Cross-world prediction**: marginalising the latent, `L1` favours world `w₂`
over `w₁` iff the conditional-joint sums favour it. -/
theorem L1_world_prefers_iff [DecidableEq W] (S : W × Lat → PMF U) (joint : PMF (W × Lat))
    (u : U) (h : PMF.marginal S joint u ≠ 0) (w₁ w₂ : W) :
    (L1 S joint u h).fst w₁ < (L1 S joint u h).fst w₂
      ↔ (∑ l : Lat, joint (w₁, l) * S (w₁, l) u)
          < ∑ l : Lat, joint (w₂, l) * S (w₂, l) u :=
  PMF.posterior_fst_lt_iff S joint u h w₁ w₂

/-- `≤` companion of `L1_world_prefers_iff`. -/
theorem L1_world_prefers_le_iff [DecidableEq W] (S : W × Lat → PMF U)
    (joint : PMF (W × Lat)) (u : U) (h : PMF.marginal S joint u ≠ 0) (w₁ w₂ : W) :
    (L1 S joint u h).fst w₁ ≤ (L1 S joint u h).fst w₂
      ↔ (∑ l : Lat, joint (w₁, l) * S (w₁, l) u)
          ≤ ∑ l : Lat, joint (w₂, l) * S (w₂, l) u :=
  PMF.posterior_fst_le_iff S joint u h w₁ w₂

/-- **Cross-latent prediction**: marginalising the world, `L1` favours latent `l₂`
over `l₁` iff the conditional-joint sums favour it. -/
theorem L1_latent_prefers_iff [DecidableEq Lat] (S : W × Lat → PMF U)
    (joint : PMF (W × Lat)) (u : U) (h : PMF.marginal S joint u ≠ 0) (l₁ l₂ : Lat) :
    (L1 S joint u h).snd l₁ < (L1 S joint u h).snd l₂
      ↔ (∑ w : W, joint (w, l₁) * S (w, l₁) u)
          < ∑ w : W, joint (w, l₂) * S (w, l₂) u :=
  PMF.posterior_snd_lt_iff S joint u h l₁ l₂

end Listener

end RSA.Canonical
