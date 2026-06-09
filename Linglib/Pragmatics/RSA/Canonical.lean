import Linglib.Core.Probability.Softmax
import Linglib.Core.Probability.JointPosterior
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Canonical RSA pipeline

The single `L0 → S1 → L1` pipeline for Rational Speech Act models
[frank-goodman-2012] [degen-2023], built directly on the `Core/Probability`
shell with no bundled configuration.

The pragmatic speaker `S1` is the softmax of a *utility* `score : St → U → EReal`
mapping a speaker state (a world, or a `world × latent` pair) to a per-utterance
utility; an utterance is inapplicable exactly when its utility is `⊥` (softmax
weight `0`). The standard informativity utility is `rsaUtility = α·(log L0 − cost)`,
but any utility plugs in the same way — action-utility ([hawkins-etal-2025]) and
belief-utility speakers included. The pragmatic listener `L1` is the joint
Bayesian posterior over `world × latent`, with marginals `.fst`/`.snd`.

Positivity is supplied once as a `ViableSpeaker` instance (no utterance has
infinite utility; every state has an applicable utterance), so per-paper speakers
carry no `tsum ≠ 0 / ≠ ⊤` plumbing.

A prediction is stated in the `*_prefers_iff` vocabulary, each a one-line wrapper
over a `Core/Probability` decomposition lemma (`PMF.softmax_lt_iff_score_lt`,
`PMF.posterior_fst_lt_iff`): the partition and the marginal cancel, leaving a
comparison of utilities / conditional-joint sums.

## Main definitions

* `RSA.Canonical.ViableSpeaker` — positivity mixin discharging the softmax obligations.
* `RSA.Canonical.S1` — pragmatic speaker, `PMF.softmax` of a viable utility.
* `RSA.Canonical.rsaUtility` — the standard informativity utility `α·(log L0 − cost)`.
* `RSA.Canonical.L1` — pragmatic listener, joint `PMF.posterior` over `world × latent`.

## Main statements

* `RSA.Canonical.S1_prefers_iff` — speaker preference ↔ utility comparison.
* `RSA.Canonical.L1_world_prefers_iff` / `L1_latent_prefers_iff` — listener marginal
  preference ↔ conditional-joint-sum comparison.

## Implementation notes

Non-latent models take `St = W` and use the foundation `PMF.posterior_lt_iff_score_lt`
directly (the `latent = Unit` collapse). The `IsCovering ⇒ ViableSpeaker (rsaUtility …)`
bridge for standard informativity speakers is added when first needed.
-/

set_option autoImplicit false

namespace RSA.Canonical

open scoped ENNReal

/-! ### Pragmatic speaker -/

section Speaker

variable {St U : Type*} [Fintype U]

/-- A speaker utility `score : St → U → EReal` is **viable** when no utterance has
infinite utility and every state has at least one finite-utility (applicable)
utterance — precisely the conditions under which the softmax speaker is
well-defined. Supplied as an instance, it discharges the `PMF.softmax` positivity
obligations so per-paper speakers need no explicit `tsum`-positivity plumbing. -/
class ViableSpeaker (score : St → U → EReal) : Prop where
  /-- No utterance has `+∞` utility. -/
  no_top : ∀ s u, score s u ≠ ⊤
  /-- Every state has at least one applicable (finite-utility) utterance. -/
  some_finite : ∀ s, ∃ u, score s u ≠ ⊥

/-- The **canonical pragmatic speaker** at state `s`: the softmax of a viable
utility. The single speaker the library instantiates; the standard informativity
form is `rsaUtility`, while action/belief-utility speakers supply their own `score`. -/
noncomputable def S1 (score : St → U → EReal) [ViableSpeaker score] (s : St) : PMF U :=
  PMF.softmax (score s) (ViableSpeaker.no_top s) (ViableSpeaker.some_finite s)

/-- **Cross-utterance prediction**: the speaker prefers `u₂` to `u₁` at state `s`
iff `u₂` has the higher utility. The partition function cancels. -/
theorem S1_prefers_iff (score : St → U → EReal) [ViableSpeaker score] (s : St) (u₁ u₂ : U) :
    S1 score s u₁ < S1 score s u₂ ↔ score s u₁ < score s u₂ :=
  PMF.softmax_lt_iff_score_lt (score s) (ViableSpeaker.no_top s) (ViableSpeaker.some_finite s) u₁ u₂

/-- `≤` companion of `S1_prefers_iff`. -/
theorem S1_prefers_le_iff (score : St → U → EReal) [ViableSpeaker score] (s : St) (u₁ u₂ : U) :
    S1 score s u₁ ≤ S1 score s u₂ ↔ score s u₁ ≤ score s u₂ :=
  PMF.softmax_le_iff_score_le (score s) (ViableSpeaker.no_top s) (ViableSpeaker.some_finite s) u₁ u₂

/-- The speaker assigns positive probability to any applicable (finite-utility)
utterance — the witness for discharging `L1` marginal positivity. -/
theorem S1_ne_zero (score : St → U → EReal) [ViableSpeaker score] {s : St} {u : U}
    (h : score s u ≠ ⊥) : S1 score s u ≠ 0 :=
  ((PMF.softmax_pos_iff_score_ne_bot (score s)
    (ViableSpeaker.no_top s) (ViableSpeaker.some_finite s) u).mpr h).ne'

end Speaker

/-! ### Standard informativity utility -/

section StandardSpeaker

variable {W U : Type*}

/-- The **standard informativity utility** `α·(log L0(u | w) − cost u)`, EReal-valued
so an inapplicable utterance (`L0 = 0 ⇒ log = ⊥`) is `⊥` (softmax weight `0`).
Plug into `S1`; the rpow speaker `RSA.S1Belief` is the cost-free case. -/
noncomputable def rsaUtility (L0 : W → U → ℝ≥0∞) (cost : U → ℝ) (α : ℝ)
    (w : W) (u : U) : EReal :=
  (α : EReal) * (ENNReal.log (L0 w u) - (cost u : EReal))

end StandardSpeaker

/-! ### Pragmatic listener -/

section Listener

variable {W Lat U : Type*} [Fintype W] [Fintype Lat]

/-- The **canonical pragmatic listener**: the joint Bayesian posterior over
`world × latent` given the observed utterance `u`. World/latent marginals are
`.fst`/`.snd`. -/
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
