import Linglib.Theories.Semantics.Degree.Core
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Core.Softmax.Limits
import Linglib.Phenomena.Generics.Data
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# @cite{tessler-goodman-2019}: The Language of Generalization
@cite{tessler-goodman-2019} @cite{lassiter-goodman-2017}

Psychological Review, 126(3), 395–436.

## Core Insight

Generics ("Robins lay eggs") use the SAME uncertain threshold semantics
as gradable adjectives. The scale is **prevalence** rather than height/degree:

    ⟦gen⟧(p, θ) = 1 if prevalence p > threshold θ

This IS `positiveMeaning` from `Semantics.Degree` — the generic meaning is
grounded in scalar adjective semantics by construction, not by bridge theorem.

## Model

**Interpretation model** (L0, Eq. 1):
    L(p, θ | u) ∝ δ_{⟦u⟧(p,θ)} · P(θ) · P(p)

**Endorsement model** (S1, Eq. 3):
    S(u | p) ∝ (∫_θ L(p, θ | u) dθ)^λ

The threshold θ is marginalized BEFORE exponentiation (matching the paper).
With N discrete thresholds, the marginalized L0 is:
    L0(p | generic) ∝ P(p) · |{θ : p > θ}| = P(p) · p.toNat

This analytical marginalization eliminates the latent variable entirely,
so the RSAConfig has `Latent = Unit`. S1 then exponentiates the
marginalized L0, exactly matching the paper's endorsement model.

## Parameters

All parameters from the paper's code (`analysis/model-simulations.Rmd`,
`exampleParameters` list, GitHub: `mhtess/genlang-paper`):

- **α = 2** in the paper (experimental fit: 2.47). We use α = 1 since the
  binary comparison S1(generic) > S1(silent) is α-invariant for α > 0
- **Bins**: paper uses 98 bins (0.01–0.98); we use 21 bins (0%, 5%, ..., 100%)
  for exact rational arithmetic. Qualitative predictions are preserved.
- **Null component**: Beta(1, 50)

| Property | Stable Beta | φ (mix) | Ref. prev. | Paper endorse |
|----------|-------------|---------|------------|---------------|
| bark | Beta(5,1) | 0.4 | 95% | 0.88 |
| hasSpots | Beta(5,1) | 0.7 | 10% | 0.02 |
| dontEatPeople | Beta(10,1)* | 1.0 | 80% | 0.41 |
| laysEggs | Beta(10,10) | 0.2 | 50% | 0.95 |
| isFemale | Beta(10,10) | 1.0 | 50% | 0.50 |
| carriesMalaria | Beta(1,30) | 0.1 | 10% | 0.97 |

*Paper uses Beta(50,1); we use Beta(10,1) for tractable arithmetic
 (avoids k^49 terms). Both give the same qualitative prediction.

## Prior Model

Prevalence priors are **mixtures of two Beta distributions** (Figure 2):
    P(p) = φ · Beta_stable(p) / Z_s + (1-φ) · Beta_null(p) / Z_n

where φ is the probability a category has the stable causal mechanism,
Beta_stable varies per property, and Beta_null = Beta(1,50) for all
properties (representing categories lacking the property mechanism).

Each component is NORMALIZED before mixing (matching the WebPPL code,
which uses `categorical` to normalize each component independently).
We achieve this without ℚ division by computing:
    P(p) ∝ φ · BW_s(p) · Z_n + (1-φ) · BW_n(p) · Z_s

## Verified Predictions

| # | Finding | Prior | p_ref | Theorem |
|---|---------|-------|-------|---------|
| 1 | "Dogs bark" endorsed | bark | 95% | `bark_endorsed` |
| 2 | "Kangaroos have spots" NOT endorsed | hasSpots | 10% | `spots_not_endorsed` |
| 3 | "Sharks don't eat people" NOT endorsed | dontEatPeople | 80% | `dontEatPeople_not_endorsed` |
| 4 | "Robins lay eggs" endorsed despite 50% | laysEggs | 50% | `laysEggs_endorsed` |
| 5 | "Robins are female" borderline at 50% | isFemale | 50% | `isFemale_borderline` |
| 6 | "Mosquitos carry malaria" endorsed at 10% | carriesMalaria | 10% | `malaria_endorsed` |
| 7 | Max prevalence satisfies all thresholds | — | — | `generic_top_true` |
| 8 | Zero prevalence fails all thresholds | — | — | `generic_zero_false` |
-/

set_option autoImplicit false

namespace Phenomena.Generics.Studies.TesslerGoodman2019

open Core.Scale (Degree Threshold deg thr allDegrees allThresholds
  Degree.toNat Threshold.toNat)
open Semantics.Degree (positiveMeaning)

-- ============================================================================
-- § 1. Domain Types (reusing Core.Scale — same types as LassiterGoodman2017)
-- ============================================================================

/-- Discretized prevalence: 0%, 5%, ..., 100% (21 values).
    Structurally identical to @cite{lassiter-goodman-2017}'s Height. -/
abbrev Prevalence := Degree 20

instance : NeZero (20 : Nat) := ⟨by omega⟩

/-- Threshold values θ₀–θ₁₉ (20 values). -/
abbrev GenThreshold := Threshold 20

/-- Prevalence at p% (bins at 5% increments, so p must be a multiple of 5).
    Uses a macro so the division is computed at elaboration time. -/
macro "prevPct" p:num : term => do
  let pVal := p.getNat
  let bin := pVal / 5
  `(deg $(Lean.Quote.quote bin))

/-- Threshold at t% (bins at 5% increments, so t must be a multiple of 5).
    Uses a macro so the division is computed at elaboration time. -/
macro "thrPct" t:num : term => do
  let tVal := t.getNat
  let bin := tVal / 5
  `(thr $(Lean.Quote.quote bin))

-- ============================================================================
-- § 2. Utterances
-- ============================================================================

/-- Generic vs null utterance. The endorsement model decides between
    producing the generalization and staying silent. -/
inductive Utterance where
  | generic  -- "Ks have property F"
  | silent   -- say nothing
  deriving Repr, DecidableEq, BEq, Fintype

-- ============================================================================
-- § 3. Semantics: Generic = Positive Threshold over Prevalence
-- ============================================================================

/-- ⟦gen⟧(p, θ) = p > θ.

    This IS `positiveMeaning` from `Semantics.Degree` — the generic meaning
    function is literally the positive scalar adjective meaning applied to the
    prevalence scale. Grounded by construction. -/
def genericMeaning (θ : GenThreshold) (p : Prevalence) : Bool :=
  positiveMeaning p θ

/-- Full meaning function: utterance × threshold → prevalence → Bool. -/
def meaning (u : Utterance) (θ : GenThreshold) (p : Prevalence) : Bool :=
  match u with
  | .generic => genericMeaning θ p
  | .silent => true

-- ============================================================================
-- § 4. Prevalence Priors — Normalized Mixture of Betas (Figure 2)
-- ============================================================================

/-! ### Mixture-of-Betas infrastructure

The paper models prevalence priors as mixtures of two Beta distributions:
a **stable** component (property-specific) and a **null** component
(Beta(1,50), representing categories without the causal mechanism).

Each component is normalized before mixing (matching the WebPPL code where
`categorical` normalizes each component independently). We achieve this
without ℚ division by computing:

    P(k) ∝ φ · BW_stable(k) · Z_null + (1-φ) · BW_null(k) · Z_stable

This is proportional to the correctly normalized mixture since:
    P(k) = Z_n · Z_s · [φ · BW_s(k)/Z_s + (1-φ) · BW_n(k)/Z_n] -/

/-- Unnormalized Beta(a,b) weight at bin k ∈ {0,...,20}.
    Proportional to Beta(a,b) PDF at x = k/20. -/
def betaWeight (a b k : Nat) : Nat :=
  k ^ (a - 1) * (20 - k) ^ (b - 1)

/-- Sum of Beta(a,b) weights across all 21 bins. -/
def betaTotal (a b : Nat) : Nat :=
  betaWeight a b 0 + betaWeight a b 1 + betaWeight a b 2 +
  betaWeight a b 3 + betaWeight a b 4 + betaWeight a b 5 +
  betaWeight a b 6 + betaWeight a b 7 + betaWeight a b 8 +
  betaWeight a b 9 + betaWeight a b 10 + betaWeight a b 11 +
  betaWeight a b 12 + betaWeight a b 13 + betaWeight a b 14 +
  betaWeight a b 15 + betaWeight a b 16 + betaWeight a b 17 +
  betaWeight a b 18 + betaWeight a b 19 + betaWeight a b 20

/-- Normalized mixture-of-Betas prevalence prior, discretized to 21 bins.

    - Stable component: Beta(as, bs) with mixture weight φ
    - Null component: Beta(na, nb) with mixture weight (1-φ)

    Each component is normalized before mixing by cross-multiplying
    with the other component's total weight:

        P(k) ∝ φ · BW_stable(k) · Z_null + (1-φ) · BW_null(k) · Z_stable

    This avoids ℚ division while preserving the correct mixture ratio. -/
def mixturePrior (phi : ℚ) (as bs na nb : Nat) (p : Prevalence) : ℚ :=
  let k := p.toNat
  let stableW : ℚ := betaWeight as bs k
  let nullW : ℚ := betaWeight na nb k
  let stableZ : ℚ := betaTotal as bs
  let nullZ : ℚ := betaTotal na nb
  phi * stableW * nullZ + (1 - phi) * nullW * stableZ

-- Null component parameters (same for all properties)
-- Paper's WebPPL: Beta({a:1, b:50})

/-- "Bark" prior: bimodal at 0 and ~90% (Figure 2, column 1).
    Stable Beta(5,1), φ = 0.4. -/
def barkPrior : Prevalence → ℚ := mixturePrior (2/5) 5 1 1 50

/-- "Have spots" prior: bimodal at 0 and ~90% (Figure 2, column 2).
    Stable Beta(5,1), φ = 0.7. Higher φ than bark — more animal
    categories can have spots than bark. -/
def haveSpotsPrior : Prevalence → ℚ := mixturePrior (7/10) 5 1 1 50

/-- "Don't eat people" prior: near-unimodal at ~90% (Figure 2, column 3).
    Stable Beta(10,1), φ = 1.0.
    Paper uses Beta(50,1); we use Beta(10,1) for tractable arithmetic
    (avoids k^49 terms). Both predict NOT endorsed at 80%. -/
def dontEatPeoplePrior : Prevalence → ℚ := mixturePrior 1 10 1 1 50

/-- "Lays eggs" prior: bimodal at 0 and ~50% (Figure 2, column 4).
    Stable Beta(10,10), φ = 0.2.
    Most animal categories don't have egg-layers (peak at 0);
    among those that do, only females lay eggs (~50% prevalence). -/
def laysEggsPrior : Prevalence → ℚ := mixturePrior (1/5) 10 10 1 50

/-- "Is female" prior: unimodal at ~50% (Figure 2, column 5).
    Stable Beta(10,10), φ = 1.0.
    Almost all animal categories have ~50% female members. -/
def isFemalePrior : Prevalence → ℚ := mixturePrior 1 10 10 1 50

/-- "Carries malaria" prior: extreme low prevalence (Figure 2, column 6).
    Stable Beta(1,30), φ = 0.1.
    Very few animal categories carry diseases (90% null component).
    Among those that do, prevalence is very low (Beta(1,30) peaked near 0). -/
def carriesMalariaPrior : Prevalence → ℚ := mixturePrior (1/10) 1 30 1 50

-- ============================================================================
-- § 5. RSAConfig — Marginalized Threshold Model
-- ============================================================================

open Real (rpow rpow_nonneg)

/-- Cast a ℚ-valued prior to ℝ. -/
noncomputable def priorR (prior : Prevalence → ℚ) (p : Prevalence) : ℝ :=
  (prior p : ℝ)

private theorem mixturePrior_nonneg (phi : ℚ) (hphi : 0 ≤ phi) (hphi1 : phi ≤ 1)
    (as bs na nb : Nat) :
    ∀ p : Prevalence, 0 ≤ mixturePrior phi as bs na nb p := by
  intro p
  simp only [mixturePrior]
  apply add_nonneg
  · apply mul_nonneg
    apply mul_nonneg hphi
    exact_mod_cast Nat.zero_le _
    exact_mod_cast Nat.zero_le _
  · apply mul_nonneg
    apply mul_nonneg (by linarith)
    exact_mod_cast Nat.zero_le _
    exact_mod_cast Nat.zero_le _

private theorem priorR_nonneg_of (prior : Prevalence → ℚ)
    (h : ∀ p : Prevalence, 0 ≤ prior p) :
    ∀ p : Prevalence, 0 ≤ priorR prior p := by
  intro p; simp only [priorR]; exact_mod_cast h p

/-- Number of thresholds θ ∈ {0,...,19} satisfying p > θ.

    For generic: count = p.toNat (0 for p=0, 1 for p=1, ..., 20 for p=20).
    For silence: count = 20 (all thresholds pass). -/
def thresholdCount (u : Utterance) (p : Prevalence) : Nat :=
  match u with
  | .generic => p.toNat
  | .silent => 20

/-- Parametric RSAConfig for threshold-based generic endorsement.

    The threshold θ is marginalized analytically into the meaning function:
    meaning(u, p) = P(p) · |{θ : ⟦u⟧(p,θ) = true}|

    This matches the paper's endorsement model structure (Eq. 3):
    S(u | p) ∝ (∫_θ L(p, θ | u) dθ)^λ

    The marginalization happens BEFORE exponentiation (matching the paper),
    not after (as would happen with θ as a latent variable in RSAConfig).
    With `Latent = Unit`, S1 scores the marginalized L0 directly.

    The paper uses α = 2 (experimental fit: 2.47), but the binary comparison
    S1(generic) > S1(silent) is α-invariant for any α > 0, since
    rpow preserves order. We use α = 1 for tractable interval arithmetic. -/
@[reducible]
noncomputable def mkGenericCfg
    (prior : Prevalence → ℝ) (hp : ∀ p, 0 ≤ prior p) :
    RSA.RSAConfig Utterance Prevalence where
  meaning _ _ u p := prior p * thresholdCount u p
  meaning_nonneg _ _ u p := mul_nonneg (hp p) (Nat.cast_nonneg _)
  s1Score l0 α _ w u := rpow (l0 u w) α
  s1Score_nonneg _ _ _ _ _ hl _ := rpow_nonneg (hl _ _) _
  α := 1
  α_pos := one_pos
  worldPrior := prior
  worldPrior_nonneg := hp
  latentPrior_nonneg _ _ := by positivity

-- ============================================================================
-- § 5a. Concrete Configs per Property
-- ============================================================================

private theorem barkPrior_nonneg : ∀ p : Prevalence, 0 ≤ barkPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _

private theorem haveSpotsPrior_nonneg : ∀ p : Prevalence, 0 ≤ haveSpotsPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _

private theorem dontEatPeoplePrior_nonneg : ∀ p : Prevalence, 0 ≤ dontEatPeoplePrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _

private theorem laysEggsPrior_nonneg : ∀ p : Prevalence, 0 ≤ laysEggsPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _

private theorem isFemalePrior_nonneg : ∀ p : Prevalence, 0 ≤ isFemalePrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _

private theorem carriesMalariaPrior_nonneg : ∀ p : Prevalence, 0 ≤ carriesMalariaPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _

/-- "Bark" config: peaked high prior (Figure 2, column 1). -/
@[reducible]
noncomputable def barkCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR barkPrior) (priorR_nonneg_of _ barkPrior_nonneg)

/-- "Have spots" config: peaked high prior (Figure 2, column 2). -/
@[reducible]
noncomputable def haveSpotsCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR haveSpotsPrior) (priorR_nonneg_of _ haveSpotsPrior_nonneg)

/-- "Don't eat people" config: peaked very high prior (Figure 2, column 3). -/
@[reducible]
noncomputable def dontEatPeopleCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR dontEatPeoplePrior) (priorR_nonneg_of _ dontEatPeoplePrior_nonneg)

/-- "Lays eggs" config: bimodal prior (Figure 2, column 4). -/
@[reducible]
noncomputable def laysEggsCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR laysEggsPrior) (priorR_nonneg_of _ laysEggsPrior_nonneg)

/-- "Is female" config: unimodal prior at 50% (Figure 2, column 5). -/
@[reducible]
noncomputable def isFemaleCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR isFemalePrior) (priorR_nonneg_of _ isFemalePrior_nonneg)

/-- "Carries malaria" config: extreme low prior (Figure 2, column 6). -/
@[reducible]
noncomputable def malariaCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR carriesMalariaPrior) (priorR_nonneg_of _ carriesMalariaPrior_nonneg)

-- ============================================================================
-- § 6. Semantic Properties
-- ============================================================================

/-- Prevalence 100% satisfies the generic for all thresholds. -/
theorem generic_top_true :
    ∀ θ : GenThreshold, genericMeaning θ (prevPct 100) = true := by
  native_decide

/-- Generic meaning at prevalence 0% is false for all thresholds. -/
theorem generic_zero_false :
    ∀ θ : GenThreshold, genericMeaning θ (prevPct 0) = false := by
  native_decide

/-- The bimodal "lays eggs" prior peaks at zero prevalence. -/
theorem laysEggs_peaks_at_zero :
    laysEggsPrior (prevPct 0) > laysEggsPrior (prevPct 50) := by native_decide

/-- The unimodal "is female" prior peaks at 50%. -/
theorem isFemale_peaks_at_50 :
    isFemalePrior (prevPct 50) > isFemalePrior (prevPct 0) := by native_decide

-- ============================================================================
-- § 7. Endorsement Predictions (S1 — the paper's primary model)
-- ============================================================================

/-! ### Endorsement model (Eq. 3)

The paper's key predictions are endorsement rates: given referent prevalence
p for a kind k, does the speaker produce the generic?

    S(u | p) ∝ (∫_θ L(p,θ|u) dθ)^λ

Endorsement > 50% ⟺ S1(generic | p) > S1(silent | p).

The binary comparison is equivalent to tc(p) > E[tc | prior], i.e.,
the referent prevalence (in threshold-count units) exceeds the prior
expected prevalence. This is the paper's central insight: the SAME
prevalence can produce different endorsement rates depending on the
prior (Figure 2). -/

/-- "Dogs bark" endorsed at 95% prevalence (Table 1: 95%; Figure 2, column 1: 0.88). -/
theorem bark_endorsed :
    barkCfg.S1 () (prevPct 95) .generic > barkCfg.S1 () (prevPct 95) .silent := by
  rsa_predict

/-- "Robins lay eggs" endorsed at 50% prevalence (Figure 2, column 4: 0.95).
    Despite only 50% prevalence, the bimodal prior (peaked at 0 and 50%)
    makes the generic highly informative — it rules out the absent component. -/
theorem laysEggs_endorsed :
    laysEggsCfg.S1 () (prevPct 50) .generic > laysEggsCfg.S1 () (prevPct 50) .silent := by
  rsa_predict

/-- "Mosquitos carry malaria" endorsed at 10% prevalence (Figure 2, column 6: 0.97).
    The prior expects near-zero prevalence, so even low prevalence is
    highly informative. This is the model's explanation of "striking property"
    generics: rare properties have low prior expectations. -/
theorem malaria_endorsed :
    malariaCfg.S1 () (prevPct 10) .generic > malariaCfg.S1 () (prevPct 10) .silent := by
  rsa_predict

/-- "Kangaroos have spots" NOT endorsed at 10% prevalence (Figure 2, column 2: 0.02).
    Even though the prior has a null component, φ = 0.7 means 70% of the prior
    mass comes from the stable Beta(5,1) peaked near 100%. At 10% prevalence,
    the generic is uninformative relative to this high-prevalence expectation. -/
theorem spots_not_endorsed :
    ¬(haveSpotsCfg.S1 () (prevPct 10) .generic > haveSpotsCfg.S1 () (prevPct 10) .silent) := by
  rsa_predict

/-- "Sharks don't eat people" NOT endorsed at 80% prevalence (Figure 2, column 3: 0.41).
    Even though 80% is high in absolute terms, the prior (φ=1, Beta(10,1))
    concentrates nearly all mass above 80%. The generic is uninformative
    because the listener already expects very high prevalence. -/
theorem dontEatPeople_not_endorsed :
    ¬(dontEatPeopleCfg.S1 () (prevPct 80) .generic > dontEatPeopleCfg.S1 () (prevPct 80) .silent) := by
  rsa_predict

/-- "Robins are female" borderline at 50% prevalence (Figure 2, column 5: 0.50).
    The unimodal prior peaks at 50% with φ = 1.0, so the prior expected
    prevalence is exactly 50%. At the referent prevalence of 50%, the generic
    is exactly as informative as silence — endorsement is 0.5. -/
theorem isFemale_borderline :
    ¬(isFemaleCfg.S1 () (prevPct 50) .generic > isFemaleCfg.S1 () (prevPct 50) .silent) := by
  rsa_predict

-- ============================================================================
-- § 8. Connection to Phenomena.Generics.Data
-- ============================================================================

/-! The prevalence asymmetry from `Phenomena.Generics.Data` is EXPLAINED
by the endorsement model: same prevalence (50%), different prior shapes →
different S1 endorsement rates.

`laysEggsVsIsFemale` records the empirical observation.
`laysEggs_endorsed` and `isFemale_borderline` derive the predictions. -/

/-- The data records 50% prevalence for both "lay eggs" and "is female". -/
theorem asymmetry_same_prevalence :
    Phenomena.Generics.laysEggsVsIsFemale.prevalence = 1/2 := rfl

-- ============================================================================
-- § 9. Infinite-Rationality Limit: Generics as Categorical Defaults
-- ============================================================================

/-! As α → ∞, the endorsement model sharpens to a categorical decision:
    endorsed generics get probability 1, non-endorsed get probability 0.

    By `rpow_luce_eq_softmax` (Core), every rpow-based Luce choice rule IS
    softmax over log scores. The endorsement model inherits all softmax
    limit theorems for free. -/

open Core Real BigOperators Finset Filter Topology

instance : Nonempty Utterance := ⟨.generic⟩

/-- L0 score for utterance u at prevalence p (unnormalized). -/
noncomputable def l0Score (prior : Prevalence → ℝ) (u : Utterance) (p : Prevalence) : ℝ :=
  prior p * (thresholdCount u p : ℝ)

/-- The endorsement rate equals softmax over log-L0 scores.
    Immediate from `rpow_luce_eq_softmax`: the endorsement model IS softmax. -/
theorem endorsement_eq_softmax (prior : Prevalence → ℝ) (p : Prevalence) (α : ℝ)
    (hl0 : ∀ u, 0 < l0Score prior u p) :
    (l0Score prior .generic p) ^ α / ∑ u : Utterance, (l0Score prior u p) ^ α =
    softmax (fun u : Utterance => log (l0Score prior u p)) α .generic :=
  rpow_luce_eq_softmax (fun u => l0Score prior u p) α hl0 .generic

/-- When l0_gen > l0_sil (endorsed generic), the endorsement rate → 1
    as α → ∞. Direct corollary of `Softmax.tendsto_softmax_infty_at_max`. -/
theorem endorsement_tendsto_one (prior : Prevalence → ℝ) (p : Prevalence)
    (hs : 0 < l0Score prior .silent p)
    (h : l0Score prior .silent p < l0Score prior .generic p) :
    Tendsto (fun α => softmax (fun u : Utterance => log (l0Score prior u p)) α .generic)
      atTop (nhds 1) := by
  apply Softmax.tendsto_softmax_infty_at_max
  intro j hj
  cases j with
  | generic => exact absurd rfl hj
  | silent => exact Real.log_lt_log hs h

/-- When l0_gen < l0_sil (non-endorsed generic), the endorsement rate → 0. -/
theorem endorsement_tendsto_zero (prior : Prevalence → ℝ) (p : Prevalence)
    (hg : 0 < l0Score prior .generic p)
    (h : l0Score prior .generic p < l0Score prior .silent p) :
    Tendsto (fun α => softmax (fun u : Utterance => log (l0Score prior u p)) α .generic)
      atTop (nhds 0) := by
  have hlim := Softmax.tendsto_softmax_infty_unique_max
    (fun u : Utterance => log (l0Score prior u p)) .silent
    (by intro j hj; cases j with
      | generic => exact Real.log_lt_log hg h
      | silent => exact absurd rfl hj) .generic
  simp only [show Utterance.generic = Utterance.silent ↔ False from by decide,
    ite_false] at hlim
  exact hlim

-- ════════════════════════════════════════════════════════════════════════════════
-- § 10. Case Study 2: Habitual Language
-- ════════════════════════════════════════════════════════════════════════════════

/-!
## Case Study 2: Habitual Language

@cite{tessler-goodman-2019} (Case Study 2) extend the generic endorsement model
to habituals. The key insight: habituals ("John runs") use the **same** threshold
semantics as generics ("Birds fly"), with `Prevalence` now interpreted as frequency
of activity across occasions rather than proportion of a kind with a property.

**Paper's actual prior model (Eq. 4)**: The paper uses a log-normal + delta mixture:

    φ ~ Beta(γ, ξ)
    ln(frequency) ~ Gaussian(μ, σ)  with probability φ
    frequency = 0.01               with probability (1 - φ)

The Beta parameters (γ, ξ) and Gaussian parameters (μ, σ) are fit to empirical
frequency estimates from participants. We approximate the fitted priors with
Beta mixtures that capture the qualitative predictions:

- **Rare-activity priors** (e.g., "climbs mountains", "writes novels"):
  most people never do this → low expected frequency
- **High-frequency priors** (e.g., "drinks coffee", "drives to work"):
  common daily activity → high expected frequency
- **Moderate priors** (e.g., "runs", "cooks dinner"):
  regular but not constant

The paper reports a model fit of r²(93) = 0.894 on habitual endorsement data.

See also: `Semantics.Lexical.Verb.Habituals.hab_reduces_to_threshold` for
the formal bridge from the traditional HAB operator to threshold semantics,
completing the pipeline: HAB → threshold → uncertain threshold → RSA endorsement.
-/

/-- Frequency prior for "runs": moderate expectation.
    Approximates the paper's fitted log-normal prior with a Beta(5,3) mixture.
    The paper fits (γ, ξ, μ, σ) to participant frequency estimates;
    the exact fitted values are in `analysis/model-simulations.Rmd`. -/
def runsPrior : Prevalence → ℚ := mixturePrior (1/2) 5 3 1 50

/-- Frequency prior for "climbs mountains": rare activity.
    Approximates the paper's fitted log-normal prior with a Beta(2,6) mixture. -/
def climbsMountainsPrior : Prevalence → ℚ := mixturePrior (1/10) 2 6 1 50

/-- Frequency prior for "drinks coffee": high-frequency activity.
    Approximates the paper's fitted log-normal prior with a Beta(7,2) mixture. -/
def drinksCoffeePrior : Prevalence → ℚ := mixturePrior (4/5) 7 2 1 50

private theorem runsPrior_nonneg : ∀ p : Prevalence, 0 ≤ runsPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _
private theorem climbsMountainsPrior_nonneg : ∀ p : Prevalence, 0 ≤ climbsMountainsPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _
private theorem drinksCoffeePrior_nonneg : ∀ p : Prevalence, 0 ≤ drinksCoffeePrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _

@[reducible]
noncomputable def runsCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR runsPrior) (priorR_nonneg_of _ runsPrior_nonneg)

@[reducible]
noncomputable def climbsMountainsCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR climbsMountainsPrior) (priorR_nonneg_of _ climbsMountainsPrior_nonneg)

@[reducible]
noncomputable def drinksCoffeeCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR drinksCoffeePrior) (priorR_nonneg_of _ drinksCoffeePrior_nonneg)

/-- "John runs" endorsed at 75% frequency (moderate freq exceeds moderate prior). -/
theorem runs_endorsed_at_high_freq :
    runsCfg.S1 () (prevPct 75) .generic > runsCfg.S1 () (prevPct 75) .silent := by
  rsa_predict

/-- "John climbs mountains" endorsed at 25% frequency (low freq exceeds rare-activity prior). -/
theorem climbs_mountains_endorsed_at_low_freq :
    climbsMountainsCfg.S1 () (prevPct 25) .generic >
    climbsMountainsCfg.S1 () (prevPct 25) .silent := by
  rsa_predict

/-- "John drinks coffee" NOT endorsed at 25% frequency (low freq below high-frequency prior). -/
theorem drinks_coffee_not_endorsed_at_low_freq :
    ¬(drinksCoffeeCfg.S1 () (prevPct 25) .generic >
      drinksCoffeeCfg.S1 () (prevPct 25) .silent) := by
  rsa_predict

/-- Habitual prior asymmetry: at the same 25% frequency, "climbs mountains" is endorsed
    but "drinks coffee" is not — paralleling the generic prevalence asymmetry. -/
theorem habitual_prior_asymmetry :
    (climbsMountainsCfg.S1 () (prevPct 25) .generic >
     climbsMountainsCfg.S1 () (prevPct 25) .silent) ∧
    ¬(drinksCoffeeCfg.S1 () (prevPct 25) .generic >
      drinksCoffeeCfg.S1 () (prevPct 25) .silent) :=
  ⟨climbs_mountains_endorsed_at_low_freq, drinks_coffee_not_endorsed_at_low_freq⟩

-- ════════════════════════════════════════════════════════════════════════════════
-- § 11. Case Study 3: Causal Language
-- ════════════════════════════════════════════════════════════════════════════════

/-!
## Case Study 3: Causal Language

@cite{tessler-goodman-2019} (Case Study 3, Experiment 3A) extend the model to
causal generics ("Zarpies cause fleas in Grups"). Here `Prevalence` is
reinterpreted as the causal rate — the proportion of cases where the cause
produces the effect.

**Experimental design (Experiment 3A)**: 2×2 between-subjects manipulation:

| Condition | Cause prevalence | Effect strength | Referent causal rate |
|-----------|-----------------|-----------------|---------------------|
| common-strong | 75% have mechanism | high rate given mechanism | tested at 20% and 70% |
| common-weak | 75% have mechanism | low rate given mechanism | tested at 20% and 70% |
| rare-strong | 25% have mechanism | high rate given mechanism | tested at 20% and 70% |
| rare-weak | 25% have mechanism | low rate given mechanism | tested at 20% and 70% |

The paper's key finding: endorsement depends on the **prior over causal rates**,
not just the referent rate itself. At the same referent rate, rare-cause conditions
show higher endorsement than common-cause conditions.

We model the four conditions as different prevalence priors, varying the mixture
weight φ (cause prevalence: common=high φ, rare=low φ) and the stable Beta
parameters (effect strength: strong → high-mean Beta, weak → low-mean Beta).

The paper reports a model fit of r²(8) = 0.835 on causal endorsement data.
-/

/-- Prior for common-strong cause: most categories have the mechanism (φ=0.75),
    and the mechanism is highly effective (Beta(10,1) peaked near 100%). -/
def commonStrongPrior : Prevalence → ℚ := mixturePrior (3/4) 10 1 1 50

/-- Prior for common-weak cause: most categories have the mechanism (φ=0.75),
    but the mechanism is weakly effective (Beta(2,8) peaked near 20%). -/
def commonWeakPrior : Prevalence → ℚ := mixturePrior (3/4) 2 8 1 50

/-- Prior for rare-strong cause: few categories have the mechanism (φ=0.25),
    but when present it is highly effective (Beta(10,1)). -/
def rareStrongPrior : Prevalence → ℚ := mixturePrior (1/4) 10 1 1 50

/-- Prior for rare-weak cause: few categories have the mechanism (φ=0.25),
    and the mechanism is weakly effective (Beta(2,8)). -/
def rareWeakPrior : Prevalence → ℚ := mixturePrior (1/4) 2 8 1 50

private theorem commonStrongPrior_nonneg : ∀ p : Prevalence, 0 ≤ commonStrongPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _
private theorem commonWeakPrior_nonneg : ∀ p : Prevalence, 0 ≤ commonWeakPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _
private theorem rareStrongPrior_nonneg : ∀ p : Prevalence, 0 ≤ rareStrongPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _
private theorem rareWeakPrior_nonneg : ∀ p : Prevalence, 0 ≤ rareWeakPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _

@[reducible]
noncomputable def commonStrongCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR commonStrongPrior) (priorR_nonneg_of _ commonStrongPrior_nonneg)

@[reducible]
noncomputable def commonWeakCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR commonWeakPrior) (priorR_nonneg_of _ commonWeakPrior_nonneg)

@[reducible]
noncomputable def rareStrongCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR rareStrongPrior) (priorR_nonneg_of _ rareStrongPrior_nonneg)

@[reducible]
noncomputable def rareWeakCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR rareWeakPrior) (priorR_nonneg_of _ rareWeakPrior_nonneg)

/-- Rare-weak cause endorsed at 20% causal rate: low prior expectation
    makes even 20% informative. -/
theorem rareWeak_endorsed_at_20pct :
    rareWeakCfg.S1 () (prevPct 20) .generic >
    rareWeakCfg.S1 () (prevPct 20) .silent := by
  rsa_predict

/-- Common-strong cause NOT endorsed at 20% causal rate: high prior
    expectation (peaked near 100%) makes 20% uninformative. -/
theorem commonStrong_not_endorsed_at_20pct :
    ¬(commonStrongCfg.S1 () (prevPct 20) .generic >
      commonStrongCfg.S1 () (prevPct 20) .silent) := by
  rsa_predict

/-- Rare-weak cause endorsed at 70% causal rate. -/
theorem rareWeak_endorsed_at_70pct :
    rareWeakCfg.S1 () (prevPct 70) .generic >
    rareWeakCfg.S1 () (prevPct 70) .silent := by
  rsa_predict

/-- Common-strong cause NOT endorsed at 50% causal rate: high prior
    (Beta(10,1), φ=0.75) puts expected rate near 70%, so 50% is uninformative. -/
theorem commonStrong_not_endorsed_at_50pct :
    ¬(commonStrongCfg.S1 () (prevPct 50) .generic >
      commonStrongCfg.S1 () (prevPct 50) .silent) := by
  rsa_predict

/-- Causal prior asymmetry (Experiment 3A): at the same referent causal rate,
    rare-cause conditions are endorsed while common-cause conditions are not. -/
theorem causal_prior_asymmetry :
    (rareWeakCfg.S1 () (prevPct 20) .generic >
     rareWeakCfg.S1 () (prevPct 20) .silent) ∧
    ¬(commonStrongCfg.S1 () (prevPct 20) .generic >
      commonStrongCfg.S1 () (prevPct 20) .silent) :=
  ⟨rareWeak_endorsed_at_20pct, commonStrong_not_endorsed_at_20pct⟩

-- ════════════════════════════════════════════════════════════════════════════════
-- § 12. Cue Validity ↔ Prevalence Prior (Appendix A)
-- ════════════════════════════════════════════════════════════════════════════════

/-!
## Cue Validity and Endorsement

@cite{tessler-goodman-2019} (pp. 29-30, Appendix A) show that endorsement in
the infinite-rationality limit reduces to a cue validity comparison:

    endorsed ⟺ prevalence(f, k_ref) > E_prior[prevalence]
             ⟺ cue_validity(f, k_ref) > 1

where `cue_validity(f, k) = prevalence(f, k) / E[prevalence]`.

This connects the RSA model to the classical notion from @cite{rosch-mervis-1975}:
a feature is diagnostic of a category exactly when the feature is more prevalent
in that category than expected across categories — i.e., when cue validity > 1.

In `mkGenericCfg`, the endorsement condition
`S1(generic | p_ref) > S1(silent | p_ref)` reduces to
`p_ref.toNat > E[k | prior]` after L0 normalization cancels the common factor.
This is exactly the cue validity condition when the expected bin E[k | prior]
serves as the denominator.
-/

/-- Cue validity: ratio of referent prevalence to expected prevalence under the prior. -/
def cueValidity (referentPrevalence expectedPrior : ℚ) : ℚ :=
  referentPrevalence / expectedPrior

/-- A generic is endorsed (prevalence exceeds prior expectation) iff cue validity > 1. -/
theorem endorsed_iff_cue_validity_gt_one
    (referentPrev expectedPrior : ℚ) (hE : 0 < expectedPrior) :
    expectedPrior < referentPrev ↔ 1 < cueValidity referentPrev expectedPrior := by
  unfold cueValidity
  exact (one_lt_div hE).symm

-- ════════════════════════════════════════════════════════════════════════════════
-- § 13. Unification: All Three Domains Use mkGenericCfg
-- ════════════════════════════════════════════════════════════════════════════════

/-!
## Unified Architecture

All three domains — generics, habituals, and causal language — are instances of
`mkGenericCfg` with different prevalence priors. The threshold semantics, RSA
inference, and endorsement mechanism are shared; only the prior varies.

This unification is structural (by construction), not proven post hoc.
The integration pipeline is:

1. **Traditional operator** (GEN/HAB) reduces to threshold semantics
   (`CompareSemantics.gen_eliminable`, `Habituals.hab_reduces_to_threshold`)
2. **Threshold semantics** with uncertain threshold → marginalized L0
3. **RSA endorsement** (`mkGenericCfg`) decides between generic and silence
4. **Endorsement ≈ cue validity** (`endorsed_iff_cue_validity_gt_one`)
-/

/-- All three case studies use `mkGenericCfg` — the prior is the only free parameter. -/
theorem unification :
    (∃ pr hp, barkCfg = mkGenericCfg pr hp) ∧
    (∃ pr hp, runsCfg = mkGenericCfg pr hp) ∧
    (∃ pr hp, rareWeakCfg = mkGenericCfg pr hp) :=
  ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩

end Phenomena.Generics.Studies.TesslerGoodman2019
