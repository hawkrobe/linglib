import Linglib.Theories.Semantics.Degree.Core
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
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

**Interpretation model** (L0):
    L(p, θ | u) ∝ δ_{⟦u⟧(p,θ)} · P(θ) · P(p)

**Endorsement model** (S1):
    S(u | p) ∝ (∫_θ L(p, θ | u) dθ)^λ

The threshold θ is marginalized BEFORE exponentiation (matching the paper).
With 10 discrete thresholds, the marginalized L0 is:
    L0(p | generic) ∝ P(p) · |{θ : p > θ}| = P(p) · p.toNat

This analytical marginalization eliminates the latent variable entirely,
so the RSAConfig has `Latent = Unit`. S1 then exponentiates the
marginalized L0, exactly matching the paper's endorsement model.

## Prior Model

Prevalence priors are **mixtures of two Beta distributions** (Figure 2):
    P(p) = φ · Beta(p; a_s, b_s) + (1-φ) · δ(p ≈ 0)

where φ is the probability a category has the stable causal mechanism,
and Beta(a_s, b_s) is the prevalence distribution when present. With
11-bin discretization, the transient Beta(1,99) concentrates >99.99%
of mass at bin 0, so we approximate it as a delta.

## Model Levels

The paper focuses on the **endorsement model** (S1, Eq. 3): given that a
speaker knows the referent prevalence p, do they produce the generic?

    S(u | p) ∝ (∫_θ L(p, θ | u) dθ)^λ

Footnote 6 gives a more general version where the speaker has uncertain
beliefs P_k over prevalence:

    S(u | k) ∝ exp(λ · E_{p∼P_k} ln ∫_θ L(p,θ|u) dθ)

The paper notes these "make almost identical predictions" for the case
studies. Our model implements Eq. 3 (speaker knows p). The L1 pragmatic
listener (Bayesian inversion of S1) goes one level beyond the paper.

## Verified Predictions

| # | Finding | Prior | p_ref | Theorem |
|---|---------|-------|-------|---------|
| 1 | "Dogs bark" endorsed | bark | 90% | `bark_endorsed` |
| 2 | "Robins lay eggs" endorsed despite 50% | laysEggs | 50% | `laysEggs_endorsed` |
| 3 | "Mosquitos carry malaria" endorsed despite ~1% | carriesMalaria | 10% | `malaria_endorsed` |
| 4 | "Robins are female" borderline at 50% | isFemale | 50% | `isFemale_endorsed` |
| 5 | "Kangaroos have spots" NOT endorsed at 0% | haveSpots | 0% | `spots_not_endorsed` |
| 6 | Max prevalence satisfies all thresholds | — | — | `generic_top_true` |
| 7 | Zero prevalence fails all thresholds | — | — | `generic_zero_false` |
-/

set_option autoImplicit false

namespace Phenomena.Generics.Studies.TesslerGoodman2019

open Core.Scale (Degree Threshold deg thr allDegrees allThresholds
  Degree.toNat Threshold.toNat)
open Semantics.Degree (positiveMeaning)

-- ============================================================================
-- § 1. Domain Types (reusing Core.Scale — same types as LassiterGoodman2017)
-- ============================================================================

/-- Discretized prevalence: 0%, 10%, ..., 100% (11 values).
    Structurally identical to @cite{lassiter-goodman-2017}'s Height. -/
abbrev Prevalence := Degree 10

instance : NeZero (10 : Nat) := ⟨by omega⟩

/-- Threshold values θ₀–θ₉ (10 values). -/
abbrev GenThreshold := Threshold 10

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
-- § 4. Prevalence Priors — Mixture of Betas (Figure 2)
-- ============================================================================

/-! ### Mixture-of-Betas infrastructure

The paper models prevalence priors as mixtures of two Beta distributions,
parametrized per property. We discretize to 11 bins (0%, 10%, ..., 100%)
and evaluate the Beta PDF kernel: x^(a-1) · (1-x)^(b-1) at x = k/10,
which is proportional to k^(a-1) · (10-k)^(b-1).

With 11 bins, the transient Beta(1,99) concentrates >99.99% of mass
in bin 0, so we approximate it as a delta at 0 scaled to preserve the
correct ratio between the absent-component peak and the stable peak. -/

/-- Unnormalized Beta(a,b) weight at bin k ∈ {0,...,10}.
    Proportional to Beta(a,b) PDF at x = k/10. -/
def betaWeight (a b k : Nat) : Nat :=
  k ^ (a - 1) * (10 - k) ^ (b - 1)

/-- Sum of Beta(a,b) weights across all 11 bins. -/
def betaTotal (a b : Nat) : Nat :=
  betaWeight a b 0 + betaWeight a b 1 + betaWeight a b 2 +
  betaWeight a b 3 + betaWeight a b 4 + betaWeight a b 5 +
  betaWeight a b 6 + betaWeight a b 7 + betaWeight a b 8 +
  betaWeight a b 9 + betaWeight a b 10

/-- Mixture-of-Betas prevalence prior, discretized to 11 bins.

    - Stable component: Beta(as, bs) with mixture weight φ
    - Absent component: point mass at prevalence 0 with weight (1-φ),
      scaled by `betaTotal` so the absent/stable peak ratio is correct

    The paper's WebPPL implementation uses `DiscreteBeta(γ, δ)` for the
    stable component with a = γδ, b = (1-γ)δ. We require integer a, b
    so that the weights are exactly rational. -/
def mixturePrior (phi : ℚ) (as bs : Nat) (p : Prevalence) : ℚ :=
  let k := p.toNat
  let stableW : ℚ := betaWeight as bs k
  let absentW : ℚ := if k = 0 then betaTotal as bs else 0
  phi * stableW + (1 - phi) * absentW

/-- "Lays eggs" prior: bimodal at 0 and ~50% (Figure 2, column 4).
    φ = 3/10, stable Beta(5,5) peaked at 50%.

    Most animal categories don't have egg-layers (peak at 0);
    among those that do, only females lay eggs (~50% prevalence). -/
def laysEggsPrior : Prevalence → ℚ := mixturePrior (3/10) 5 5

/-- "Is female" prior: unimodal at ~50% (Figure 2, column 5).
    φ = 99/100, stable Beta(5,5) peaked at 50%.

    Almost all animal categories have ~50% female members. -/
def isFemalePrior : Prevalence → ℚ := mixturePrior (99/100) 5 5

/-- "Carries malaria" prior: extreme low prevalence (Figure 2, column 6).
    φ = 1/100, stable Beta(2,10) peaked near 10%.

    Very few animal categories carry diseases. Among those
    that do, prevalence is very low. -/
def carriesMalariaPrior : Prevalence → ℚ := mixturePrior (1/100) 2 10

/-- "Bark" prior: bimodal at 0 and ~90% (Figure 2, column 1).
    φ = 1/2, stable Beta(10,2) peaked at ~90%.

    Most animals don't bark (peak at 0);
    those that do bark with high prevalence. -/
def barkPrior : Prevalence → ℚ := mixturePrior (1/2) 10 2

/-- "Have spots" prior: bimodal at 0 and ~90% (Figure 2, column 2).
    φ = 1/10, stable Beta(10,2) peaked at ~90%.

    Most animal categories don't have spots (peak at 0);
    those that do tend to have high prevalence. Lower φ than bark
    since fewer animal categories have spotted members. -/
def haveSpotsPrior : Prevalence → ℚ := mixturePrior (1/10) 10 2

/-- "Don't eat people" prior: near-unimodal at ~90% (Figure 2, column 3).
    φ = 99/100, stable Beta(10,2) peaked at ~90%.

    Almost all animal categories don't eat people. -/
def dontEatPeoplePrior : Prevalence → ℚ := mixturePrior (99/100) 10 2

-- ============================================================================
-- § 5. RSAConfig — Marginalized Threshold Model
-- ============================================================================

open Real (rpow rpow_nonneg)

/-- Cast a ℚ-valued prior to ℝ. -/
noncomputable def priorR (prior : Prevalence → ℚ) (p : Prevalence) : ℝ :=
  (prior p : ℝ)

private theorem mixturePrior_nonneg (phi : ℚ) (hphi : 0 ≤ phi) (hphi1 : phi ≤ 1)
    (as bs : Nat) :
    ∀ p : Prevalence, 0 ≤ mixturePrior phi as bs p := by
  intro p
  simp only [mixturePrior]
  apply add_nonneg
  · apply mul_nonneg hphi; exact_mod_cast Nat.zero_le _
  · apply mul_nonneg (by linarith)
    split
    · exact_mod_cast Nat.zero_le _
    · exact le_refl 0

private theorem priorR_nonneg_of (prior : Prevalence → ℚ)
    (h : ∀ p : Prevalence, 0 ≤ prior p) :
    ∀ p : Prevalence, 0 ≤ priorR prior p := by
  intro p; simp only [priorR]; exact_mod_cast h p

/-- Number of thresholds θ ∈ {0,...,9} satisfying p > θ.

    For generic: count = p.toNat (0 for p=0, 1 for p=1, ..., 10 for p=10).
    For silence: count = 10 (all thresholds pass). -/
def thresholdCount (u : Utterance) (p : Prevalence) : Nat :=
  match u with
  | .generic => p.toNat
  | .silent => 10

/-- Parametric RSAConfig for threshold-based generic endorsement.

    The threshold θ is marginalized analytically into the meaning function:
    meaning(u, p) = P(p) · |{θ : ⟦u⟧(p,θ) = true}|

    This matches the paper's endorsement model structure:
    S(u | p) ∝ (∫_θ L(p, θ | u) dθ)^λ

    The marginalization happens BEFORE exponentiation (matching the paper),
    not after (as would happen with θ as a latent variable in RSAConfig).
    With `Latent = Unit`, S1 scores the marginalized L0 directly. -/
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

private theorem laysEggsPrior_nonneg : ∀ p : Prevalence, 0 ≤ laysEggsPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _

private theorem isFemalePrior_nonneg : ∀ p : Prevalence, 0 ≤ isFemalePrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _

private theorem carriesMalariaPrior_nonneg : ∀ p : Prevalence, 0 ≤ carriesMalariaPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _

private theorem barkPrior_nonneg : ∀ p : Prevalence, 0 ≤ barkPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _

private theorem haveSpotsPrior_nonneg : ∀ p : Prevalence, 0 ≤ haveSpotsPrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _

private theorem dontEatPeoplePrior_nonneg : ∀ p : Prevalence, 0 ≤ dontEatPeoplePrior p :=
  mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _

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

-- ============================================================================
-- § 6. Semantic Properties
-- ============================================================================

/-- Prevalence 100% satisfies the generic for all thresholds. -/
theorem generic_top_true :
    ∀ θ : GenThreshold, genericMeaning θ (deg 10) = true := by
  native_decide

/-- Generic meaning at prevalence 0% is false for all thresholds. -/
theorem generic_zero_false :
    ∀ θ : GenThreshold, genericMeaning θ (deg 0) = false := by
  native_decide

/-- The bimodal "lays eggs" prior peaks at zero prevalence. -/
theorem laysEggs_peaks_at_zero :
    laysEggsPrior (deg 0) > laysEggsPrior (deg 5) := by native_decide

/-- The unimodal "is female" prior peaks at 50%. -/
theorem isFemale_peaks_at_50 :
    isFemalePrior (deg 5) > isFemalePrior (deg 0) := by native_decide

-- ============================================================================
-- § 7. Endorsement Predictions (S1 — the paper's primary model)
-- ============================================================================

/-! ### Endorsement model (Eq. 3)

The paper's key predictions are endorsement rates: given referent prevalence
p for a kind k, does the speaker produce the generic?

    S(u | p) ∝ (∫_θ L(p,θ|u) dθ)^λ

Endorsement > 50% ⟺ S1(generic | p) > S1(silent | p).

With α = 1, this reduces to L0(generic, p) > L0(silent, p), which holds
iff the referent prevalence exceeds the prior mean prevalence. This is
the paper's central insight: the same prevalence can produce different
endorsement rates depending on the prior (Figure 2). -/

/-- "Dogs bark" endorsed at 90% prevalence (Figure 2, column 1: 0.88). -/
theorem bark_endorsed :
    barkCfg.S1 () (deg 9) .generic > barkCfg.S1 () (deg 9) .silent := by
  rsa_predict

/-- "Robins lay eggs" endorsed at 50% prevalence (Figure 2, column 4: 0.95).
    Despite only 50% prevalence, the bimodal prior (peaked at 0 and 50%)
    makes the generic highly informative — it rules out the absent component. -/
theorem laysEggs_endorsed :
    laysEggsCfg.S1 () (deg 5) .generic > laysEggsCfg.S1 () (deg 5) .silent := by
  rsa_predict

/-- "Mosquitos carry malaria" endorsed at 10% prevalence (Figure 2, column 6: 0.97).
    The prior expects near-zero prevalence, so even low prevalence is
    highly informative. This is the model's explanation of "striking property"
    generics: rare properties have low prior expectations. -/
theorem malaria_endorsed :
    malariaCfg.S1 () (deg 1) .generic > malariaCfg.S1 () (deg 1) .silent := by
  rsa_predict

/-- "Robins are female" endorsed at 50% prevalence (Figure 2, column 5: 0.50).
    The unimodal prior peaks at 50%, so the generic is minimally informative.
    Endorsement is barely above 50%, matching the paper's borderline prediction. -/
theorem isFemale_endorsed :
    isFemaleCfg.S1 () (deg 5) .generic > isFemaleCfg.S1 () (deg 5) .silent := by
  rsa_predict

/-- "Kangaroos have spots" NOT endorsed at 0% prevalence (Figure 2, column 2: 0.02).
    At p = 0, no threshold θ satisfies 0 > θ, so the generic is trivially false. -/
theorem spots_not_endorsed :
    ¬(haveSpotsCfg.S1 () (deg 0) .generic > haveSpotsCfg.S1 () (deg 0) .silent) := by
  rsa_predict

-- ============================================================================
-- § 8. Connection to Phenomena.Generics.Data
-- ============================================================================

/-! The prevalence asymmetry from `Phenomena.Generics.Data` is EXPLAINED
by the endorsement model: same prevalence (50%), different prior shapes →
different S1 endorsement rates.

`laysEggsVsIsFemale` records the empirical observation.
`laysEggs_endorsed` and `isFemale_endorsed` derive the predictions. -/

/-- The data records 50% prevalence for both "lay eggs" and "is female". -/
theorem asymmetry_same_prevalence :
    Phenomena.Generics.laysEggsVsIsFemale.prevalence = 1/2 := rfl

end Phenomena.Generics.Studies.TesslerGoodman2019
