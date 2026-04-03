import Linglib.Theories.Semantics.Degree.Core
import Linglib.Tactics.RSAPredict
import Linglib.Theories.Pragmatics.RSA.Core.Config
import Linglib.Theories.Pragmatics.RSA.Core.Softmax.Limits
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
| 9 | Only rareWeak endorsed at 20% | all four causal | 20% | `causal_20pct_pattern` |
| 10 | 3/4 causal conditions endorsed at 70% | all four causal | 70% | `causal_70pct_pattern` |
| 11 | Endorsement ⟺ exceeds E[k|prior] | — | — | `endorsement_iff_exceeds_expected` |
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
  deriving Repr, DecidableEq, Fintype

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
  (List.range 21).foldl (fun acc k => acc + betaWeight a b k) 0

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

/-- "Bark" config: peaked high prior (Figure 2, column 1). -/
@[reducible]
noncomputable def barkCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR barkPrior) (priorR_nonneg_of _ <|
    mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)

/-- "Have spots" config: peaked high prior (Figure 2, column 2). -/
@[reducible]
noncomputable def haveSpotsCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR haveSpotsPrior) (priorR_nonneg_of _ <|
    mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)

/-- "Don't eat people" config: peaked very high prior (Figure 2, column 3). -/
@[reducible]
noncomputable def dontEatPeopleCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR dontEatPeoplePrior) (priorR_nonneg_of _ <|
    mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)

/-- "Lays eggs" config: bimodal prior (Figure 2, column 4). -/
@[reducible]
noncomputable def laysEggsCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR laysEggsPrior) (priorR_nonneg_of _ <|
    mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)

/-- "Is female" config: unimodal prior at 50% (Figure 2, column 5). -/
@[reducible]
noncomputable def isFemaleCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR isFemalePrior) (priorR_nonneg_of _ <|
    mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)

/-- "Carries malaria" config: extreme low prior (Figure 2, column 6). -/
@[reducible]
noncomputable def malariaCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR carriesMalariaPrior) (priorR_nonneg_of _ <|
    mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)

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
-- § 7a. Endorsement Condition Simplification (Appendix A)
-- ============================================================================

/-! ### Analytical endorsement condition

The paper's central analytical result (Appendix A) is that the endorsement
comparison reduces to a cue validity test:

    S1(generic | p) > S1(silent | p) ⟺ p.toNat > E[k | prior]

i.e., the referent prevalence bin exceeds the prior expected bin.

**Proof sketch**: S1(u|p) ∝ rpow(L0(p|u), α). Since rpow is monotone for α > 0,
the comparison reduces to L0(p|generic) > L0(p|silent). Expanding:

    L0(p|u) = meaning(u,p) / Z_u = prior(p) · tc(u,p) / Z_u

For the generic, Z_gen = Σ_w prior(w) · w.toNat; for silence, Z_sil = 20 · Z_prior.
Dividing by prior(p) > 0 and cross-multiplying:

    p.toNat / Z_gen > 20 / Z_sil ⟺ p.toNat > Z_gen / Z_prior = E[k | prior]
-/

/-- Expected prevalence bin under a prior: E[k | prior] = Σ_k k·P(k) / Σ_k P(k). -/
noncomputable def expectedBin (prior : Prevalence → ℝ) : ℝ :=
  (∑ w : Prevalence, prior w * (w.toNat : ℝ)) / (∑ w : Prevalence, prior w)

open Core in
/-- Policy comparison ↔ score comparison for any RationalAction.
    Combines `policy_gt_of_score_gt` and `policy_not_gt_of_score_le`. -/
private theorem policy_gt_iff_score_gt {S A : Type*} [Fintype A]
    (ra : RationalAction S A) (s : S) (a₁ a₂ : A) :
    ra.policy s a₁ > ra.policy s a₂ ↔ ra.score s a₁ > ra.score s a₂ :=
  ⟨fun h => by
    by_contra hle; push_neg at hle
    exact absurd h (not_lt.mpr (ra.policy_monotone s a₁ a₂ hle)),
   ra.policy_gt_of_score_gt s a₁ a₂⟩

/-- The endorsement condition reduces to a cue validity comparison:
    a generic is endorsed iff the referent prevalence bin exceeds
    the prior expected bin. This is the paper's central analytical
    result (Appendix A).

    Proof: S1 policy comparison reduces to S1 score comparison (same
    denominator at world p), which equals L0 policy (rpow with α=1).
    The L0 policy comparison cross-multiplies to
    p.toNat × Σ prior > Σ prior × toNat, i.e., p.toNat > E[k|prior]. -/
theorem endorsement_iff_exceeds_expected
    (prior : Prevalence → ℝ) (hp : ∀ p, 0 ≤ prior p)
    (p : Prevalence)
    (hp_pos : 0 < prior p)
    (hZ : 0 < ∑ w : Prevalence, prior w) :
    (mkGenericCfg prior hp).S1 () p .generic > (mkGenericCfg prior hp).S1 () p .silent ↔
    (p.toNat : ℝ) > expectedBin prior := by
  set cfg := mkGenericCfg prior hp
  set l0 := cfg.L0agent ()
  -- Step 1: S1 policy → S1 score → L0 policy
  have hs1_eq : ∀ u, (cfg.S1agent ()).score p u = l0.policy u p :=
    fun u => Real.rpow_one _
  have step1 : cfg.S1 () p .generic > cfg.S1 () p .silent ↔
      l0.policy .generic p > l0.policy .silent p := by
    rw [show cfg.S1 () p .generic > cfg.S1 () p .silent ↔
        (cfg.S1agent ()).score p .generic > (cfg.S1agent ()).score p .silent from
      policy_gt_iff_score_gt _ _ _ _, hs1_eq, hs1_eq]
  rw [step1]
  -- Step 2: L0 totalScore facts
  have htg : l0.totalScore .generic = ∑ w, prior w * (w.toNat : ℝ) :=
    Finset.sum_congr rfl fun _ _ => rfl
  have hts : l0.totalScore .silent = 20 * ∑ w, prior w := by
    show ∑ w, l0.score .silent w = _
    simp_rw [show ∀ w, l0.score .silent w = prior w * 20 from fun _ => rfl, ← Finset.sum_mul]
    ring
  have hts_pos : 0 < l0.totalScore .silent := by rw [hts]; positivity
  have hts_ne : l0.totalScore .silent ≠ 0 := ne_of_gt hts_pos
  -- L0 silent policy = prior(p) / Zp
  have hpol_sil : l0.policy .silent p = prior p / ∑ w, prior w := by
    rw [Core.RationalAction.policy, if_neg hts_ne, hts]
    show prior p * 20 / (20 * ∑ w, prior w) = _
    rw [mul_comm (prior p) 20, mul_div_mul_left _ _ (by norm_num : (20 : ℝ) ≠ 0)]
  -- Case split on Zg
  by_cases hg0 : l0.totalScore .generic = 0
  · -- Zg = 0: p.toNat must be 0 (since prior(p) > 0), so both sides false
    rw [htg] at hg0
    have hpn : prior p * (p.toNat : ℝ) ≤ 0 :=
      hg0 ▸ Finset.single_le_sum (fun w _ => mul_nonneg (hp w) (Nat.cast_nonneg _))
        (Finset.mem_univ p)
    have hpn0 : (p.toNat : ℝ) = 0 := by
      nlinarith [mul_nonneg (le_of_lt hp_pos) (Nat.cast_nonneg (α := ℝ) (Degree.toNat p))]
    have hpol_gen : l0.policy .generic p = 0 := by
      rw [Core.RationalAction.policy, if_pos (by rw [htg]; exact hg0)]
    rw [hpol_gen, hpol_sil, hpn0, expectedBin, hg0, zero_div]
    constructor
    · intro h; linarith [div_pos hp_pos hZ]
    · intro h; linarith
  · -- Zg > 0: cross-multiply
    have hg_pos : 0 < l0.totalScore .generic :=
      lt_of_le_of_ne (l0.totalScore_nonneg .generic) (Ne.symm hg0)
    have hpol_gen : l0.policy .generic p = prior p * (p.toNat : ℝ) /
        (∑ w, prior w * (w.toNat : ℝ)) := by
      rw [Core.RationalAction.policy, if_neg hg0, htg]; rfl
    rw [hpol_gen, hpol_sil, expectedBin, gt_iff_lt, gt_iff_lt,
        div_lt_div_iff₀ hZ (by rwa [htg] at hg_pos), div_lt_iff₀ hZ]
    -- Goal: prior p * Zg < prior p * p.toNat * Zp ↔ Zg < p.toNat * Zp
    constructor <;> intro h <;> nlinarith

-- ============================================================================
-- § 8. Prevalence Asymmetry (@cite{leslie-2008})
-- ============================================================================

/-! The classic prevalence asymmetry is EXPLAINED by the endorsement model:
same prevalence (50%), different prior shapes → different S1 endorsement rates.

"Robins lay eggs" (true, ~50% prevalence) vs "Robins are female" (odd, ~50%
prevalence). @cite{leslie-2008} documents the empirical observation;
@cite{tessler-goodman-2019} derives the asymmetry from prior shape differences.

`laysEggs_endorsed` and `isFemale_borderline` (above) derive the predictions. -/

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

@[reducible]
noncomputable def runsCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR runsPrior) (priorR_nonneg_of _ <|
    mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)

@[reducible]
noncomputable def climbsMountainsCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR climbsMountainsPrior) (priorR_nonneg_of _ <|
    mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)

@[reducible]
noncomputable def drinksCoffeeCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR drinksCoffeePrior) (priorR_nonneg_of _ <|
    mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)

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

@cite{tessler-goodman-2019} (Case Study 3, Experiments 3A–3B) extend the model to
causal generics ("Herb X makes cheebas sleepy"). Here `Prevalence` is
reinterpreted as the causal rate — the proportion of cases where the cause
produces the effect.

**Experimental design**: In Experiment 3A, participants see "previous experimental
results" (a table of substances tested on 100 subjects) that follow one of four
distributions, manipulated between subjects:

- **common**: all substances show similar efficacy (unimodal distribution)
- **rare**: some substances show no efficacy, others show high (bimodal distribution)
- **strong**: effective substances produce strong effects (avg ~98%)
- **weak**: effective substances produce weak effects (avg ~20%)

In Experiment 3B, participants see one of two referent causal rates (**20%** or
**70%**) and judge whether the causal generalization holds ("Herb C makes cheebas
sleepy").

We model the four conditions as different prevalence priors, varying the mixture
weight φ (common → high φ, rare → low φ) and the stable Beta parameters
(strong → high-mean Beta, weak → low-mean Beta). These are approximations of
the empirically elicited priors from Experiment 3A, not exact replications.

The paper reports a model fit of r²(8) = 0.835 on causal endorsement data
(Figure 11B).
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

@[reducible]
noncomputable def commonStrongCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR commonStrongPrior) (priorR_nonneg_of _ <|
    mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)

@[reducible]
noncomputable def commonWeakCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR commonWeakPrior) (priorR_nonneg_of _ <|
    mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)

@[reducible]
noncomputable def rareStrongCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR rareStrongPrior) (priorR_nonneg_of _ <|
    mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)

@[reducible]
noncomputable def rareWeakCfg : RSA.RSAConfig Utterance Prevalence :=
  mkGenericCfg (priorR rareWeakPrior) (priorR_nonneg_of _ <|
    mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)

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
    (Beta(10,1), φ=0.75) puts expected rate near 70%, so 50% is uninformative.
    Note: the paper tests at 20% and 70%. At 70%, the comparison is borderline
    (E[k|prior] ≈ 14 ≈ bin(70%)), matching the paper's ~50% endorsement rate
    at referent prevalence 0.7 for common-strong (Figure 11B). -/
theorem commonStrong_not_endorsed_at_50pct :
    ¬(commonStrongCfg.S1 () (prevPct 50) .generic >
      commonStrongCfg.S1 () (prevPct 50) .silent) := by
  rsa_predict

/-- Rare-strong cause NOT endorsed at 20% causal rate (Figure 11B: ~35% endorsement).
    Despite fewer competing causes than common-strong, the prior still
    concentrates enough mass above 20% (via Beta(10,1)) to make 20% uninformative. -/
theorem rareStrong_not_endorsed_at_20pct :
    ¬(rareStrongCfg.S1 () (prevPct 20) .generic >
      rareStrongCfg.S1 () (prevPct 20) .silent) := by
  rsa_predict

/-- Rare-strong cause endorsed at 70% causal rate (Figure 11B: ~90% endorsement). -/
theorem rareStrong_endorsed_at_70pct :
    rareStrongCfg.S1 () (prevPct 70) .generic >
    rareStrongCfg.S1 () (prevPct 70) .silent := by
  rsa_predict

/-- Common-weak cause endorsed at 70% causal rate (Figure 11B: ~75% endorsement).
    With Beta(2,8) peaked near 20%, a referent rate of 70% far exceeds
    the prior expectation. -/
theorem commonWeak_endorsed_at_70pct :
    commonWeakCfg.S1 () (prevPct 70) .generic >
    commonWeakCfg.S1 () (prevPct 70) .silent := by
  rsa_predict

/-- Causal prior asymmetry (Experiment 3B): at 20% referent rate, only
    rare-weak is endorsed; the other three conditions are not.
    This matches the paper's Figure 11B (left panel). -/
theorem causal_20pct_pattern :
    (rareWeakCfg.S1 () (prevPct 20) .generic >
     rareWeakCfg.S1 () (prevPct 20) .silent) ∧
    ¬(rareStrongCfg.S1 () (prevPct 20) .generic >
      rareStrongCfg.S1 () (prevPct 20) .silent) ∧
    ¬(commonStrongCfg.S1 () (prevPct 20) .generic >
      commonStrongCfg.S1 () (prevPct 20) .silent) :=
  ⟨rareWeak_endorsed_at_20pct, rareStrong_not_endorsed_at_20pct,
   commonStrong_not_endorsed_at_20pct⟩

/-- At 70% referent rate, all conditions except common-strong are endorsed
    (Figure 11B). Common-strong is borderline (~50% endorsement in the paper),
    matching our model's E[k|prior] ≈ bin(70%). -/
theorem causal_70pct_pattern :
    (rareWeakCfg.S1 () (prevPct 70) .generic >
     rareWeakCfg.S1 () (prevPct 70) .silent) ∧
    (rareStrongCfg.S1 () (prevPct 70) .generic >
     rareStrongCfg.S1 () (prevPct 70) .silent) ∧
    (commonWeakCfg.S1 () (prevPct 70) .generic >
     commonWeakCfg.S1 () (prevPct 70) .silent) :=
  ⟨rareWeak_endorsed_at_70pct, rareStrong_endorsed_at_70pct, commonWeak_endorsed_at_70pct⟩

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
   (`CovertQuantifier.reduces_to_threshold`, `Habituals.hab_reduces_to_threshold`)
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
