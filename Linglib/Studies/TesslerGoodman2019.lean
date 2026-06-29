import Linglib.Semantics.Degree.Basic
import Linglib.Pragmatics.RSA.Operators
import Linglib.Pragmatics.RSA.Limits
import Linglib.Pragmatics.RSA.Monotonicity
import Linglib.Core.Probability.Finite
import Mathlib.Data.Rat.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# [tessler-goodman-2019]: The Language of Generalization
[tessler-goodman-2019] [lassiter-goodman-2017]

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

This analytical marginalization eliminates the latent variable entirely.
The model is the mathlib-`PMF` RSA pipeline ([frank-goodman-2012]): the literal
listener `L0gen prior u : PMF Prevalence` normalises the marginalized meaning
`meaningE prior u p = P(p) · |{θ : ⟦u⟧(p,θ)}|` (lifted to `ℝ≥0∞`), and the speaker
`S1gen prior p : PMF Utterance` is `RSA.S1Belief` with `α = 1`, zero cost. Each
prediction is one application of `S1Belief_apply_lt_iff_score_lt` (the `rsa` simp
set): the partition cancels, leaving an `L0` comparison that reduces to the cue
validity test `p.toNat > E[k | prior]`. The prior expectation is the shared
`PMF.condExpect` of the silent listener's posterior (`expectedBin_eq_condExpect`).

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

namespace TesslerGoodman2019

open Semantics.Degree (Degree Threshold deg thr allDegrees allThresholds Degree.toNat Threshold.toNat)
open Semantics.Degree (positiveMeaning)

-- ============================================================================
-- § 1. Domain Types (reusing Semantics.Degree — same types as LassiterGoodman2017)
-- ============================================================================

/-- Discretized prevalence: 0%, 5%, ..., 100% (21 values).
    Structurally identical to [lassiter-goodman-2017]'s Height. -/
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
-- § 5. RSA Endorsement Model — mathlib-`PMF` pipeline
-- ============================================================================

open RSA
open scoped ENNReal

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

/-- The marginalized meaning lifted to `ℝ≥0∞`: `φ(u, p) = P(p) · |{θ : ⟦u⟧(p,θ)}|`.

    The latent threshold θ is marginalized analytically into the meaning, so the
    literal listener normalises this directly (matching the paper's structure, where
    θ is integrated out *before* exponentiation). For the generic the count is
    `p.toNat`; for silence it is the full `20`. -/
noncomputable def meaningE (prior : Prevalence → ℝ) (u : Utterance) (p : Prevalence) : ℝ≥0∞ :=
  ENNReal.ofReal (prior p * (thresholdCount u p : ℝ))

/-- The marginal meaning sum equals `ofReal` of the real sum (all summands `≥ 0`). -/
private theorem tsum_meaningE (prior : Prevalence → ℝ) (hp : ∀ p, 0 ≤ prior p) (u : Utterance) :
    ∑' p, meaningE prior u p = ENNReal.ofReal (∑ p, prior p * (thresholdCount u p : ℝ)) := by
  rw [tsum_fintype, ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (hp p) (by positivity))]
  rfl

/-- The marginal meaning sum is finite (`ofReal` is never `⊤`); no positivity needed. -/
private theorem meaningE_tsum_ne_top (prior : Prevalence → ℝ) (u : Utterance) :
    ∑' p, meaningE prior u p ≠ ⊤ := by
  rw [tsum_fintype]; exact ENNReal.sum_ne_top.mpr (fun p _ => ENNReal.ofReal_ne_top)

/-- Literal listener `L0(·|u) : PMF Prevalence`, normalising the marginalized meaning
    (`[frank-goodman-2012]`; the threshold-marginalized Eq. 1 of [tessler-goodman-2019]). -/
noncomputable def L0gen (prior : Prevalence → ℝ) (u : Utterance)
    (h0 : ∑' p, meaningE prior u p ≠ 0) (hT : ∑' p, meaningE prior u p ≠ ⊤) : PMF Prevalence :=
  RSA.L0OfMeaning (meaningE prior) u h0 hT

theorem L0gen_apply (prior : Prevalence → ℝ) (u : Utterance)
    (h0 : ∑' p, meaningE prior u p ≠ 0) (hT : ∑' p, meaningE prior u p ≠ ⊤) (p : Prevalence) :
    L0gen prior u h0 hT p = meaningE prior u p * (∑' q, meaningE prior u q)⁻¹ :=
  L0OfMeaning_apply _ _ _ _ _

open Classical in
/-- Total wrapper around `L0gen`: where the marginal is degenerate (mass `0`) the
    listener falls back to uniform, so the speaker `S1gen` below is a total `PMF`. On
    every well-defined prior (`tsum ≠ 0`) it agrees with `L0gen` (`L0genT_eq`). -/
noncomputable def L0genT (prior : Prevalence → ℝ) (u : Utterance) : PMF Prevalence :=
  if h : ∑' p, meaningE prior u p ≠ 0 then
    L0gen prior u h (meaningE_tsum_ne_top prior u)
  else PMF.uniformOfFintype Prevalence

open Classical in
theorem L0genT_eq (prior : Prevalence → ℝ) (u : Utterance) (h : ∑' p, meaningE prior u p ≠ 0) :
    L0genT prior u = L0gen prior u h (meaningE_tsum_ne_top prior u) := by
  rw [L0genT, dif_pos h]

private theorem s1gen_score_ne_top (prior : Prevalence → ℝ) (p : Prevalence) :
    ∑' u, (L0genT prior u p : ℝ≥0∞) ^ (1 : ℝ) * 1 ≠ ⊤ := by
  simp only [ENNReal.rpow_one, mul_one]; rw [tsum_fintype]
  exact ENNReal.sum_ne_top.mpr (fun u _ => PMF.apply_ne_top _ _)

open Classical in
/-- Pragmatic speaker `S1(·|p) ∝ L0(p|u)` (α = 1, zero cost), a `PMF Utterance`
    ([frank-goodman-2012]; the paper's Eq. 3 endorsement model). Total via `L0genT`:
    where the world `p` has zero prior mass the speaker degenerates to silence, but
    on the worlds the predictions evaluate (positive prior) it is the genuine
    `RSA.S1Belief` over the marginalized listener. -/
noncomputable def S1gen (prior : Prevalence → ℝ) (p : Prevalence) : PMF Utterance :=
  if h : ∑' u, (L0genT prior u p : ℝ≥0∞) ^ (1 : ℝ) * 1 ≠ 0 then
    S1Belief (L0genT prior) (fun _ => 1) 1 p h (s1gen_score_ne_top prior p)
  else PMF.pure .silent

open Classical in
theorem S1gen_eq (prior : Prevalence → ℝ) (p : Prevalence)
    (h : ∑' u, (L0genT prior u p : ℝ≥0∞) ^ (1 : ℝ) * 1 ≠ 0) :
    S1gen prior p = S1Belief (L0genT prior) (fun _ => 1) 1 p h (s1gen_score_ne_top prior p) := by
  rw [S1gen, dif_pos h]

/-- Silence is informative everywhere a world has positive prior mass, so the
    speaker's score-sum is non-degenerate there. -/
private theorem s1gen_score_ne_zero (prior : Prevalence → ℝ)
    (hsil : ∑' p, meaningE prior .silent p ≠ 0) (p : Prevalence) (hpp : 0 < prior p) :
    ∑' u, (L0genT prior u p : ℝ≥0∞) ^ (1 : ℝ) * 1 ≠ 0 := by
  simp only [ENNReal.rpow_one, mul_one]; rw [tsum_fintype]; intro h
  have hz := Finset.sum_eq_zero_iff.mp h .silent (Finset.mem_univ _)
  rw [L0genT_eq prior .silent hsil, L0gen_apply] at hz
  rcases mul_eq_zero.mp hz with h1 | h2
  · exact (ENNReal.ofReal_pos.mpr (by
      rw [show (thresholdCount .silent p : ℝ) = 20 from rfl]; exact mul_pos hpp (by norm_num))).ne' h1
  · exact ENNReal.inv_ne_zero.mpr (meaningE_tsum_ne_top prior .silent) h2

/-- The silent normaliser is non-degenerate given positive total prior mass. -/
private theorem meaningE_silent_ne_zero (prior : Prevalence → ℝ) (hp : ∀ p, 0 ≤ prior p)
    (hZ : 0 < ∑ w, prior w) : ∑' p, meaningE prior .silent p ≠ 0 := by
  rw [tsum_meaningE prior hp .silent]
  refine (ENNReal.ofReal_pos.mpr ?_).ne'
  rw [show (∑ w, prior w * (thresholdCount .silent w : ℝ)) = 20 * ∑ w, prior w from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun w _ => by
          rw [show (thresholdCount .silent w : ℝ) = 20 from rfl]; ring)]
  positivity

/-- The generic normaliser is non-degenerate when the referent has positive prior
    mass and a positive threshold count (`p.toNat > 0`, i.e. `p ≠ 0%`). -/
private theorem meaningE_generic_ne_zero (prior : Prevalence → ℝ) (hp : ∀ p, 0 ≤ prior p)
    (p : Prevalence) (hpp : 0 < prior p) (hpn : 0 < p.toNat) :
    ∑' q, meaningE prior .generic q ≠ 0 := by
  rw [tsum_meaningE prior hp .generic]
  refine (ENNReal.ofReal_pos.mpr ?_).ne'
  refine lt_of_lt_of_le (b := prior p * (thresholdCount .generic p : ℝ)) ?_
    (Finset.single_le_sum (f := fun q => prior q * (thresholdCount .generic q : ℝ))
      (fun q _ => mul_nonneg (hp q) (by positivity)) (Finset.mem_univ p))
  have hcount : 0 < (thresholdCount .generic p : ℝ) := by
    rw [show (thresholdCount .generic p : ℝ) = (p.toNat : ℝ) from rfl]; exact_mod_cast hpn
  exact mul_pos hpp hcount

-- ============================================================================
-- § 6. Semantic Properties
-- ============================================================================

/-- Prevalence 100% satisfies the generic for all thresholds. -/
theorem generic_top_true :
    ∀ θ : GenThreshold, genericMeaning θ (prevPct 100) = true := by
  decide

/-- Generic meaning at prevalence 0% is false for all thresholds. -/
theorem generic_zero_false :
    ∀ θ : GenThreshold, genericMeaning θ (prevPct 0) = false := by
  decide

/-- The bimodal "lays eggs" prior peaks at zero prevalence. -/
theorem laysEggs_peaks_at_zero :
    laysEggsPrior (prevPct 0) > laysEggsPrior (prevPct 50) := by
  norm_num [laysEggsPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]

/-- The unimodal "is female" prior peaks at 50%. -/
theorem isFemale_peaks_at_50 :
    isFemalePrior (prevPct 50) > isFemalePrior (prevPct 0) := by
  norm_num [isFemalePrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]

/-- Expand a sum over `Degree 20` (≃ `Fin 21`) into a `Fin 21` sum, so that
    concrete prior expectations evaluate by `Fin.sum_univ_succ` + `norm_num`. -/
private theorem sum_degree20 {M : Type*} [AddCommMonoid M] (f : Degree 20 → M) :
    ∑ w, f w = ∑ i : Fin 21, f ⟨i⟩ :=
  (Equiv.sum_comp ⟨(⟨·⟩), Degree.value, fun _ => rfl, fun ⟨_⟩ => rfl⟩ f).symm

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

/-- The endorsement condition reduces to a cue validity comparison:
    a generic is endorsed iff the referent prevalence bin exceeds the prior
    expected bin. This is the paper's central analytical result (Appendix A).

    The hypotheses `hgen`/`hsil` (the two normalisers are non-degenerate) are exactly
    `PMF.normalize`'s well-definedness obligations; they hold for every real prior with
    positive total mass and a positive-count referent (see `meaningE_generic_ne_zero`,
    `meaningE_silent_ne_zero`).

    Proof: the `rsa` simp set reduces the `S1Belief` comparison to the `L0` scores
    (`S1Belief_apply_lt_iff_score_lt`, partition cancels); `L0gen_apply` expands each to
    `meaningE · / Σ meaningE`; lifting `ofReal` out cross-multiplies to
    `p.toNat × Σ prior > Σ prior · toNat`, i.e. `p.toNat > E[k|prior]`. -/
theorem endorsement_iff_exceeds_expected
    (prior : Prevalence → ℝ) (hp : ∀ p, 0 ≤ prior p)
    (hgen : ∑' q, meaningE prior .generic q ≠ 0)
    (hsil : ∑' q, meaningE prior .silent q ≠ 0)
    (p : Prevalence)
    (hp_pos : 0 < prior p)
    (hZ : 0 < ∑ w : Prevalence, prior w) :
    S1gen prior p .generic > S1gen prior p .silent ↔ (p.toNat : ℝ) > expectedBin prior := by
  rw [gt_iff_lt, S1gen_eq prior p (s1gen_score_ne_zero prior hsil p hp_pos)]
  simp only [rsa, ENNReal.rpow_one, mul_one]
  rw [L0genT_eq prior .silent hsil, L0genT_eq prior .generic hgen,
      L0gen_apply, L0gen_apply, tsum_meaningE prior hp .silent, tsum_meaningE prior hp .generic]
  simp only [meaningE]
  have hSgen : 0 < ∑ w, prior w * (thresholdCount .generic w : ℝ) := by
    rw [← ENNReal.ofReal_pos, ← tsum_meaningE prior hp .generic]; exact pos_iff_ne_zero.mpr hgen
  have hSsil : (∑ w, prior w * (thresholdCount .silent w : ℝ)) = 20 * (∑ w, prior w) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => by
      rw [show (thresholdCount .silent w : ℝ) = 20 from rfl]; ring)
  rw [hSsil, show (thresholdCount .silent p : ℝ) = 20 from rfl,
      ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos hSgen,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity),
      expectedBin, gt_iff_lt, ← div_eq_mul_inv, ← div_eq_mul_inv,
      div_lt_div_iff₀ (by positivity) hSgen, div_lt_iff₀ hZ]
  -- `thresholdCount .generic` is `Degree.toNat`; unify so the atoms match `expectedBin`.
  simp only [thresholdCount]
  constructor <;> intro h <;> nlinarith

/-! ### The endorsement boundary is the silent listener's expected prevalence

The silent utterance is true at every prevalence, so the silent literal listener's
posterior `L0gen prior .silent` *is* the (normalised) prevalence prior. Its
`PMF.condExpect` over all prevalences is therefore exactly `expectedBin prior` — the
boundary in `endorsement_iff_exceeds_expected`, expressed through the shared
conditional-expectation API rather than as an ad-hoc ratio. -/

/-- The silent listener's posterior is the normalised prior: `L0(p | silent) = P(p)/Z`. -/
theorem L0genT_silent_apply (prior : Prevalence → ℝ) (hp : ∀ p, 0 ≤ prior p)
    (hsil : ∑' q, meaningE prior .silent q ≠ 0) (hZ : 0 < ∑ w, prior w) (p : Prevalence) :
    L0genT prior .silent p = ENNReal.ofReal (prior p / (∑ w, prior w)) := by
  rw [L0genT_eq prior .silent hsil, L0gen_apply, tsum_meaningE prior hp .silent]
  simp only [meaningE]
  rw [show (∑ w, prior w * (thresholdCount .silent w : ℝ)) = 20 * (∑ w, prior w) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun w _ => by
          rw [show (thresholdCount .silent w : ℝ) = 20 from rfl]; ring),
      show (thresholdCount .silent p : ℝ) = 20 from rfl,
      ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_mul (mul_nonneg (hp p) (by norm_num))]
  congr 1
  field_simp

/-- **`expectedBin` is a conditional expectation**: the endorsement boundary equals
    `E[prevalence | silent listener]`, computed through the shared `PMF.condExpect`. -/
theorem expectedBin_eq_condExpect (prior : Prevalence → ℝ) (hp : ∀ p, 0 ≤ prior p)
    (hsil : ∑' q, meaningE prior .silent q ≠ 0) (hZ : 0 < ∑ w, prior w) :
    (L0genT prior .silent).condExpect Set.univ (fun p => (p.toNat : ℝ≥0∞)) =
      ENNReal.ofReal (expectedBin prior) := by
  rw [PMF.condExpect_eq_div, PMF.probOfSet_univ, div_one]
  simp only [Set.indicator_univ]
  rw [expectedBin, Finset.sum_div, ENNReal.ofReal_sum_of_nonneg
        (fun w _ => div_nonneg (mul_nonneg (hp w) (by positivity)) (le_of_lt hZ))]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [L0genT_silent_apply prior hp hsil hZ w, ← ENNReal.ofReal_natCast w.toNat,
      ← ENNReal.ofReal_mul (div_nonneg (hp w) (le_of_lt hZ))]
  congr 1
  rw [div_mul_eq_mul_div]

/-! ### Symmetric priors put the endorsement boundary at the centre

A prior invariant under bin-reflection `k ↦ 20 − k` has its mean at the central bin
(50% prevalence). This makes the "robins are female" borderline a *theorem about
symmetry* rather than a numerical coincidence. -/

/-- The bin-reflection `k ↦ 20 − k` as a permutation of `Prevalence`. `Degree 20`
    wraps `Fin 21`, so reflect `Fin.rev` on the underlying `.value` field. -/
private def reflectPrev : Equiv.Perm Prevalence where
  toFun k := ⟨Fin.rev k.value⟩
  invFun k := ⟨Fin.rev k.value⟩
  left_inv k := by simp only [Fin.rev_rev]
  right_inv k := by simp only [Fin.rev_rev]

private theorem reflectPrev_toNat (k : Prevalence) : (reflectPrev k).toNat = 20 - k.toNat := by
  show (Fin.rev k.value).val = 20 - k.value.val
  rw [Fin.val_rev]; omega

/-- For a reflection-symmetric prior the prevalence-weighted total is the centre bin
    times the mass: `∑ prior(k)·k = 10 · ∑ prior(k)` — reflect the index and average
    with the original. -/
private theorem wsum_symm {prior : Prevalence → ℝ}
    (hsymm : ∀ k : Prevalence, prior (reflectPrev k) = prior k) :
    ∑ k : Prevalence, prior k * (k.toNat : ℝ) = 10 * ∑ k : Prevalence, prior k := by
  have hk : ∀ k : Prevalence, k.toNat ≤ 20 := fun k => Nat.lt_succ_iff.mp k.value.isLt
  have key : (∑ k : Prevalence, prior k * (k.toNat : ℝ))
           = ∑ k : Prevalence, prior k * ((20 : ℝ) - (k.toNat : ℝ)) := by
    refine Fintype.sum_equiv reflectPrev _ _ (fun k => ?_)
    rw [hsymm k, reflectPrev_toNat k, Nat.cast_sub (hk k)]; push_cast; ring
  rw [Finset.sum_congr rfl (fun k _ => by ring :
        ∀ k ∈ Finset.univ, prior k * ((20:ℝ) - (k.toNat:ℝ)) = 20 * prior k - prior k * (k.toNat:ℝ)),
      Finset.sum_sub_distrib, ← Finset.mul_sum] at key
  linarith [key]

/-- **A reflection-symmetric prior has its mean exactly at the centre bin (50%).** -/
theorem expectedBin_of_symmetric {prior : Prevalence → ℝ}
    (hsymm : ∀ k : Prevalence, prior (reflectPrev k) = prior k)
    (hZ : 0 < ∑ k : Prevalence, prior k) : expectedBin prior = 10 := by
  unfold expectedBin
  rw [wsum_symm hsymm, mul_div_assoc, div_self (ne_of_gt hZ), mul_one]

/-- The "is female" prior — `Beta(10, 10)` with mixture weight `φ = 1` — is invariant
    under bin-reflection, since `betaWeight a b k = betaWeight b a (20−k)` and here
    `a = b = 10`. -/
theorem isFemalePrior_symm (k : Prevalence) :
    priorR isFemalePrior (reflectPrev k) = priorR isFemalePrior k := by
  unfold priorR
  congr 1
  show isFemalePrior (reflectPrev k) = isFemalePrior k
  have hk : k.toNat ≤ 20 := Nat.lt_succ_iff.mp k.value.isLt
  have h20 : 20 - (20 - k.toNat) = k.toNat := by omega
  simp only [isFemalePrior, mixturePrior, betaWeight, reflectPrev_toNat k, h20]
  ring

set_option maxHeartbeats 1000000 in
/-- "Dogs bark" endorsed at 95% prevalence (Table 1: 95%; Figure 2, column 1: 0.88). -/
theorem bark_endorsed :
    S1gen (priorR barkPrior) (prevPct 95) .generic >
    S1gen (priorR barkPrior) (prevPct 95) .silent := by
  have hp := priorR_nonneg_of barkPrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR barkPrior (prevPct 95) := by
    simp only [priorR]
    norm_num [barkPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR barkPrior w := by
    rw [sum_degree20]
    norm_num [priorR, barkPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR barkPrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 95) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 95) hpp hZ]
  unfold expectedBin
  rw [gt_iff_lt, div_lt_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, barkPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

set_option maxHeartbeats 1000000 in
/-- "Robins lay eggs" endorsed at 50% prevalence (Figure 2, column 4: 0.95).
    Despite only 50% prevalence, the bimodal prior (peaked at 0 and 50%)
    makes the generic highly informative — it rules out the absent component. -/
theorem laysEggs_endorsed :
    S1gen (priorR laysEggsPrior) (prevPct 50) .generic >
    S1gen (priorR laysEggsPrior) (prevPct 50) .silent := by
  have hp := priorR_nonneg_of laysEggsPrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR laysEggsPrior (prevPct 50) := by
    simp only [priorR]
    norm_num [laysEggsPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR laysEggsPrior w := by
    rw [sum_degree20]
    norm_num [priorR, laysEggsPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR laysEggsPrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 50) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 50) hpp hZ]
  unfold expectedBin
  rw [gt_iff_lt, div_lt_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, laysEggsPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

set_option maxHeartbeats 1000000 in
/-- "Mosquitos carry malaria" endorsed at 10% prevalence (Figure 2, column 6: 0.97).
    The prior expects near-zero prevalence, so even low prevalence is
    highly informative. This is the model's explanation of "striking property"
    generics: rare properties have low prior expectations. -/
theorem malaria_endorsed :
    S1gen (priorR carriesMalariaPrior) (prevPct 10) .generic >
    S1gen (priorR carriesMalariaPrior) (prevPct 10) .silent := by
  have hp := priorR_nonneg_of carriesMalariaPrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR carriesMalariaPrior (prevPct 10) := by
    simp only [priorR]
    norm_num [carriesMalariaPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR carriesMalariaPrior w := by
    rw [sum_degree20]
    norm_num [priorR, carriesMalariaPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR carriesMalariaPrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 10) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 10) hpp hZ]
  unfold expectedBin
  rw [gt_iff_lt, div_lt_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, carriesMalariaPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

set_option maxHeartbeats 1000000 in
/-- "Kangaroos have spots" NOT endorsed at 10% prevalence (Figure 2, column 2: 0.02).
    Even though the prior has a null component, φ = 0.7 means 70% of the prior
    mass comes from the stable Beta(5,1) peaked near 100%. At 10% prevalence,
    the generic is uninformative relative to this high-prevalence expectation. -/
theorem spots_not_endorsed :
    ¬(S1gen (priorR haveSpotsPrior) (prevPct 10) .generic >
      S1gen (priorR haveSpotsPrior) (prevPct 10) .silent) := by
  have hp := priorR_nonneg_of haveSpotsPrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR haveSpotsPrior (prevPct 10) := by
    simp only [priorR]
    norm_num [haveSpotsPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR haveSpotsPrior w := by
    rw [sum_degree20]
    norm_num [priorR, haveSpotsPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR haveSpotsPrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 10) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 10) hpp hZ, not_lt]
  unfold expectedBin
  rw [le_div_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, haveSpotsPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

set_option maxHeartbeats 1000000 in
/-- "Sharks don't eat people" NOT endorsed at 80% prevalence (Figure 2, column 3: 0.41).
    Even though 80% is high in absolute terms, the prior (φ=1, Beta(10,1))
    concentrates nearly all mass above 80%. The generic is uninformative
    because the listener already expects very high prevalence. -/
theorem dontEatPeople_not_endorsed :
    ¬(S1gen (priorR dontEatPeoplePrior) (prevPct 80) .generic >
      S1gen (priorR dontEatPeoplePrior) (prevPct 80) .silent) := by
  have hp := priorR_nonneg_of dontEatPeoplePrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR dontEatPeoplePrior (prevPct 80) := by
    simp only [priorR]
    norm_num [dontEatPeoplePrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR dontEatPeoplePrior w := by
    rw [sum_degree20]
    norm_num [priorR, dontEatPeoplePrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR dontEatPeoplePrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 80) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 80) hpp hZ, not_lt]
  unfold expectedBin
  rw [le_div_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, dontEatPeoplePrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

set_option maxHeartbeats 1000000 in
/-- "Robins are female" borderline at 50% prevalence (Figure 2, column 5: 0.50) — as
    a **symmetry theorem**. The `Beta(10,10)`, `φ = 1` prior is reflection-symmetric
    (`isFemalePrior_symm`), so its mean is exactly the centre bin
    (`expectedBin_of_symmetric`: 50%); the 50%-referent then sits exactly on the
    endorsement boundary, so the generic is no more informative than silence. Not a
    numerical coincidence — a consequence of the prior's symmetry. -/
theorem isFemale_borderline :
    ¬(S1gen (priorR isFemalePrior) (prevPct 50) .generic >
      S1gen (priorR isFemalePrior) (prevPct 50) .silent) := by
  have hp := priorR_nonneg_of isFemalePrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR isFemalePrior (prevPct 50) := by
    simp only [priorR]
    norm_num [isFemalePrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR isFemalePrior w :=
    Finset.sum_pos' (fun i _ => hp i) ⟨prevPct 50, Finset.mem_univ _, hpp⟩
  rw [endorsement_iff_exceeds_expected (priorR isFemalePrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 50) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 50) hpp hZ, not_lt, expectedBin_of_symmetric isFemalePrior_symm hZ]
  norm_num [Degree.toNat]


-- ============================================================================
-- § 7b. Mathematical laws of the endorsement model
-- ============================================================================

/-! `endorsement_iff_exceeds_expected` says the endorsement decision is a single
*threshold on the referent prevalence at the prior mean* `expectedBin`. The model's
qualitative content is the behaviour of that threshold, derived below from the law
alone — no prior-specific computation, no `decide`. -/

/-- **Monotonicity in prevalence** (Figure 1C). At a fixed prior, endorsement is
    monotone in the referent prevalence: once a prevalence exceeds the prior mean,
    every higher prevalence is endorsed too. The endorsement curve is a step up at
    `expectedBin prior`. -/
theorem endorse_monotone {prior : Prevalence → ℝ} (hp : ∀ p, 0 ≤ prior p)
    (hgen : ∑' q, meaningE prior .generic q ≠ 0) (hsil : ∑' q, meaningE prior .silent q ≠ 0)
    (p₁ p₂ : Prevalence) (hpos₁ : 0 < prior p₁) (hpos₂ : 0 < prior p₂)
    (hZ : 0 < ∑ w : Prevalence, prior w) (hle : p₁.toNat ≤ p₂.toNat)
    (h : S1gen prior p₁ .generic > S1gen prior p₁ .silent) :
    S1gen prior p₂ .generic > S1gen prior p₂ .silent := by
  rw [endorsement_iff_exceeds_expected prior hp hgen hsil p₁ hpos₁ hZ, gt_iff_lt] at h
  rw [endorsement_iff_exceeds_expected prior hp hgen hsil p₂ hpos₂ hZ, gt_iff_lt]
  exact lt_of_lt_of_le h (by exact_mod_cast hle)

/-- **Prevalence asymmetry** ([leslie-2008]) as a theorem about prior *means*. At one
    and the same referent prevalence `p`, a property whose prior mean lies below `p`
    is endorsed while one whose prior mean lies at or above `p` is not. The asymmetry
    is therefore not a fact about the prevalence (it is shared) but the ordering of
    the two prior means `expectedBin prior₁ < p ≤ expectedBin prior₂` — exactly the
    paper's explanation of "robins lay eggs" vs. "robins are female". -/
theorem endorse_asymmetry_of_expected {prior₁ prior₂ : Prevalence → ℝ}
    (hp₁ : ∀ p, 0 ≤ prior₁ p) (hp₂ : ∀ p, 0 ≤ prior₂ p)
    (hgen₁ : ∑' q, meaningE prior₁ .generic q ≠ 0) (hsil₁ : ∑' q, meaningE prior₁ .silent q ≠ 0)
    (hgen₂ : ∑' q, meaningE prior₂ .generic q ≠ 0) (hsil₂ : ∑' q, meaningE prior₂ .silent q ≠ 0)
    (p : Prevalence)
    (hpos₁ : 0 < prior₁ p) (hpos₂ : 0 < prior₂ p)
    (hZ₁ : 0 < ∑ w : Prevalence, prior₁ w) (hZ₂ : 0 < ∑ w : Prevalence, prior₂ w)
    (hlo : expectedBin prior₁ < (p.toNat : ℝ)) (hhi : (p.toNat : ℝ) ≤ expectedBin prior₂) :
    (S1gen prior₁ p .generic > S1gen prior₁ p .silent) ∧
    ¬(S1gen prior₂ p .generic > S1gen prior₂ p .silent) := by
  refine ⟨?_, ?_⟩
  · rw [endorsement_iff_exceeds_expected prior₁ hp₁ hgen₁ hsil₁ p hpos₁ hZ₁, gt_iff_lt]; exact hlo
  · rw [endorsement_iff_exceeds_expected prior₂ hp₂ hgen₂ hsil₂ p hpos₂ hZ₂, not_lt]; exact hhi

-- ============================================================================
-- § 8. Prevalence Asymmetry ([leslie-2008])
-- ============================================================================

/-! The classic prevalence asymmetry is EXPLAINED by the endorsement model:
same prevalence (50%), different prior shapes → different S1 endorsement rates.

"Robins lay eggs" (true, ~50% prevalence) vs "Robins are female" (odd, ~50%
prevalence). [leslie-2008] documents the empirical observation;
[tessler-goodman-2019] derives the asymmetry from prior shape differences.

`laysEggs_endorsed` and `isFemale_borderline` (above) derive the predictions. -/

/-- **Generic endorsement is not prevalence-functional** — at the *same* referent
    prevalence (50%), "robins lay eggs" is endorsed but "robins are female" is not.
    The verdict is fixed by the property-specific prior, not by the prevalence
    ratio. This is the prevalence asymmetry ([leslie-2008]) as a structural fact:
    no generalized quantifier whose truth depends only on the cell ratio
    |R∩S| : |R∖S| — i.e. no `Proportional` quantifier, every counting quantifier
    in `Quantification.Counting` including `mostOn` — can capture generic
    endorsement. This is exactly where the majority view fails: contrast
    `Cohen1999.cohen_proportional`, which shows Cohen's θ = 1/2 GEN *is* proportional
    (and hence cannot exhibit this asymmetry). -/
theorem same_prevalence_opposite_endorsement :
    (S1gen (priorR laysEggsPrior) (prevPct 50) .generic >
      S1gen (priorR laysEggsPrior) (prevPct 50) .silent) ∧
    ¬(S1gen (priorR isFemalePrior) (prevPct 50) .generic >
      S1gen (priorR isFemalePrior) (prevPct 50) .silent) :=
  ⟨laysEggs_endorsed, isFemale_borderline⟩

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
    softmax (α • fun u : Utterance => log (l0Score prior u p)) .generic :=
  rpow_luce_eq_softmax (fun u => l0Score prior u p) α hl0 .generic

/-- When l0_gen > l0_sil (endorsed generic), the endorsement rate → 1
    as α → ∞. Direct corollary of `Softmax.tendsto_softmax_infty_at_max`. -/
theorem endorsement_tendsto_one (prior : Prevalence → ℝ) (p : Prevalence)
    (hs : 0 < l0Score prior .silent p)
    (h : l0Score prior .silent p < l0Score prior .generic p) :
    Tendsto (fun (α : ℝ) => softmax (α • fun u : Utterance => log (l0Score prior u p)) .generic)
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
    Tendsto (fun (α : ℝ) => softmax (α • fun u : Utterance => log (l0Score prior u p)) .generic)
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

[tessler-goodman-2019] (Case Study 2) extend the generic endorsement model
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

See also: `Genericity.thresholdGeneric` (grounded on the canonical
`Quantification.thresholdGtOn`) for the threshold reading of GEN, completing
the pipeline:
GEN → threshold → uncertain threshold → RSA endorsement.
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

set_option maxHeartbeats 1000000 in
/-- "John runs" endorsed at 75% frequency (moderate freq exceeds moderate prior). -/
theorem runs_endorsed_at_high_freq :
    S1gen (priorR runsPrior) (prevPct 75) .generic >
    S1gen (priorR runsPrior) (prevPct 75) .silent := by
  have hp := priorR_nonneg_of runsPrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR runsPrior (prevPct 75) := by
    simp only [priorR]
    norm_num [runsPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR runsPrior w := by
    rw [sum_degree20]
    norm_num [priorR, runsPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR runsPrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 75) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 75) hpp hZ]
  unfold expectedBin
  rw [gt_iff_lt, div_lt_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, runsPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

set_option maxHeartbeats 1000000 in
/-- "John climbs mountains" endorsed at 25% frequency (low freq exceeds rare-activity prior). -/
theorem climbs_mountains_endorsed_at_low_freq :
    S1gen (priorR climbsMountainsPrior) (prevPct 25) .generic >
    S1gen (priorR climbsMountainsPrior) (prevPct 25) .silent := by
  have hp := priorR_nonneg_of climbsMountainsPrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR climbsMountainsPrior (prevPct 25) := by
    simp only [priorR]
    norm_num [climbsMountainsPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR climbsMountainsPrior w := by
    rw [sum_degree20]
    norm_num [priorR, climbsMountainsPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR climbsMountainsPrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 25) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 25) hpp hZ]
  unfold expectedBin
  rw [gt_iff_lt, div_lt_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, climbsMountainsPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

set_option maxHeartbeats 1000000 in
/-- "John drinks coffee" NOT endorsed at 25% frequency (low freq below high-frequency prior). -/
theorem drinks_coffee_not_endorsed_at_low_freq :
    ¬(S1gen (priorR drinksCoffeePrior) (prevPct 25) .generic >
      S1gen (priorR drinksCoffeePrior) (prevPct 25) .silent) := by
  have hp := priorR_nonneg_of drinksCoffeePrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR drinksCoffeePrior (prevPct 25) := by
    simp only [priorR]
    norm_num [drinksCoffeePrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR drinksCoffeePrior w := by
    rw [sum_degree20]
    norm_num [priorR, drinksCoffeePrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR drinksCoffeePrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 25) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 25) hpp hZ, not_lt]
  unfold expectedBin
  rw [le_div_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, drinksCoffeePrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

/-- Habitual prior asymmetry: at the same 25% frequency, "climbs mountains" is endorsed
    but "drinks coffee" is not — paralleling the generic prevalence asymmetry. -/
theorem habitual_prior_asymmetry :
    (S1gen (priorR climbsMountainsPrior) (prevPct 25) .generic >
     S1gen (priorR climbsMountainsPrior) (prevPct 25) .silent) ∧
    ¬(S1gen (priorR drinksCoffeePrior) (prevPct 25) .generic >
      S1gen (priorR drinksCoffeePrior) (prevPct 25) .silent) :=
  ⟨climbs_mountains_endorsed_at_low_freq, drinks_coffee_not_endorsed_at_low_freq⟩

-- ════════════════════════════════════════════════════════════════════════════════
-- § 11. Case Study 3: Causal Language
-- ════════════════════════════════════════════════════════════════════════════════

/-!
## Case Study 3: Causal Language

[tessler-goodman-2019] (Case Study 3, Experiments 3A–3B) extend the model to
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

set_option maxHeartbeats 1000000 in
/-- Rare-weak cause endorsed at 20% causal rate: low prior expectation
    makes even 20% informative. -/
theorem rareWeak_endorsed_at_20pct :
    S1gen (priorR rareWeakPrior) (prevPct 20) .generic >
    S1gen (priorR rareWeakPrior) (prevPct 20) .silent := by
  have hp := priorR_nonneg_of rareWeakPrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR rareWeakPrior (prevPct 20) := by
    simp only [priorR]
    norm_num [rareWeakPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR rareWeakPrior w := by
    rw [sum_degree20]
    norm_num [priorR, rareWeakPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR rareWeakPrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 20) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 20) hpp hZ]
  unfold expectedBin
  rw [gt_iff_lt, div_lt_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, rareWeakPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

set_option maxHeartbeats 1000000 in
/-- Common-strong cause NOT endorsed at 20% causal rate: high prior
    expectation (peaked near 100%) makes 20% uninformative. -/
theorem commonStrong_not_endorsed_at_20pct :
    ¬(S1gen (priorR commonStrongPrior) (prevPct 20) .generic >
      S1gen (priorR commonStrongPrior) (prevPct 20) .silent) := by
  have hp := priorR_nonneg_of commonStrongPrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR commonStrongPrior (prevPct 20) := by
    simp only [priorR]
    norm_num [commonStrongPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR commonStrongPrior w := by
    rw [sum_degree20]
    norm_num [priorR, commonStrongPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR commonStrongPrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 20) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 20) hpp hZ, not_lt]
  unfold expectedBin
  rw [le_div_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, commonStrongPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

set_option maxHeartbeats 1000000 in
/-- Rare-weak cause endorsed at 70% causal rate. -/
theorem rareWeak_endorsed_at_70pct :
    S1gen (priorR rareWeakPrior) (prevPct 70) .generic >
    S1gen (priorR rareWeakPrior) (prevPct 70) .silent := by
  have hp := priorR_nonneg_of rareWeakPrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR rareWeakPrior (prevPct 70) := by
    simp only [priorR]
    norm_num [rareWeakPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR rareWeakPrior w := by
    rw [sum_degree20]
    norm_num [priorR, rareWeakPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR rareWeakPrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 70) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 70) hpp hZ]
  unfold expectedBin
  rw [gt_iff_lt, div_lt_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, rareWeakPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

set_option maxHeartbeats 1000000 in
/-- Common-strong cause NOT endorsed at 50% causal rate: high prior
    (Beta(10,1), φ=0.75) puts expected rate near 70%, so 50% is uninformative.
    Note: the paper tests at 20% and 70%. At 70%, the comparison is borderline
    (E[k|prior] ≈ 14 ≈ bin(70%)), matching the paper's ~50% endorsement rate
    at referent prevalence 0.7 for common-strong (Figure 11B). -/
theorem commonStrong_not_endorsed_at_50pct :
    ¬(S1gen (priorR commonStrongPrior) (prevPct 50) .generic >
      S1gen (priorR commonStrongPrior) (prevPct 50) .silent) := by
  have hp := priorR_nonneg_of commonStrongPrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR commonStrongPrior (prevPct 50) := by
    simp only [priorR]
    norm_num [commonStrongPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR commonStrongPrior w := by
    rw [sum_degree20]
    norm_num [priorR, commonStrongPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR commonStrongPrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 50) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 50) hpp hZ, not_lt]
  unfold expectedBin
  rw [le_div_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, commonStrongPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

set_option maxHeartbeats 1000000 in
/-- Rare-strong cause NOT endorsed at 20% causal rate (Figure 11B: ~35% endorsement).
    Despite fewer competing causes than common-strong, the prior still
    concentrates enough mass above 20% (via Beta(10,1)) to make 20% uninformative. -/
theorem rareStrong_not_endorsed_at_20pct :
    ¬(S1gen (priorR rareStrongPrior) (prevPct 20) .generic >
      S1gen (priorR rareStrongPrior) (prevPct 20) .silent) := by
  have hp := priorR_nonneg_of rareStrongPrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR rareStrongPrior (prevPct 20) := by
    simp only [priorR]
    norm_num [rareStrongPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR rareStrongPrior w := by
    rw [sum_degree20]
    norm_num [priorR, rareStrongPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR rareStrongPrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 20) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 20) hpp hZ, not_lt]
  unfold expectedBin
  rw [le_div_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, rareStrongPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

set_option maxHeartbeats 1000000 in
/-- Rare-strong cause endorsed at 70% causal rate (Figure 11B: ~90% endorsement). -/
theorem rareStrong_endorsed_at_70pct :
    S1gen (priorR rareStrongPrior) (prevPct 70) .generic >
    S1gen (priorR rareStrongPrior) (prevPct 70) .silent := by
  have hp := priorR_nonneg_of rareStrongPrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR rareStrongPrior (prevPct 70) := by
    simp only [priorR]
    norm_num [rareStrongPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR rareStrongPrior w := by
    rw [sum_degree20]
    norm_num [priorR, rareStrongPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR rareStrongPrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 70) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 70) hpp hZ]
  unfold expectedBin
  rw [gt_iff_lt, div_lt_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, rareStrongPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

set_option maxHeartbeats 1000000 in
/-- Common-weak cause endorsed at 70% causal rate (Figure 11B: ~75% endorsement).
    With Beta(2,8) peaked near 20%, a referent rate of 70% far exceeds
    the prior expectation. -/
theorem commonWeak_endorsed_at_70pct :
    S1gen (priorR commonWeakPrior) (prevPct 70) .generic >
    S1gen (priorR commonWeakPrior) (prevPct 70) .silent := by
  have hp := priorR_nonneg_of commonWeakPrior (mixturePrior_nonneg _ (by norm_num) (by norm_num) _ _ _ _)
  have hpp : 0 < priorR commonWeakPrior (prevPct 70) := by
    simp only [priorR]
    norm_num [commonWeakPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil]
  have hZ : 0 < ∑ w : Prevalence, priorR commonWeakPrior w := by
    rw [sum_degree20]
    norm_num [priorR, commonWeakPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
      List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
  rw [endorsement_iff_exceeds_expected (priorR commonWeakPrior) hp
      (meaningE_generic_ne_zero _ hp (prevPct 70) hpp (by decide)) (meaningE_silent_ne_zero _ hp hZ)
      (prevPct 70) hpp hZ]
  unfold expectedBin
  rw [gt_iff_lt, div_lt_iff₀ hZ, sum_degree20, sum_degree20]
  norm_num [priorR, commonWeakPrior, mixturePrior, betaWeight, betaTotal, Degree.toNat,
    List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
    Fin.sum_univ_succ, Fin.sum_univ_zero]

/-- Causal prior asymmetry (Experiment 3B): at 20% referent rate, only
    rare-weak is endorsed; the other three conditions are not.
    This matches the paper's Figure 11B (left panel). -/
theorem causal_20pct_pattern :
    (S1gen (priorR rareWeakPrior) (prevPct 20) .generic >
     S1gen (priorR rareWeakPrior) (prevPct 20) .silent) ∧
    ¬(S1gen (priorR rareStrongPrior) (prevPct 20) .generic >
      S1gen (priorR rareStrongPrior) (prevPct 20) .silent) ∧
    ¬(S1gen (priorR commonStrongPrior) (prevPct 20) .generic >
      S1gen (priorR commonStrongPrior) (prevPct 20) .silent) :=
  ⟨rareWeak_endorsed_at_20pct, rareStrong_not_endorsed_at_20pct,
   commonStrong_not_endorsed_at_20pct⟩

/-- At 70% referent rate, all conditions except common-strong are endorsed
    (Figure 11B). Common-strong is borderline (~50% endorsement in the paper),
    matching our model's E[k|prior] ≈ bin(70%). -/
theorem causal_70pct_pattern :
    (S1gen (priorR rareWeakPrior) (prevPct 70) .generic >
     S1gen (priorR rareWeakPrior) (prevPct 70) .silent) ∧
    (S1gen (priorR rareStrongPrior) (prevPct 70) .generic >
     S1gen (priorR rareStrongPrior) (prevPct 70) .silent) ∧
    (S1gen (priorR commonWeakPrior) (prevPct 70) .generic >
     S1gen (priorR commonWeakPrior) (prevPct 70) .silent) :=
  ⟨rareWeak_endorsed_at_70pct, rareStrong_endorsed_at_70pct, commonWeak_endorsed_at_70pct⟩

-- ════════════════════════════════════════════════════════════════════════════════
-- § 12. Cue Validity ↔ Prevalence Prior (Appendix A)
-- ════════════════════════════════════════════════════════════════════════════════

/-!
## Cue Validity and Endorsement

[tessler-goodman-2019] (pp. 29-30, Appendix A) show that endorsement in
the infinite-rationality limit reduces to a cue validity comparison:

    endorsed ⟺ prevalence(f, k_ref) > E_prior[prevalence]
             ⟺ cue_validity(f, k_ref) > 1

where `cue_validity(f, k) = prevalence(f, k) / E[prevalence]`.

This connects the RSA model to the classical notion from [rosch-mervis-1975]:
a feature is diagnostic of a category exactly when the feature is more prevalent
in that category than expected across categories — i.e., when cue validity > 1.

In `S1gen`, the endorsement condition
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
-- § 13. Unification: All Three Domains Use S1gen
-- ════════════════════════════════════════════════════════════════════════════════

/-!
## Unified Architecture

All three domains — generics, habituals, and causal language — are the **same**
`S1gen` speaker over `meaningE`, with different prevalence priors. The threshold
semantics, RSA inference, and endorsement mechanism are shared; only the prior varies.

This unification is structural (by construction), not proven post hoc.
The integration pipeline is:

1. **Traditional operator** (GEN/HAB) reduces to threshold semantics
   (`Genericity.thresholdGeneric`, on `Quantification.thresholdGtOn`)
2. **Threshold semantics** with uncertain threshold → marginalized `meaningE` → `L0gen`
3. **RSA endorsement** (`S1gen`) decides between generic and silence
4. **Endorsement ≈ cue validity** (`endorsed_iff_cue_validity_gt_one`)
-/

/-- All three case studies are `S1gen` of a prior — the prior is the only free
    parameter (the speaker engine is shared by construction). -/
theorem unification :
    (∃ pr : Prevalence → ℝ, S1gen (priorR barkPrior) = S1gen pr) ∧
    (∃ pr : Prevalence → ℝ, S1gen (priorR runsPrior) = S1gen pr) ∧
    (∃ pr : Prevalence → ℝ, S1gen (priorR rareWeakPrior) = S1gen pr) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

end TesslerGoodman2019
