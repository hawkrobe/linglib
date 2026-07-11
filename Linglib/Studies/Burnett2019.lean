import Linglib.Pragmatics.RSA.Canonical
import Linglib.Pragmatics.SocialMeaning.EckertMontague
import Linglib.Pragmatics.SignalingGame.Interpretation
import Linglib.Pragmatics.SocialMeaning.IndexicalField
import Linglib.Studies.Eckert2008
import Linglib.Studies.Labov2012

/-!
# [burnett-2019] — Signalling Games, Sociolinguistic Variation, and
the Construction of Style

Linguistics and Philosophy 42: 419–450.

## Overview

Social Meaning Games (SMGs) model how sociolinguistic variant choice
conveys social information. A speaker's use of *-ing* vs *-in'* induces
listener inferences about persona traits (competent, friendly, etc.).
The framework combines [lewis-1969]'s signalling games with RSA-style
Bayesian reasoning to derive both style shifting (intra-speaker variation
across contexts) and social stratification (inter-speaker variation across
classes) from the same principles.

## Architecture

The meaning function is **grounded** in the Eckert–Montague lift from
`EckertMontague.emMeaningMI`: each variant's Eckert field (a set of
indexed properties) is lifted to persona compatibility via intersection
semantics. The grounding theorem `ingMeaning_eq_emMeaningMI` verifies
that the study's meaning function matches the theory-layer derivation.

Each context is a belief-based RSA over personae (worlds) and variants
(utterances): the speaker `Sk` is the softmax of `L₀⁶` (α = 6) and the
listener `L1k` the Bayesian posterior (`PMF.posterior`) against the
context-specific persona prior, which also weights `L₀` (Burnett eq. 11).
Predictions are exact `PMF`-value comparisons.

## Key predictions

1. **Per-persona variant preference**: cool-guy prefers *-in'* ~69%
2. **Style shifting**: casual→careful flips the cool-guy's preference
3. **Stern-leader exclusion**: -in' is incompatible with stern leader
4. **Listener interpretation**: Rice/Pelosi/Bush /t/ release predictions
5. **Bulletproofing**: strong prior overwhelms variant effects (Bush)
6. **Cross-reference**: model predictions close to [labov-2012] data
-/

set_option autoImplicit false

namespace Burnett2019

open SocialMeaning
open SocialMeaning.EckertMontague
open Eckert2008 (INGVariant)
open RSA

-- ============================================================================
-- §1. Types
-- ============================================================================

/-- Social properties (Burnett example (5)). Two bipolar dimensions:
    competence (competent/incompetent) and warmth (friendly/aloof). -/
inductive PersonaTrait where
  | competent | incompetent | friendly | aloof
  deriving DecidableEq, Repr

instance : Fintype PersonaTrait where
  elems := {.competent, .incompetent, .friendly, .aloof}
  complete := by intro x; cases x <;> simp

/-- The four personae: maximally consistent subsets (Burnett example (6)).
    Each selects one pole per dimension. -/
inductive Persona where
  | coolGuy      -- {competent, friendly}: the cool guy
  | sternLeader  -- {competent, aloof}: the stern leader
  | doofus       -- {incompetent, friendly}: the doofus
  | asshole      -- {incompetent, aloof}: the arrogant asshole
  deriving DecidableEq, Repr

instance : Fintype Persona where
  elems := {.coolGuy, .sternLeader, .doofus, .asshole}
  complete := by intro x; cases x <;> simp

-- INGVariant is imported from Studies/Eckert2008
-- Burnett's *-ing* = .velar, *-in'* = .apical

-- ============================================================================
-- §2. Meaning: grounded in Eckert–Montague lift
-- ============================================================================

/-! Eckert fields (Burnett example (10)):
- [*-ing*] = {competent, aloof}
- [*-in'*] = {incompetent, friendly}

The meaning function is derived via the Montagovian Individual /
intersection semantics (Burnett footnote 14, Table 1): persona p is
compatible with variant v iff p shares at least one property with v's
Eckert field. -/

/-- The property space for Burnett's simplified example. -/
def burnettSpace : PropertySpace where
  Property := PersonaTrait
  incompatible
    | .competent, .incompetent | .incompetent, .competent => true
    | .friendly, .aloof | .aloof, .friendly => true
    | _, _ => false
  incomp_symm := by intro p q; cases p <;> cases q <;> simp
  incomp_irrefl := by intro p; cases p <;> rfl

/-- Persona membership as a `Finset`. -/
def Persona.toFinset : Persona → Finset PersonaTrait
  | .coolGuy     => {.competent, .friendly}
  | .sternLeader => {.competent, .aloof}
  | .doofus      => {.incompetent, .friendly}
  | .asshole     => {.incompetent, .aloof}

/-- Eckert fields for (ING) (Burnett example (10)). -/
def ingEckertField : INGVariant → Finset PersonaTrait
  | .velar => {.competent, .aloof}
  | .apical => {.incompetent, .friendly}

/-- The ING grounded field: both Eckert fields are consistent. -/
def ingField : GroundedField INGVariant burnettSpace where
  indexedProperties := ingEckertField
  indexed_consistent := by intro v; cases v <;> native_decide

/-- Meaning via the EM intersection lift: persona p is compatible with
    variant v iff p shares ≥1 property with v's Eckert field. -/
def ingMeaning : INGVariant → Persona → Bool
  | .velar,.coolGuy     => true   -- coolGuy has competent ∈ {comp, aloof}
  | .velar,.sternLeader => true   -- sternLeader has comp AND aloof
  | .velar,.asshole     => true   -- asshole has aloof ∈ {comp, aloof}
  | .velar,.doofus      => false  -- doofus has neither comp nor aloof
  | .apical,.coolGuy     => true   -- coolGuy has friendly ∈ {incomp, friendly}
  | .apical,.sternLeader => false  -- sternLeader has neither incomp nor friendly
  | .apical,.asshole     => true   -- asshole has incomp ∈ {incomp, friendly}
  | .apical,.doofus      => true   -- doofus has incomp AND friendly

/-- **Grounding theorem**: the inline meaning function equals the
    theory-layer `emMeaningMI` applied to the ING Eckert fields. -/
theorem ingMeaning_eq_emMeaningMI (v : INGVariant) (p : Persona) :
    ingMeaning v p = emMeaningMI ingField v p.toFinset := by
  cases v <;> cases p <;> native_decide

/-- *-ing* is compatible with 3 personae (Table 1: excludes doofus). -/
theorem ing_compat_count :
    (Finset.univ.filter (fun p => ingMeaning .velar p = true)).card = 3 := by
  native_decide

/-- *-in'* is compatible with 3 personae (Table 1: excludes stern leader). -/
theorem in'_compat_count :
    (Finset.univ.filter (fun p => ingMeaning .apical p = true)).card = 3 := by
  native_decide

-- ============================================================================
-- §3. SMG as belief-based RSA (mathlib-PMF pipeline)
-- ============================================================================

open scoped ENNReal

/-! Each social context is a belief-based RSA over personae (worlds) and
variants (utterances), α = 6 ([burnett-2019] p. 435):

    L₀(p | v) ∝ ⟦v⟧(p) · π(p)      (Bayesian literal listener, `L0k`)
    S₁(v | p) ∝ L₀(p | v)⁶         (`Sk`)
    L₁(p | v) ∝ π(p) · S₁(v | p)   (`L1k`, `PMF.posterior`)

The persona prior enters L₀ directly (Burnett eq. 11): the "naive listener"
weights compatible personae by `π`, not uniformly — this context-dependence
drives style shifting. `meaningE` carries that prior-weighted meaning; the
speaker is the softmax of `L₀⁶` and the listener the Bayesian posterior
against the same prior `π` (which sums to 1 for every context). -/

/-- Prior-weighted literal meaning `⟦v⟧(p) · π(p)`, lifted to `ℝ≥0∞`. -/
def meaningE (π : Persona → ℚ) (v : INGVariant) (p : Persona) : ℝ≥0∞ :=
  if ingMeaning v p then ENNReal.ofReal (π p) else 0

private theorem meaningE_compat {π : Persona → ℚ} {v : INGVariant} {p : Persona}
    (h : ingMeaning v p = true) : meaningE π v p = ENNReal.ofReal (π p) := by
  simp only [meaningE, h, if_true]

private theorem meaningE_incompat {π : Persona → ℚ} {v : INGVariant} {p : Persona}
    (h : ingMeaning v p = false) : meaningE π v p = 0 := by
  simp only [meaningE, h, Bool.false_eq_true, if_false]

private theorem mIncompat {π : Persona → ℚ} {v : INGVariant} {p : Persona}
    (h : ingMeaning v p = false) : meaningE π v p = ENNReal.ofReal 0 := by
  rw [ENNReal.ofReal_zero]; exact meaningE_incompat h

/-- Persona `Finset.sum` expands to its four summands. -/
private theorem sumP (f : Persona → ℝ≥0∞) :
    (∑ p : Persona, f p) = f .coolGuy + f .sternLeader + f .doofus + f .asshole := by
  rw [show (Finset.univ : Finset Persona)
      = {.coolGuy, .sternLeader, .doofus, .asshole} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- Persona `tsum` expands to its four summands. -/
private theorem tsumP (f : Persona → ℝ≥0∞) :
    (∑' p, f p) = f .coolGuy + f .sternLeader + f .doofus + f .asshole := by
  rw [tsum_fintype]; exact sumP f

/-- **Denominator value** `D_v = Σ_p ⟦v⟧(p)·π(p)`, assembled from the four
per-persona meaning values (`ENNReal.ofReal` of `π p` or `0`). -/
theorem D_val {π : Persona → ℚ} {v : INGVariant} {mc ms md ma s : ℝ}
    (hc : meaningE π v .coolGuy = ENNReal.ofReal mc)
    (hs : meaningE π v .sternLeader = ENNReal.ofReal ms)
    (hd : meaningE π v .doofus = ENNReal.ofReal md)
    (ha : meaningE π v .asshole = ENNReal.ofReal ma)
    (hcnn : 0 ≤ mc) (hsnn : 0 ≤ ms) (hdnn : 0 ≤ md) (hann : 0 ≤ ma)
    (hsum : mc + ms + md + ma = s) :
    (∑' p, meaningE π v p) = ENNReal.ofReal s := by
  rw [tsumP, hc, hs, hd, ha, ← ENNReal.ofReal_add hcnn hsnn,
    ← ENNReal.ofReal_add (add_nonneg hcnn hsnn) hdnn,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg hcnn hsnn) hdnn) hann, hsum]

/-- Variant `tsum` expands to its two summands. -/
private theorem sumV (f : INGVariant → ℝ≥0∞) : (∑' v, f v) = f .velar + f .apical := by
  rw [tsum_fintype, show (Finset.univ : Finset INGVariant) = {.velar, .apical} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton]

private theorem meaning_ne_zero (π : Persona → ℚ) (hπ : ∀ p, 0 < π p) (v : INGVariant) :
    (∑' p, meaningE π v p) ≠ 0 := by
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨.coolGuy, ?_⟩
  have hv : ingMeaning v .coolGuy = true := by cases v <;> rfl
  simp only [meaningE, hv, if_true]
  exact (ENNReal.ofReal_pos.mpr (by exact_mod_cast hπ .coolGuy)).ne'

private theorem meaning_ne_top (π : Persona → ℚ) (v : INGVariant) :
    (∑' p, meaningE π v p) ≠ ⊤ := by
  rw [tsum_fintype]
  refine ENNReal.sum_ne_top.mpr fun p _ => ?_
  simp only [meaningE]; split
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top

/-- Prior-weighted literal listener `L₀(· | v) : PMF Persona`. -/
noncomputable def L0k (π : Persona → ℚ) (hπ : ∀ p, 0 < π p) (v : INGVariant) : PMF Persona :=
  RSA.L0OfMeaning (meaningE π) v (meaning_ne_zero π hπ v) (meaning_ne_top π v)

/-- **L0 value**: `L₀(p | v) = ⟦v⟧(p)·π(p) / D_v`, an exact `ENNReal.ofReal`. -/
theorem L0_val (π : Persona → ℚ) (hπ : ∀ p, 0 < π p) {v : INGVariant} {p : Persona}
    {m d q : ℝ} (hm : meaningE π v p = ENNReal.ofReal m)
    (hd : (∑' p', meaningE π v p') = ENNReal.ofReal d)
    (hmnn : 0 ≤ m) (hdpos : 0 < d) (hq : m / d = q) :
    L0k π hπ v p = ENNReal.ofReal q := by
  rw [L0k, RSA.L0OfMeaning_apply, hm, hd, ← ENNReal.ofReal_inv_of_pos hdpos,
    ← ENNReal.ofReal_mul hmnn, ← div_eq_mul_inv, hq]

private theorem L0k_ne_zero (π : Persona → ℚ) (hπ : ∀ p, 0 < π p) {v : INGVariant} {p : Persona}
    (hm : meaningE π v p ≠ 0) : L0k π hπ v p ≠ 0 := by
  rw [L0k, ← PMF.mem_support_iff, RSA.L0OfMeaning, PMF.mem_support_normalize_iff]; exact hm

private theorem L0k_tsum_ne_top (π : Persona → ℚ) (hπ : ∀ p, 0 < π p) (p : Persona) :
    (∑' v, (L0k π hπ v p) ^ 6) ≠ ⊤ := by
  rw [sumV]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.pow_ne_top (PMF.apply_ne_top _ _),
    ENNReal.pow_ne_top (PMF.apply_ne_top _ _)⟩

private theorem L0k_pow_tsum_ne_zero (π : Persona → ℚ) (hπ : ∀ p, 0 < π p) (p : Persona) :
    (∑' v, (L0k π hπ v p) ^ 6) ≠ 0 := by
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ?_
  obtain ⟨v, hv⟩ : ∃ v, ingMeaning v p = true := by
    cases p
    · exact ⟨.velar, rfl⟩
    · exact ⟨.velar, rfl⟩
    · exact ⟨.apical, rfl⟩
    · exact ⟨.velar, rfl⟩
  refine ⟨v, pow_ne_zero 6 (L0k_ne_zero π hπ ?_)⟩
  simp only [meaningE, hv, if_true]
  exact (ENNReal.ofReal_pos.mpr (by exact_mod_cast hπ p)).ne'

/-- **Speaker** `S₁(· | p) : PMF INGVariant`, softmax of `L₀⁶` (α = 6). -/
noncomputable def Sk (π : Persona → ℚ) (hπ : ∀ p, 0 < π p) (p : Persona) : PMF INGVariant :=
  PMF.normalize (fun v => (L0k π hπ v p) ^ 6)
    (L0k_pow_tsum_ne_zero π hπ p) (L0k_tsum_ne_top π hπ p)

/-- **Speaker value**: `S₁(v | p) = L₀(p|v)⁶ / Σ_v' L₀(p|v')⁶`. -/
theorem Sk_val (π : Persona → ℚ) (hπ : ∀ p, 0 < π p) {v : INGVariant} {p : Persona}
    {a z q : ℝ} (ha : L0k π hπ v p = ENNReal.ofReal a)
    (hz : (∑' v', (L0k π hπ v' p) ^ 6) = ENNReal.ofReal z)
    (hann : 0 ≤ a) (hzpos : 0 < z) (hq : a ^ 6 / z = q) :
    Sk π hπ p v = ENNReal.ofReal q := by
  rw [Sk, PMF.normalize_apply]
  show (L0k π hπ v p) ^ 6 * (∑' v', (L0k π hπ v' p) ^ 6)⁻¹ = _
  rw [ha, hz, ← ENNReal.ofReal_pow hann, ← ENNReal.ofReal_inv_of_pos hzpos,
    ← ENNReal.ofReal_mul (by positivity), ← div_eq_mul_inv, hq]

/-- **Speaker `Z` value**: `Σ_v L₀(p|v)⁶`, assembled from the two `L0_val`s. -/
theorem SkZ_val (π : Persona → ℚ) (hπ : ∀ p, 0 < π p) {p : Persona} {a b z : ℝ}
    (ha : L0k π hπ .velar p = ENNReal.ofReal a) (hb : L0k π hπ .apical p = ENNReal.ofReal b)
    (hann : 0 ≤ a) (hbnn : 0 ≤ b) (hz : a ^ 6 + b ^ 6 = z) :
    (∑' v, (L0k π hπ v p) ^ 6) = ENNReal.ofReal z := by
  rw [sumV, ha, hb, ← ENNReal.ofReal_pow hann, ← ENNReal.ofReal_pow hbnn,
    ← ENNReal.ofReal_add (by positivity) (by positivity), hz]

/-- **Endorsement reduction (`<`)**: `S₁` prefers `v₂` iff `L₀⁶` does. -/
theorem Sk_lt_iff (π : Persona → ℚ) (hπ : ∀ p, 0 < π p) {p : Persona} (v₁ v₂ : INGVariant) :
    Sk π hπ p v₁ < Sk π hπ p v₂ ↔ (L0k π hπ v₁ p) ^ 6 < (L0k π hπ v₂ p) ^ 6 := by
  rw [Sk, PMF.normalize_lt_iff_lt]

private theorem Sk_ne_zero (π : Persona → ℚ) (hπ : ∀ p, 0 < π p) {v : INGVariant} {p : Persona}
    (hm : meaningE π v p ≠ 0) : Sk π hπ p v ≠ 0 := by
  rw [Sk, ← PMF.mem_support_iff, PMF.mem_support_normalize_iff]
  exact pow_ne_zero 6 (L0k_ne_zero π hπ hm)

/-- The persona prior sums to `1` (every context is a distribution). -/
theorem prior_pmf_sum (π : Persona → ℚ) (hπ : ∀ p, 0 ≤ π p)
    (h : π .coolGuy + π .sternLeader + π .doofus + π .asshole = 1) :
    (∑ p : Persona, ENNReal.ofReal (π p)) = 1 := by
  have hn : ∀ p, (0 : ℝ) ≤ (π p : ℝ) := fun p => by exact_mod_cast hπ p
  rw [sumP, ← ENNReal.ofReal_add (hn _) (hn _),
    ← ENNReal.ofReal_add (add_nonneg (hn _) (hn _)) (hn _),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (hn _) (hn _)) (hn _)) (hn _),
    show ((π .coolGuy : ℝ) + π .sternLeader + π .doofus + π .asshole) = 1 from by exact_mod_cast h,
    ENNReal.ofReal_one]

/-- The listener's persona prior `π : PMF Persona`. -/
noncomputable def priorK (π : Persona → ℚ) (h1 : (∑ p : Persona, ENNReal.ofReal (π p)) = 1) :
    PMF Persona :=
  PMF.ofFintype (fun p => ENNReal.ofReal (π p)) h1

@[simp] theorem priorK_apply (π : Persona → ℚ) (h1 : (∑ p : Persona, ENNReal.ofReal (π p)) = 1)
    (p : Persona) : priorK π h1 p = ENNReal.ofReal (π p) := rfl

theorem marg_ne_zero (π : Persona → ℚ) (hπ : ∀ p, 0 < π p)
    (h1 : (∑ p : Persona, ENNReal.ofReal (π p)) = 1) (v : INGVariant) :
    PMF.marginal (Sk π hπ) (priorK π h1) v ≠ 0 := by
  have hv : ingMeaning v .coolGuy = true := by cases v <;> rfl
  have hm : meaningE π v .coolGuy ≠ 0 := by
    simp only [meaningE, hv, if_true]; exact (ENNReal.ofReal_pos.mpr (by exact_mod_cast hπ _)).ne'
  refine PMF.marginal_ne_zero (Sk π hπ) (priorK π h1) v (a := .coolGuy) ?_ (Sk_ne_zero π hπ hm)
  rw [priorK_apply]; exact (ENNReal.ofReal_pos.mpr (by exact_mod_cast hπ _)).ne'

/-- **Pragmatic listener** `L₁(· | v) : PMF Persona`, the Bayesian posterior. -/
noncomputable def L1k (π : Persona → ℚ) (hπ : ∀ p, 0 < π p)
    (h1 : (∑ p : Persona, ENNReal.ofReal (π p)) = 1) (v : INGVariant) : PMF Persona :=
  PMF.posterior (Sk π hπ) (priorK π h1) v (marg_ne_zero π hπ h1 v)

/-- **Listener reduction (`<`)**: `L₁` prefers `p₂` iff the prior-weighted
speaker scores do; the marginal cancels. -/
theorem L1_lt_iff (π : Persona → ℚ) (hπ : ∀ p, 0 < π p)
    (h1 : (∑ p : Persona, ENNReal.ofReal (π p)) = 1) (v : INGVariant) (p₁ p₂ : Persona) :
    L1k π hπ h1 v p₁ < L1k π hπ h1 v p₂ ↔
      ENNReal.ofReal (π p₁) * Sk π hπ p₁ v < ENNReal.ofReal (π p₂) * Sk π hπ p₂ v := by
  rw [L1k, PMF.posterior_lt_iff_score_lt, priorK_apply, priorK_apply]

-- ============================================================================
-- §3a. Context-specific configurations
-- ============================================================================

/-- Casual-context prior (Burnett Table 2): voters at the barbecue
    think Obama is aloof (personae with aloof get more weight). -/
def casualPrior : Persona → ℚ
  | .sternLeader => 3/10
  | .coolGuy     => 2/10
  | .asshole     => 3/10
  | .doofus      => 2/10

theorem casualPos : ∀ p, 0 < casualPrior p := by intro p; cases p <;> norm_num [casualPrior]

/-- Speaker at the casual context. -/
noncomputable abbrev casualSk : Persona → PMF INGVariant := Sk casualPrior casualPos

/-- Careful-context prior (Burnett Table 5): journalists think Obama
    is incompetent (incompetent personae get more weight). -/
def carefulPrior : Persona → ℚ
  | .sternLeader => 2/10
  | .coolGuy     => 2/10
  | .asshole     => 3/10
  | .doofus      => 3/10

theorem carefulPos : ∀ p, 0 < carefulPrior p := by intro p; cases p <;> norm_num [carefulPrior]

/-- Speaker at the careful context. -/
noncomputable abbrev carefulSk : Persona → PMF INGVariant := Sk carefulPrior carefulPos

/-- Rice: uniform prior — unfamiliar politician (Burnett Table 10). -/
def ricePrior : Persona → ℚ
  | _ => 1/4

theorem ricePos : ∀ p, 0 < ricePrior p := by intro p; cases p <;> norm_num [ricePrior]
theorem riceSum1 : (∑ p : Persona, ENNReal.ofReal (ricePrior p)) = 1 :=
  prior_pmf_sum ricePrior (fun p => (ricePos p).le) (by norm_num [ricePrior])

/-- Listener for the Rice item (uniform prior). -/
noncomputable abbrev riceL1 : INGVariant → PMF Persona := L1k ricePrior ricePos riceSum1

/-- Pelosi: listeners believe she is inarticulate (Burnett Table 13). -/
def pelosiPrior : Persona → ℚ
  | .sternLeader => 5/100
  | .coolGuy     => 5/100
  | .asshole     => 45/100
  | .doofus      => 45/100

theorem pelosiPos : ∀ p, 0 < pelosiPrior p := by intro p; cases p <;> norm_num [pelosiPrior]
theorem pelosiSum1 : (∑ p : Persona, ENNReal.ofReal (pelosiPrior p)) = 1 :=
  prior_pmf_sum pelosiPrior (fun p => (pelosiPos p).le) (by norm_num [pelosiPrior])

/-- Listener for the Pelosi item. -/
noncomputable abbrev pelosiL1 : INGVariant → PMF Persona := L1k pelosiPrior pelosiPos pelosiSum1

/-- Bush: listeners almost certain he is {inarticulate, aloof}
    (Burnett Table 15). -/
def bushPrior : Persona → ℚ
  | .sternLeader => 1/100
  | .coolGuy     => 1/100
  | .asshole     => 97/100
  | .doofus      => 1/100

theorem bushPos : ∀ p, 0 < bushPrior p := by intro p; cases p <;> norm_num [bushPrior]
theorem bushSum1 : (∑ p : Persona, ENNReal.ofReal (bushPrior p)) = 1 :=
  prior_pmf_sum bushPrior (fun p => (bushPos p).le) (by norm_num [bushPrior])

/-- Listener for the Bush item. -/
noncomputable abbrev bushL1 : INGVariant → PMF Persona := L1k bushPrior bushPos bushSum1

-- ============================================================================
-- §3b. Certified numeric values
-- ============================================================================

/-! ### Denominators, literal-listener, and speaker values -/

-- casual
private theorem D_casual_velar :
    (∑' p, meaningE casualPrior .velar p) = ENNReal.ofReal (4/5) :=
  D_val (meaningE_compat (by decide)) (meaningE_compat (by decide))
    (mIncompat (by decide)) (meaningE_compat (by decide))
    (by norm_num [casualPrior]) (by norm_num [casualPrior])
    (le_refl 0) (by norm_num [casualPrior])
    (by norm_num [casualPrior])
private theorem D_casual_apical :
    (∑' p, meaningE casualPrior .apical p) = ENNReal.ofReal (7/10) :=
  D_val (meaningE_compat (by decide)) (mIncompat (by decide))
    (meaningE_compat (by decide)) (meaningE_compat (by decide))
    (by norm_num [casualPrior]) (le_refl 0)
    (by norm_num [casualPrior]) (by norm_num [casualPrior])
    (by norm_num [casualPrior])
private theorem L0_casual_velar_coolGuy :
    L0k casualPrior casualPos .velar .coolGuy = ENNReal.ofReal (1/4) :=
  L0_val casualPrior casualPos (meaningE_compat (by decide)) D_casual_velar
    (by norm_num [casualPrior]) (by norm_num) (by norm_num [casualPrior])
private theorem L0_casual_apical_coolGuy :
    L0k casualPrior casualPos .apical .coolGuy = ENNReal.ofReal (2/7) :=
  L0_val casualPrior casualPos (meaningE_compat (by decide)) D_casual_apical
    (by norm_num [casualPrior]) (by norm_num) (by norm_num [casualPrior])
private theorem L0_casual_velar_sternLeader :
    L0k casualPrior casualPos .velar .sternLeader = ENNReal.ofReal (3/8) :=
  L0_val casualPrior casualPos (meaningE_compat (by decide)) D_casual_velar
    (by norm_num [casualPrior]) (by norm_num) (by norm_num [casualPrior])
private theorem L0_casual_apical_sternLeader :
    L0k casualPrior casualPos .apical .sternLeader = ENNReal.ofReal 0 :=
  L0_val casualPrior casualPos (mIncompat (by decide)) D_casual_apical
    (le_refl 0) (by norm_num) (by norm_num)
private theorem L0_casual_velar_doofus :
    L0k casualPrior casualPos .velar .doofus = ENNReal.ofReal 0 :=
  L0_val casualPrior casualPos (mIncompat (by decide)) D_casual_velar
    (le_refl 0) (by norm_num) (by norm_num)
private theorem L0_casual_apical_doofus :
    L0k casualPrior casualPos .apical .doofus = ENNReal.ofReal (2/7) :=
  L0_val casualPrior casualPos (meaningE_compat (by decide)) D_casual_apical
    (by norm_num [casualPrior]) (by norm_num) (by norm_num [casualPrior])
private theorem L0_casual_velar_asshole :
    L0k casualPrior casualPos .velar .asshole = ENNReal.ofReal (3/8) :=
  L0_val casualPrior casualPos (meaningE_compat (by decide)) D_casual_velar
    (by norm_num [casualPrior]) (by norm_num) (by norm_num [casualPrior])
private theorem L0_casual_apical_asshole :
    L0k casualPrior casualPos .apical .asshole = ENNReal.ofReal (3/7) :=
  L0_val casualPrior casualPos (meaningE_compat (by decide)) D_casual_apical
    (by norm_num [casualPrior]) (by norm_num) (by norm_num [casualPrior])

-- careful
private theorem D_careful_velar :
    (∑' p, meaningE carefulPrior .velar p) = ENNReal.ofReal (7/10) :=
  D_val (meaningE_compat (by decide)) (meaningE_compat (by decide))
    (mIncompat (by decide)) (meaningE_compat (by decide))
    (by norm_num [carefulPrior]) (by norm_num [carefulPrior])
    (le_refl 0) (by norm_num [carefulPrior])
    (by norm_num [carefulPrior])
private theorem D_careful_apical :
    (∑' p, meaningE carefulPrior .apical p) = ENNReal.ofReal (4/5) :=
  D_val (meaningE_compat (by decide)) (mIncompat (by decide))
    (meaningE_compat (by decide)) (meaningE_compat (by decide))
    (by norm_num [carefulPrior]) (le_refl 0)
    (by norm_num [carefulPrior]) (by norm_num [carefulPrior])
    (by norm_num [carefulPrior])
private theorem L0_careful_velar_coolGuy :
    L0k carefulPrior carefulPos .velar .coolGuy = ENNReal.ofReal (2/7) :=
  L0_val carefulPrior carefulPos (meaningE_compat (by decide)) D_careful_velar
    (by norm_num [carefulPrior]) (by norm_num) (by norm_num [carefulPrior])
private theorem L0_careful_apical_coolGuy :
    L0k carefulPrior carefulPos .apical .coolGuy = ENNReal.ofReal (1/4) :=
  L0_val carefulPrior carefulPos (meaningE_compat (by decide)) D_careful_apical
    (by norm_num [carefulPrior]) (by norm_num) (by norm_num [carefulPrior])

-- rice
private theorem D_rice_velar :
    (∑' p, meaningE ricePrior .velar p) = ENNReal.ofReal (3/4) :=
  D_val (meaningE_compat (by decide)) (meaningE_compat (by decide))
    (mIncompat (by decide)) (meaningE_compat (by decide))
    (by norm_num [ricePrior]) (by norm_num [ricePrior])
    (le_refl 0) (by norm_num [ricePrior])
    (by norm_num [ricePrior])
private theorem D_rice_apical :
    (∑' p, meaningE ricePrior .apical p) = ENNReal.ofReal (3/4) :=
  D_val (meaningE_compat (by decide)) (mIncompat (by decide))
    (meaningE_compat (by decide)) (meaningE_compat (by decide))
    (by norm_num [ricePrior]) (le_refl 0)
    (by norm_num [ricePrior]) (by norm_num [ricePrior])
    (by norm_num [ricePrior])
private theorem L0_rice_velar_coolGuy :
    L0k ricePrior ricePos .velar .coolGuy = ENNReal.ofReal (1/3) :=
  L0_val ricePrior ricePos (meaningE_compat (by decide)) D_rice_velar
    (by norm_num [ricePrior]) (by norm_num) (by norm_num [ricePrior])
private theorem L0_rice_apical_coolGuy :
    L0k ricePrior ricePos .apical .coolGuy = ENNReal.ofReal (1/3) :=
  L0_val ricePrior ricePos (meaningE_compat (by decide)) D_rice_apical
    (by norm_num [ricePrior]) (by norm_num) (by norm_num [ricePrior])
private theorem L0_rice_velar_sternLeader :
    L0k ricePrior ricePos .velar .sternLeader = ENNReal.ofReal (1/3) :=
  L0_val ricePrior ricePos (meaningE_compat (by decide)) D_rice_velar
    (by norm_num [ricePrior]) (by norm_num) (by norm_num [ricePrior])
private theorem L0_rice_apical_sternLeader :
    L0k ricePrior ricePos .apical .sternLeader = ENNReal.ofReal 0 :=
  L0_val ricePrior ricePos (mIncompat (by decide)) D_rice_apical
    (le_refl 0) (by norm_num) (by norm_num)
private theorem L0_rice_velar_doofus :
    L0k ricePrior ricePos .velar .doofus = ENNReal.ofReal 0 :=
  L0_val ricePrior ricePos (mIncompat (by decide)) D_rice_velar
    (le_refl 0) (by norm_num) (by norm_num)
private theorem L0_rice_apical_doofus :
    L0k ricePrior ricePos .apical .doofus = ENNReal.ofReal (1/3) :=
  L0_val ricePrior ricePos (meaningE_compat (by decide)) D_rice_apical
    (by norm_num [ricePrior]) (by norm_num) (by norm_num [ricePrior])
private theorem L0_rice_velar_asshole :
    L0k ricePrior ricePos .velar .asshole = ENNReal.ofReal (1/3) :=
  L0_val ricePrior ricePos (meaningE_compat (by decide)) D_rice_velar
    (by norm_num [ricePrior]) (by norm_num) (by norm_num [ricePrior])
private theorem L0_rice_apical_asshole :
    L0k ricePrior ricePos .apical .asshole = ENNReal.ofReal (1/3) :=
  L0_val ricePrior ricePos (meaningE_compat (by decide)) D_rice_apical
    (by norm_num [ricePrior]) (by norm_num) (by norm_num [ricePrior])
private theorem SkZ_rice_coolGuy :
    (∑' v, (L0k ricePrior ricePos v .coolGuy) ^ 6)
      = ENNReal.ofReal (2/729) :=
  SkZ_val ricePrior ricePos L0_rice_velar_coolGuy L0_rice_apical_coolGuy
    (by norm_num) (by norm_num) (by norm_num)
private theorem SkZ_rice_sternLeader :
    (∑' v, (L0k ricePrior ricePos v .sternLeader) ^ 6)
      = ENNReal.ofReal (1/729) :=
  SkZ_val ricePrior ricePos L0_rice_velar_sternLeader L0_rice_apical_sternLeader
    (by norm_num) (by norm_num) (by norm_num)
private theorem SkZ_rice_doofus :
    (∑' v, (L0k ricePrior ricePos v .doofus) ^ 6)
      = ENNReal.ofReal (1/729) :=
  SkZ_val ricePrior ricePos L0_rice_velar_doofus L0_rice_apical_doofus
    (by norm_num) (by norm_num) (by norm_num)
private theorem SkZ_rice_asshole :
    (∑' v, (L0k ricePrior ricePos v .asshole) ^ 6)
      = ENNReal.ofReal (2/729) :=
  SkZ_val ricePrior ricePos L0_rice_velar_asshole L0_rice_apical_asshole
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_rice_coolGuy_velar :
    Sk ricePrior ricePos .coolGuy .velar = ENNReal.ofReal (1/2) :=
  Sk_val ricePrior ricePos L0_rice_velar_coolGuy SkZ_rice_coolGuy
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_rice_coolGuy_apical :
    Sk ricePrior ricePos .coolGuy .apical = ENNReal.ofReal (1/2) :=
  Sk_val ricePrior ricePos L0_rice_apical_coolGuy SkZ_rice_coolGuy
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_rice_sternLeader_velar :
    Sk ricePrior ricePos .sternLeader .velar = ENNReal.ofReal 1 :=
  Sk_val ricePrior ricePos L0_rice_velar_sternLeader SkZ_rice_sternLeader
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_rice_sternLeader_apical :
    Sk ricePrior ricePos .sternLeader .apical = ENNReal.ofReal 0 :=
  Sk_val ricePrior ricePos L0_rice_apical_sternLeader SkZ_rice_sternLeader
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_rice_doofus_velar :
    Sk ricePrior ricePos .doofus .velar = ENNReal.ofReal 0 :=
  Sk_val ricePrior ricePos L0_rice_velar_doofus SkZ_rice_doofus
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_rice_doofus_apical :
    Sk ricePrior ricePos .doofus .apical = ENNReal.ofReal 1 :=
  Sk_val ricePrior ricePos L0_rice_apical_doofus SkZ_rice_doofus
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_rice_asshole_velar :
    Sk ricePrior ricePos .asshole .velar = ENNReal.ofReal (1/2) :=
  Sk_val ricePrior ricePos L0_rice_velar_asshole SkZ_rice_asshole
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_rice_asshole_apical :
    Sk ricePrior ricePos .asshole .apical = ENNReal.ofReal (1/2) :=
  Sk_val ricePrior ricePos L0_rice_apical_asshole SkZ_rice_asshole
    (by norm_num) (by norm_num) (by norm_num)

-- pelosi
private theorem D_pelosi_velar :
    (∑' p, meaningE pelosiPrior .velar p) = ENNReal.ofReal (11/20) :=
  D_val (meaningE_compat (by decide)) (meaningE_compat (by decide))
    (mIncompat (by decide)) (meaningE_compat (by decide))
    (by norm_num [pelosiPrior]) (by norm_num [pelosiPrior])
    (le_refl 0) (by norm_num [pelosiPrior])
    (by norm_num [pelosiPrior])
private theorem D_pelosi_apical :
    (∑' p, meaningE pelosiPrior .apical p) = ENNReal.ofReal (19/20) :=
  D_val (meaningE_compat (by decide)) (mIncompat (by decide))
    (meaningE_compat (by decide)) (meaningE_compat (by decide))
    (by norm_num [pelosiPrior]) (le_refl 0)
    (by norm_num [pelosiPrior]) (by norm_num [pelosiPrior])
    (by norm_num [pelosiPrior])
private theorem L0_pelosi_velar_coolGuy :
    L0k pelosiPrior pelosiPos .velar .coolGuy = ENNReal.ofReal (1/11) :=
  L0_val pelosiPrior pelosiPos (meaningE_compat (by decide)) D_pelosi_velar
    (by norm_num [pelosiPrior]) (by norm_num) (by norm_num [pelosiPrior])
private theorem L0_pelosi_apical_coolGuy :
    L0k pelosiPrior pelosiPos .apical .coolGuy = ENNReal.ofReal (1/19) :=
  L0_val pelosiPrior pelosiPos (meaningE_compat (by decide)) D_pelosi_apical
    (by norm_num [pelosiPrior]) (by norm_num) (by norm_num [pelosiPrior])
private theorem L0_pelosi_velar_sternLeader :
    L0k pelosiPrior pelosiPos .velar .sternLeader = ENNReal.ofReal (1/11) :=
  L0_val pelosiPrior pelosiPos (meaningE_compat (by decide)) D_pelosi_velar
    (by norm_num [pelosiPrior]) (by norm_num) (by norm_num [pelosiPrior])
private theorem L0_pelosi_apical_sternLeader :
    L0k pelosiPrior pelosiPos .apical .sternLeader = ENNReal.ofReal 0 :=
  L0_val pelosiPrior pelosiPos (mIncompat (by decide)) D_pelosi_apical
    (le_refl 0) (by norm_num) (by norm_num)
private theorem L0_pelosi_velar_doofus :
    L0k pelosiPrior pelosiPos .velar .doofus = ENNReal.ofReal 0 :=
  L0_val pelosiPrior pelosiPos (mIncompat (by decide)) D_pelosi_velar
    (le_refl 0) (by norm_num) (by norm_num)
private theorem L0_pelosi_apical_doofus :
    L0k pelosiPrior pelosiPos .apical .doofus = ENNReal.ofReal (9/19) :=
  L0_val pelosiPrior pelosiPos (meaningE_compat (by decide)) D_pelosi_apical
    (by norm_num [pelosiPrior]) (by norm_num) (by norm_num [pelosiPrior])
private theorem L0_pelosi_velar_asshole :
    L0k pelosiPrior pelosiPos .velar .asshole = ENNReal.ofReal (9/11) :=
  L0_val pelosiPrior pelosiPos (meaningE_compat (by decide)) D_pelosi_velar
    (by norm_num [pelosiPrior]) (by norm_num) (by norm_num [pelosiPrior])
private theorem L0_pelosi_apical_asshole :
    L0k pelosiPrior pelosiPos .apical .asshole = ENNReal.ofReal (9/19) :=
  L0_val pelosiPrior pelosiPos (meaningE_compat (by decide)) D_pelosi_apical
    (by norm_num [pelosiPrior]) (by norm_num) (by norm_num [pelosiPrior])
private theorem SkZ_pelosi_coolGuy :
    (∑' v, (L0k pelosiPrior pelosiPos v .coolGuy) ^ 6)
      = ENNReal.ofReal (48817442/83344647990241) :=
  SkZ_val pelosiPrior pelosiPos L0_pelosi_velar_coolGuy L0_pelosi_apical_coolGuy
    (by norm_num) (by norm_num) (by norm_num)
private theorem SkZ_pelosi_sternLeader :
    (∑' v, (L0k pelosiPrior pelosiPos v .sternLeader) ^ 6)
      = ENNReal.ofReal (1/1771561) :=
  SkZ_val pelosiPrior pelosiPos L0_pelosi_velar_sternLeader L0_pelosi_apical_sternLeader
    (by norm_num) (by norm_num) (by norm_num)
private theorem SkZ_pelosi_doofus :
    (∑' v, (L0k pelosiPrior pelosiPos v .doofus) ^ 6)
      = ENNReal.ofReal (531441/47045881) :=
  SkZ_val pelosiPrior pelosiPos L0_pelosi_velar_doofus L0_pelosi_apical_doofus
    (by norm_num) (by norm_num) (by norm_num)
private theorem SkZ_pelosi_asshole :
    (∑' v, (L0k pelosiPrior pelosiPos v .asshole) ^ 6)
      = ENNReal.ofReal (25943590193922/83344647990241) :=
  SkZ_val pelosiPrior pelosiPos L0_pelosi_velar_asshole L0_pelosi_apical_asshole
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_pelosi_coolGuy_velar :
    Sk pelosiPrior pelosiPos .coolGuy .velar = ENNReal.ofReal (47045881/48817442) :=
  Sk_val pelosiPrior pelosiPos L0_pelosi_velar_coolGuy SkZ_pelosi_coolGuy
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_pelosi_coolGuy_apical :
    Sk pelosiPrior pelosiPos .coolGuy .apical = ENNReal.ofReal (1771561/48817442) :=
  Sk_val pelosiPrior pelosiPos L0_pelosi_apical_coolGuy SkZ_pelosi_coolGuy
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_pelosi_sternLeader_velar :
    Sk pelosiPrior pelosiPos .sternLeader .velar = ENNReal.ofReal 1 :=
  Sk_val pelosiPrior pelosiPos L0_pelosi_velar_sternLeader SkZ_pelosi_sternLeader
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_pelosi_sternLeader_apical :
    Sk pelosiPrior pelosiPos .sternLeader .apical = ENNReal.ofReal 0 :=
  Sk_val pelosiPrior pelosiPos L0_pelosi_apical_sternLeader SkZ_pelosi_sternLeader
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_pelosi_doofus_velar :
    Sk pelosiPrior pelosiPos .doofus .velar = ENNReal.ofReal 0 :=
  Sk_val pelosiPrior pelosiPos L0_pelosi_velar_doofus SkZ_pelosi_doofus
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_pelosi_doofus_apical :
    Sk pelosiPrior pelosiPos .doofus .apical = ENNReal.ofReal 1 :=
  Sk_val pelosiPrior pelosiPos L0_pelosi_apical_doofus SkZ_pelosi_doofus
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_pelosi_asshole_velar :
    Sk pelosiPrior pelosiPos .asshole .velar = ENNReal.ofReal (47045881/48817442) :=
  Sk_val pelosiPrior pelosiPos L0_pelosi_velar_asshole SkZ_pelosi_asshole
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_pelosi_asshole_apical :
    Sk pelosiPrior pelosiPos .asshole .apical = ENNReal.ofReal (1771561/48817442) :=
  Sk_val pelosiPrior pelosiPos L0_pelosi_apical_asshole SkZ_pelosi_asshole
    (by norm_num) (by norm_num) (by norm_num)

-- bush
private theorem D_bush_velar :
    (∑' p, meaningE bushPrior .velar p) = ENNReal.ofReal (99/100) :=
  D_val (meaningE_compat (by decide)) (meaningE_compat (by decide))
    (mIncompat (by decide)) (meaningE_compat (by decide))
    (by norm_num [bushPrior]) (by norm_num [bushPrior])
    (le_refl 0) (by norm_num [bushPrior])
    (by norm_num [bushPrior])
private theorem D_bush_apical :
    (∑' p, meaningE bushPrior .apical p) = ENNReal.ofReal (99/100) :=
  D_val (meaningE_compat (by decide)) (mIncompat (by decide))
    (meaningE_compat (by decide)) (meaningE_compat (by decide))
    (by norm_num [bushPrior]) (le_refl 0)
    (by norm_num [bushPrior]) (by norm_num [bushPrior])
    (by norm_num [bushPrior])
private theorem L0_bush_velar_coolGuy :
    L0k bushPrior bushPos .velar .coolGuy = ENNReal.ofReal (1/99) :=
  L0_val bushPrior bushPos (meaningE_compat (by decide)) D_bush_velar
    (by norm_num [bushPrior]) (by norm_num) (by norm_num [bushPrior])
private theorem L0_bush_apical_coolGuy :
    L0k bushPrior bushPos .apical .coolGuy = ENNReal.ofReal (1/99) :=
  L0_val bushPrior bushPos (meaningE_compat (by decide)) D_bush_apical
    (by norm_num [bushPrior]) (by norm_num) (by norm_num [bushPrior])
private theorem L0_bush_velar_sternLeader :
    L0k bushPrior bushPos .velar .sternLeader = ENNReal.ofReal (1/99) :=
  L0_val bushPrior bushPos (meaningE_compat (by decide)) D_bush_velar
    (by norm_num [bushPrior]) (by norm_num) (by norm_num [bushPrior])
private theorem L0_bush_apical_sternLeader :
    L0k bushPrior bushPos .apical .sternLeader = ENNReal.ofReal 0 :=
  L0_val bushPrior bushPos (mIncompat (by decide)) D_bush_apical
    (le_refl 0) (by norm_num) (by norm_num)
private theorem L0_bush_velar_doofus :
    L0k bushPrior bushPos .velar .doofus = ENNReal.ofReal 0 :=
  L0_val bushPrior bushPos (mIncompat (by decide)) D_bush_velar
    (le_refl 0) (by norm_num) (by norm_num)
private theorem L0_bush_apical_doofus :
    L0k bushPrior bushPos .apical .doofus = ENNReal.ofReal (1/99) :=
  L0_val bushPrior bushPos (meaningE_compat (by decide)) D_bush_apical
    (by norm_num [bushPrior]) (by norm_num) (by norm_num [bushPrior])
private theorem L0_bush_velar_asshole :
    L0k bushPrior bushPos .velar .asshole = ENNReal.ofReal (97/99) :=
  L0_val bushPrior bushPos (meaningE_compat (by decide)) D_bush_velar
    (by norm_num [bushPrior]) (by norm_num) (by norm_num [bushPrior])
private theorem L0_bush_apical_asshole :
    L0k bushPrior bushPos .apical .asshole = ENNReal.ofReal (97/99) :=
  L0_val bushPrior bushPos (meaningE_compat (by decide)) D_bush_apical
    (by norm_num [bushPrior]) (by norm_num) (by norm_num [bushPrior])
private theorem SkZ_bush_coolGuy :
    (∑' v, (L0k bushPrior bushPos v .coolGuy) ^ 6)
      = ENNReal.ofReal (2/941480149401) :=
  SkZ_val bushPrior bushPos L0_bush_velar_coolGuy L0_bush_apical_coolGuy
    (by norm_num) (by norm_num) (by norm_num)
private theorem SkZ_bush_sternLeader :
    (∑' v, (L0k bushPrior bushPos v .sternLeader) ^ 6)
      = ENNReal.ofReal (1/941480149401) :=
  SkZ_val bushPrior bushPos L0_bush_velar_sternLeader L0_bush_apical_sternLeader
    (by norm_num) (by norm_num) (by norm_num)
private theorem SkZ_bush_doofus :
    (∑' v, (L0k bushPrior bushPos v .doofus) ^ 6)
      = ENNReal.ofReal (1/941480149401) :=
  SkZ_val bushPrior bushPos L0_bush_velar_doofus L0_bush_apical_doofus
    (by norm_num) (by norm_num) (by norm_num)
private theorem SkZ_bush_asshole :
    (∑' v, (L0k bushPrior bushPos v .asshole) ^ 6)
      = ENNReal.ofReal (1665944009858/941480149401) :=
  SkZ_val bushPrior bushPos L0_bush_velar_asshole L0_bush_apical_asshole
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bush_coolGuy_velar :
    Sk bushPrior bushPos .coolGuy .velar = ENNReal.ofReal (1/2) :=
  Sk_val bushPrior bushPos L0_bush_velar_coolGuy SkZ_bush_coolGuy
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bush_coolGuy_apical :
    Sk bushPrior bushPos .coolGuy .apical = ENNReal.ofReal (1/2) :=
  Sk_val bushPrior bushPos L0_bush_apical_coolGuy SkZ_bush_coolGuy
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bush_sternLeader_velar :
    Sk bushPrior bushPos .sternLeader .velar = ENNReal.ofReal 1 :=
  Sk_val bushPrior bushPos L0_bush_velar_sternLeader SkZ_bush_sternLeader
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bush_sternLeader_apical :
    Sk bushPrior bushPos .sternLeader .apical = ENNReal.ofReal 0 :=
  Sk_val bushPrior bushPos L0_bush_apical_sternLeader SkZ_bush_sternLeader
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bush_doofus_velar :
    Sk bushPrior bushPos .doofus .velar = ENNReal.ofReal 0 :=
  Sk_val bushPrior bushPos L0_bush_velar_doofus SkZ_bush_doofus
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bush_doofus_apical :
    Sk bushPrior bushPos .doofus .apical = ENNReal.ofReal 1 :=
  Sk_val bushPrior bushPos L0_bush_apical_doofus SkZ_bush_doofus
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bush_asshole_velar :
    Sk bushPrior bushPos .asshole .velar = ENNReal.ofReal (1/2) :=
  Sk_val bushPrior bushPos L0_bush_velar_asshole SkZ_bush_asshole
    (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bush_asshole_apical :
    Sk bushPrior bushPos .asshole .apical = ENNReal.ofReal (1/2) :=
  Sk_val bushPrior bushPos L0_bush_apical_asshole SkZ_bush_asshole
    (by norm_num) (by norm_num) (by norm_num)

/-! ### Bush bulletproofing: exact posterior values -/

private theorem ennreal_9_10 : (9 / 10 : ℝ≥0∞) = ENNReal.ofReal (9 / 10) := by
  rw [← ENNReal.ofReal_ofNat (n := 9), ← ENNReal.ofReal_ofNat (n := 10),
    ← ENNReal.ofReal_div_of_pos (by norm_num)]

private theorem bushMarg_velar :
    PMF.marginal (Sk bushPrior bushPos) (priorK bushPrior bushSum1) .velar
      = ENNReal.ofReal (1 / 2) := by
  show ((priorK bushPrior bushSum1).bind (Sk bushPrior bushPos)) .velar = _
  rw [PMF.bind_apply_eq_finset_sum, sumP]
  simp only [priorK_apply, Sk_bush_coolGuy_velar, Sk_bush_sternLeader_velar,
    Sk_bush_doofus_velar, Sk_bush_asshole_velar]
  rw [← ENNReal.ofReal_mul (by norm_num [bushPrior]),
    ← ENNReal.ofReal_mul (by norm_num [bushPrior]),
    ← ENNReal.ofReal_mul (by norm_num [bushPrior]),
    ← ENNReal.ofReal_mul (by norm_num [bushPrior]),
    ← ENNReal.ofReal_add (by norm_num [bushPrior]) (by norm_num [bushPrior]),
    ← ENNReal.ofReal_add (by norm_num [bushPrior]) (by norm_num [bushPrior]),
    ← ENNReal.ofReal_add (by norm_num [bushPrior]) (by norm_num [bushPrior])]
  congr 1; norm_num [bushPrior]

private theorem bushMarg_apical :
    PMF.marginal (Sk bushPrior bushPos) (priorK bushPrior bushSum1) .apical
      = ENNReal.ofReal (1 / 2) := by
  show ((priorK bushPrior bushSum1).bind (Sk bushPrior bushPos)) .apical = _
  rw [PMF.bind_apply_eq_finset_sum, sumP]
  simp only [priorK_apply, Sk_bush_coolGuy_apical, Sk_bush_sternLeader_apical,
    Sk_bush_doofus_apical, Sk_bush_asshole_apical]
  rw [← ENNReal.ofReal_mul (by norm_num [bushPrior]),
    ← ENNReal.ofReal_mul (by norm_num [bushPrior]),
    ← ENNReal.ofReal_mul (by norm_num [bushPrior]),
    ← ENNReal.ofReal_mul (by norm_num [bushPrior]),
    ← ENNReal.ofReal_add (by norm_num [bushPrior]) (by norm_num [bushPrior]),
    ← ENNReal.ofReal_add (by norm_num [bushPrior]) (by norm_num [bushPrior]),
    ← ENNReal.ofReal_add (by norm_num [bushPrior]) (by norm_num [bushPrior])]
  congr 1; norm_num [bushPrior]

private theorem bush_L1_velar_asshole :
    bushL1 .velar .asshole = ENNReal.ofReal (97 / 100) := by
  rw [bushL1, L1k, PMF.posterior_apply, priorK_apply, Sk_bush_asshole_velar, bushMarg_velar,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    ← ENNReal.ofReal_mul (by norm_num [bushPrior]), ← ENNReal.ofReal_mul (by norm_num [bushPrior])]
  congr 1; norm_num [bushPrior]

private theorem bush_L1_apical_asshole :
    bushL1 .apical .asshole = ENNReal.ofReal (97 / 100) := by
  rw [bushL1, L1k, PMF.posterior_apply, priorK_apply, Sk_bush_asshole_apical, bushMarg_apical,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    ← ENNReal.ofReal_mul (by norm_num [bushPrior]), ← ENNReal.ofReal_mul (by norm_num [bushPrior])]
  congr 1; norm_num [bushPrior]

-- ============================================================================
-- §4. Speaker predictions (casual context)
-- ============================================================================

section casual

/-- Cool-guy at the barbecue prefers *-in'* over *-ing* (~69% vs ~31%).
    Burnett (p. 435): "we predict that Obama will use -in' around **69%**
    of the time [...] which is close to what Labov found" (72%). -/
theorem casual_coolGuy_prefers_in' :
    casualSk .coolGuy .apical > casualSk .coolGuy .velar := by
  rw [gt_iff_lt, Sk_lt_iff, L0_casual_velar_coolGuy, L0_casual_apical_coolGuy,
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- Stern leader only uses *-ing*: *-in'* is incompatible (Table 1).
    This predicts ~0% *-in'* in formal contexts where Obama constructs
    the stern leader. -/
theorem casual_sternLeader_prefers_ing :
    casualSk .sternLeader .velar > casualSk .sternLeader .apical := by
  rw [gt_iff_lt, Sk_lt_iff, L0_casual_apical_sternLeader, L0_casual_velar_sternLeader,
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- The doofus only uses *-in'*: *-ing* is incompatible (Table 1). -/
theorem casual_doofus_prefers_in' :
    casualSk .doofus .apical > casualSk .doofus .velar := by
  rw [gt_iff_lt, Sk_lt_iff, L0_casual_velar_doofus, L0_casual_apical_doofus,
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

end casual

-- ============================================================================
-- §5. Style shifting: casual → careful
-- ============================================================================

section styleShifting

/-- In the careful context, the cool-guy now prefers *-ing* over *-in'*.
    The prior shift reverses the informativity ranking. -/
theorem careful_coolGuy_prefers_ing :
    carefulSk .coolGuy .velar > carefulSk .coolGuy .apical := by
  rw [gt_iff_lt, Sk_lt_iff, L0_careful_apical_coolGuy, L0_careful_velar_coolGuy,
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

end styleShifting

-- ============================================================================
-- §6. /t/ release: listener interpretation ([podesva-etal-2015])
-- ============================================================================

/-! The /t/ release variable has the same mathematical structure as (ING).
Relabeling: articulate↔competent, inarticulate↔incompetent (same friendly/aloof).
Variants: released [tʰ]↔*-ing*, flapped [ɾ]↔*-in'*.
The Eckert fields are structurally identical (Burnett example (19)):
  [tʰ] = {articulate, aloof},  [ɾ] = {inarticulate, friendly}.

We reuse the same types and meaning function, since the math is isomorphic.
The personae reinterpret as:
  coolGuy ↔ {articulate, friendly},
  sternLeader ↔ {articulate, aloof},
  doofus ↔ {inarticulate, friendly},
  asshole ↔ {inarticulate, aloof}. -/

/-- The asshole prefers *-in'* in the casual context (both variants are
    compatible, but *-in'* is more informative given the prior). -/
theorem casual_asshole_prefers_in' :
    casualSk .asshole .apical > casualSk .asshole .velar := by
  rw [gt_iff_lt, Sk_lt_iff, L0_casual_velar_asshole, L0_casual_apical_asshole,
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

section tRelease

/-- Rice: released /t/ triggers {articulate, aloof} = stern leader
    (Burnett Table 11). With uniform prior, the exclusive variant
    (only *-ing* compatible) gets double the L1 weight. -/
theorem rice_released_sternLeader :
    riceL1 .velar .sternLeader > riceL1 .velar .coolGuy := by
  rw [gt_iff_lt, L1_lt_iff, Sk_rice_coolGuy_velar, Sk_rice_sternLeader_velar,
    ← ENNReal.ofReal_mul (by norm_num [ricePrior]),
    ← ENNReal.ofReal_mul (by norm_num [ricePrior]),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num [ricePrior])]
  norm_num [ricePrior]

/-- Rice: flapped /t/ triggers {inarticulate, friendly} = doofus
    (Burnett Table 11). Symmetric to the released case. -/
theorem rice_flapped_doofus :
    riceL1 .apical .doofus > riceL1 .apical .coolGuy := by
  rw [gt_iff_lt, L1_lt_iff, Sk_rice_coolGuy_apical, Sk_rice_doofus_apical,
    ← ENNReal.ofReal_mul (by norm_num [ricePrior]),
    ← ENNReal.ofReal_mul (by norm_num [ricePrior]),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num [ricePrior])]
  norm_num [ricePrior]

/-- Pelosi: released /t/ predominantly triggers {inarticulate, aloof} —
    the strong prior that she is inarticulate overwhelms the released /t/
    association with articulateness (Burnett Table 14). -/
theorem pelosi_released_inarticAloof :
    pelosiL1 .velar .asshole > pelosiL1 .velar .sternLeader := by
  rw [gt_iff_lt, L1_lt_iff, Sk_pelosi_sternLeader_velar, Sk_pelosi_asshole_velar,
    ← ENNReal.ofReal_mul (by norm_num [pelosiPrior]),
    ← ENNReal.ofReal_mul (by norm_num [pelosiPrior]),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num [pelosiPrior])]
  norm_num [pelosiPrior]

/-- Pelosi: flapped /t/ triggers {inarticulate, friendly} (Table 14). -/
theorem pelosi_flapped_friendly :
    pelosiL1 .apical .doofus > pelosiL1 .apical .asshole := by
  rw [gt_iff_lt, L1_lt_iff, Sk_pelosi_asshole_apical, Sk_pelosi_doofus_apical,
    ← ENNReal.ofReal_mul (by norm_num [pelosiPrior]),
    ← ENNReal.ofReal_mul (by norm_num [pelosiPrior]),
    ENNReal.ofReal_lt_ofReal_iff (by norm_num [pelosiPrior])]
  norm_num [pelosiPrior]

/-- Bush "bulletproofing" (Burnett p. 444, Table 16): the prior is so
    extreme that variant choice has no practical effect. Both released and
    flapped /t/ yield >90% {inarticulate, aloof}. -/
theorem bush_bulletproofing :
    bushL1 .velar .asshole > 9 / 10 ∧
    bushL1 .apical .asshole > 9 / 10 := by
  simp only [gt_iff_lt, ennreal_9_10, bush_L1_velar_asshole, bush_L1_apical_asshole]
  exact ⟨(ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num),
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)⟩

end tRelease

-- ============================================================================
-- §7. Cross-study bridge: Labov 2012 data ↔ SMG predictions
-- ============================================================================

/-- Cross-reference: the SMG model's qualitative predictions match the
    directional pattern observed in [labov-2012]'s data on Obama's
    (ING) rates. The model predicts the cool-guy persona prefers *-in'*
    in casual context and *-ing* in careful context; the data shows
    Obama's *-in'* rate decreasing monotonically from casual (72%)
    through careful (33%) to formal (3%). -/
theorem smg_matches_labov_direction :
    -- SMG: cool-guy prefers -in' in casual context
    casualSk .coolGuy .apical > casualSk .coolGuy .velar ∧
    -- SMG: cool-guy prefers -ing in careful context
    carefulSk .coolGuy .velar > carefulSk .coolGuy .apical ∧
    -- Observed: casual > careful > formal
    Labov2012.obama_ING.casual > Labov2012.obama_ING.careful ∧
    Labov2012.obama_ING.careful > Labov2012.obama_ING.formal :=
  ⟨casual_coolGuy_prefers_in', careful_coolGuy_prefers_ing,
   by native_decide, by native_decide⟩

-- ============================================================================
-- §8. Social Meaning Games (Definitions 4.1 and 4.3)
-- ============================================================================

/-! Burnett's Social Meaning Game (SMG): a signalling game in which a
speaker's variant choice conveys social information about their persona.
An SMG is an interpretation game in [franke-2011]'s sense, extended with
the speaker's value function μ over personae ([burnett-2019] Def. 4.3).
`toInterpGame` converts any SMG onto the shared signaling-game carrier.

Burnett's own agent dynamics — the informativity speaker (eqs. (12)–(13)),
soft-max persona selection (eqs. (14)–(15)), the Bayesian *naive listener*
(eq. (18)) and the value-inferring *uncovering listener* (eq. (20)) — are
not formalized in this section; the quantitative eq.-(13)-style speaker
lives in the `Sk` pipeline of §3. What this section verifies is the
structural layer: the carrier's *literal* listener on the converted game
captures the exclusion behavior of the meaning function. -/

section smgDefs

/-- A Social Meaning Game ([burnett-2019] Def. 4.1, extended per Def. 4.3
    with the value function): a signalling game where variant choice
    conveys social information.

    - `P`: persona types (social categories the listener is trying to infer)
    - `V`: variant types (linguistic forms the speaker chooses)
    - `prior`: probability distribution over personae
    - `meaning`: whether a variant is compatible with a persona
      (derived from the EM field: `v` means `t` iff the EM lift of `v`
      includes persona `t`)
    - `socialEval`: Def. 4.3's μ — the value the speaker assigns to
      constructing each persona in the context (persona-only, as in the
      paper) -/
structure SocialMeaningGame (P V : Type)
    [Fintype P] [Fintype V]
    [DecidableEq P] [DecidableEq V] where
  /-- Prior probability over personae. -/
  prior : P → ℚ
  /-- Prior is non-negative. -/
  prior_nonneg : ∀ (t : P), 0 ≤ prior t
  /-- Semantic meaning: is variant `v` compatible with persona `t`? -/
  meaning : V → P → Bool
  /-- Def. 4.3's value function μ: how much the speaker values
      constructing persona `t` in the context. -/
  socialEval : P → ℚ

/-- Convert a Social Meaning Game to an interpretation game
([franke-2011]) on the shared signaling-game carrier.

    The mapping:
    - Types = Personae (what the listener tries to infer)
    - Messages = Variants (what the speaker chooses)
    - meaning = SMG meaning (EM field compatibility)
    - prior = SMG prior over personae -/
def SocialMeaningGame.toInterpGame {P V : Type}
    [Fintype P] [Fintype V]
    [DecidableEq P] [DecidableEq V]
    (smg : SocialMeaningGame P V) : InterpGame P V where
  meaning := fun v p => smg.meaning v p = true
  prior := smg.prior

/-- Construct a Social Meaning Game from a grounded field, prior, and
    social evaluation function.

    The meaning function is derived from the EM field: variant `v`
    is compatible with a persona set `p` iff `v`'s indexed properties
    are a subset of `p`'s properties. -/
def fromGroundedField {V : Type} [Fintype V] [DecidableEq V]
    (ps : PropertySpace)
    (gf : GroundedField V ps)
    (personaeSets : Finset (Finset ps.Property))
    [Fintype personaeSets] [DecidableEq personaeSets]
    (prior : personaeSets → ℚ)
    (prior_nonneg : ∀ (t : personaeSets), 0 ≤ prior t)
    (socialEval : personaeSets → ℚ) :
    SocialMeaningGame personaeSets V :=
  { prior := prior
    prior_nonneg := prior_nonneg
    meaning := fun v t => gf.indexedProperties v ⊆ t.val
    socialEval := socialEval }

end smgDefs

/-! The carrier's literal listener on the converted game is *uniform* over
compatible personae. This captures the exclusion structure (which
personae are ruled out by each variant) but not the prior-weighted
refinement — [burnett-2019]'s naive listener proper (eq. (18)) is
Bayesian over the speaker's production rule. The *quantitative*
predictions (≈69% -in' for cool guy at α = α′ = 6, eq. (15); style
shifting) use the belief-based speaker `Sk` of §3 (Burnett eq. (13):
P_S(m|π) ∝ L₀(π|m)^α), which incorporates the context-specific prior
into the meaning function to recover Bayesian conditioning. We
construct an SMG from the study's types and prove structural
properties. -/

section smgBridge

/-- Obama's social value function μ at the barbecue
    ([burnett-2019], Table 6, p. 438).

    Cool guy ({competent, friendly}) is most valued (μ = 2);
    asshole ({incompetent, aloof}) is least (μ = 0).
    The μ function reflects what the speaker (Obama) most wants
    the listener to infer about him in this context. -/
def obamaValues : Persona → ℚ
  | .coolGuy     => 2
  | .sternLeader => 1
  | .doofus      => 1
  | .asshole     => 0

/-- The (ING) Social Meaning Game for the casual context
    ([burnett-2019], Defs. 4.1/4.3 + Table 2 + Table 6).

    This connects the study's types to the §8 game structure,
    exercising `SocialMeaningGame` and `toInterpGame`. -/
def casualSMG : SocialMeaningGame Persona INGVariant where
  prior := casualPrior
  prior_nonneg := by intro p; cases p <;> norm_num [casualPrior]
  meaning := ingMeaning
  socialEval := obamaValues

/-- The SMG meaning is grounded in the Eckert–Montague intersection
    lift — connecting the game structure to the compositional
    semantics layer via `ingMeaning_eq_emMeaningMI`. -/
theorem smg_meaning_grounded (v : INGVariant) (p : Persona) :
    casualSMG.meaning v p = emMeaningMI ingField v p.toFinset :=
  ingMeaning_eq_emMeaningMI v p

/-- The literal listener excludes stern leader after hearing *-in'*
    (incompatible: stern leader = {competent, aloof} shares no
    property with [-in'] = {incompetent, friendly}). -/
theorem smg_L0_in'_excludes_sternLeader :
    casualSMG.toInterpGame.literal .apical .sternLeader = 0 := by
  native_decide

/-- The literal listener excludes doofus after hearing *-ing*
    (incompatible: doofus = {incompetent, friendly} shares no
    property with [-ing] = {competent, aloof}). -/
theorem smg_L0_ing_excludes_doofus :
    casualSMG.toInterpGame.literal .velar .doofus = 0 := by
  native_decide

/-- The literal listener assigns equal probability (1/3) to all
    compatible personae — uniform over ⟦v⟧: since 3 personae are
    compatible with each variant, each gets 1/3.

    This is the structural content of the meaning function: each variant
    partitions personae into compatible (1/3) and incompatible (0). -/
theorem smg_L0_uniform_compatible :
    casualSMG.toInterpGame.literal .velar .coolGuy = 1/3 ∧
    casualSMG.toInterpGame.literal .velar .sternLeader = 1/3 ∧
    casualSMG.toInterpGame.literal .velar .asshole = 1/3 ∧
    casualSMG.toInterpGame.literal .apical .coolGuy = 1/3 ∧
    casualSMG.toInterpGame.literal .apical .asshole = 1/3 ∧
    casualSMG.toInterpGame.literal .apical .doofus = 1/3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end smgBridge

end Burnett2019
