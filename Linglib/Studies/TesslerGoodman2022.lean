import Linglib.Semantics.Degree.Discrete
import Linglib.Semantics.Degree.Kennedy
import Linglib.Pragmatics.RSA.Canonical
import Linglib.Data.Examples.TesslerGoodman2022
import Linglib.Semantics.Quantification.DomainRestriction

/-!
# [tessler-goodman-2022]: Warm (for Winter)
[tessler-goodman-2022] [lassiter-goodman-2017]

Cognitive Science 46 (2022) e13095.

## Core Insight

Comparison class inference uses the SAME uncertain threshold mechanism as
adjective interpretation ([lassiter-goodman-2017]). The listener jointly
infers the degree x AND the comparison class c (Eq. 1):

    L₁(x, c | u, k) ∝ S₁(u | x, c) · P(x | k) · P(c | k)

The comparison class c determines L0's height prior: subordinate uses the
kind's distribution (e.g., basketball players), superordinate uses the
general population (people). The threshold θ is marginalized analytically
following [lassiter-goodman-2017]'s threshold RSA framework (the height priors are identical — see
`personWeight_eq_lassiterGoodman` and `basketballWeight_eq_lassiterGoodman`).

## Main Prediction: Polarity × Expectations Interaction

- "tall basketball player" → superordinate (people) comparison class
- "short basketball player" → subordinate (basketball players) comparison class
- Pattern reverses for jockeys (expected short)

The interaction emerges from RSA reasoning: a speaker saying "tall" about a
basketball player is more informative under superordinate comparison (the
L0 normalization Z_c(tall) differs by comparison class because the height
distribution shifts), so L1 infers superordinate. For "short," subordinate
comparison is more informative.

## Simplifications

- **α = 1** (the paper fits α₁ ≈ 1.45, α₂ ≈ 5.31; α=1 suffices for
  qualitative predictions since S₁ ∝ L₀^α is monotone in α)
- **No utterance costs** (Note 3: costs assumed equal for all utterances,
  so S₁(u | x, c) ∝ L₀(x | u, c)^α; cf. [lassiter-goodman-2017]
  which has C(tall)=C(short)=2, C(∅)=0)
- **Flat comparison class prior** (P(c|k) uniform; the paper's "Flat prior"
  model variant from Table 2; the full model fits basic-level bias +
  frequency effects, but the flat prior already yields the qualitative
  polarity × expectations pattern)
- **Two extreme categories** (basketball=high, jockey=low; the paper uses
  three per item set including a medium control like soccer player/golfer
  where no polarity effect is predicted)

## Model Architecture

Per-kind mathlib-PMF pipeline with latent `ComparisonClass`, world `Height`:
- `meaningE(k, c, u, h)` = P(h | c) · |{θ : ⟦u⟧(h,θ)}|  (marginalized threshold)
- `jointW(k)` world prior = P(h | k)  (L1's kind-specific height prior)
- flat comparison-class prior P(c | k)  (absorbed into `jointW`)
- speaker `Sk` (α = 1, no cost); listener `listenerK` = `RSA.Canonical.L1`

## Verified Predictions

### S1 Endorsement (speaker-level)

| # | Prediction | Kind | Height | Comp. Class | Theorem |
|---|-----------|------|--------|-------------|---------|
| 1 | "tall" endorsed | basketball | h=6 | super | `basketball_tall_endorsed_super` |
| 2 | "tall" NOT endorsed | basketball | h=6 | sub | `basketball_tall_not_endorsed_sub` |
| 3 | "short" endorsed | basketball | h=5 | sub | `basketball_short_endorsed_sub` |
| 4 | "short" NOT endorsed | basketball | h=5 | super | `basketball_short_not_endorsed_super` |
| 5 | "tall" endorsed | jockey | h=4 | sub | `jockey_tall_endorsed_sub` |
| 6 | "tall" NOT endorsed | jockey | h=4 | super | `jockey_tall_not_endorsed_super` |
| 7 | "short" endorsed | jockey | h=4 | super | `jockey_short_endorsed_super` |
| 8 | "short" NOT endorsed | jockey | h=4 | sub | `jockey_short_not_endorsed_sub` |

### L1 Comparison Class Inference (Eq. 1 — the paper's main prediction)

| # | Adj | Kind | Inferred CC | Theorem |
|---|-----|------|-------------|---------|
| 9 | tall | basketball | super | `basketball_tall_infers_super` |
| 10 | short | basketball | sub | `basketball_short_infers_sub` |
| 11 | tall | jockey | sub | `jockey_tall_infers_sub` |
| 12 | short | jockey | super | `jockey_short_infers_super` |

### Alternative Literal Listener (Eq. 6, Fig. 2 — opposite predictions)

| # | Kind | Adj | Literal | Pragmatic | Theorem |
|---|------|-----|---------|-----------|---------|
| 13 | basketball | tall | sub | super (#9) | `literal_basketball_tall_sub` |
| 14 | basketball | short | super | sub (#10) | `literal_basketball_short_super` |
| 15 | jockey | tall | super | sub (#11) | `literal_jockey_tall_super` |
| 16 | jockey | short | sub | super (#12) | `literal_jockey_short_sub` |
-/

set_option autoImplicit false

namespace TesslerGoodman2022

open Degree (Degree Threshold deg thr allDegrees allThresholds Degree.toNat Threshold.toNat)
open Degree (positiveMeaning negativeMeaning)

-- ============================================================================
-- § 1. Domain Types
-- ============================================================================

/-- Discretized height: 0 through 10 in discrete steps (11 values). -/
abbrev Height := Degree 10

/-- Comparison classes: subordinate (the kind itself) or superordinate
    (the general population). -/
inductive ComparisonClass where
  | subordinate   -- compare to the specific kind (basketball players)
  | superordinate -- compare to the broader category (people)
  deriving Repr, DecidableEq, Fintype

/-- Kinds (nominals) that can be modified by adjectives. -/
inductive Kind where
  | person            -- generic person (baseline)
  | basketballPlayer  -- expected to be tall
  | jockey            -- expected to be short
  deriving Repr, DecidableEq, Fintype

/-- Utterances: positive adjective, negative adjective, or silence. -/
inductive Utterance where
  | tall    -- "x is tall"
  | short   -- "x is short"
  | silent  -- say nothing (null utterance)
  deriving Repr, DecidableEq, Fintype

-- ============================================================================
-- § 2. Height Priors (unnormalized weights)
-- ============================================================================

/-- Height weight for generic people: symmetric, peaked at h=5.
    Approximates a discretized normal centered at the population mean. -/
def personHeightWeight (h : Height) : Nat :=
  match h.toNat with
  | 0 => 1 | 1 => 2 | 2 => 5 | 3 => 10 | 4 => 15
  | 5 => 20 | 6 => 15 | 7 => 10 | 8 => 5 | 9 => 2 | _ => 1

/-- Height weight for basketball players: shifted right, peaked at h=7. -/
def basketballHeightWeight (h : Height) : Nat :=
  match h.toNat with
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 5
  | 5 => 10 | 6 => 15 | 7 => 20 | 8 => 15 | 9 => 10 | _ => 5

/-- Height weight for jockeys: shifted left, peaked at h=3. -/
def jockeyHeightWeight (h : Height) : Nat :=
  match h.toNat with
  | 0 => 5 | 1 => 10 | 2 => 15 | 3 => 20 | 4 => 15
  | 5 => 10 | 6 => 5 | 7 => 2 | 8 => 1 | 9 => 0 | _ => 0

/-- Height weight for a given kind: P(h | k) (unnormalized). -/
def heightWeight (k : Kind) : Height → Nat :=
  match k with
  | .person => personHeightWeight
  | .basketballPlayer => basketballHeightWeight
  | .jockey => jockeyHeightWeight

/-- L0's height weight conditioned on comparison class.
    Subordinate uses the kind's own distribution; superordinate uses people. -/
def l0HeightWeight (c : ComparisonClass) (k : Kind) : Height → Nat :=
  match c with
  | .subordinate => heightWeight k
  | .superordinate => personHeightWeight

/-- Comparison class prior weights: P(c | k) (unnormalized).
    Flat prior: subordinate and superordinate equally likely a priori.
    The qualitative polarity × expectations interaction emerges entirely
    from pragmatic reasoning about informativity, not from prior bias.
    (Paper Table 2: "Flat prior" model variant, r² = 0.136 for CC inference.) -/
def compClassWeight (_k : Kind) : ComparisonClass → Nat :=
  λ _ => 1

-- ============================================================================
-- § 3. Semantics: Threshold-Marginalized Meaning
-- ============================================================================

/-- Number of thresholds θ ∈ {0,...,9} satisfying ⟦u⟧(h,θ) = true.

    For tall (`positiveMeaning`): |{θ : h > θ}| = h.toNat
    For short (`negativeMeaning`): |{θ : h < θ}| = 9 - h.toNat
    For silent: 10 (all thresholds pass) -/
def thresholdCount (u : Utterance) (h : Height) : Nat :=
  match u with
  | .tall => h.toNat
  | .short => 9 - h.toNat  -- Nat subtraction floors at 0
  | .silent => 10

/-- Grounding: `thresholdCount .tall` equals the count of thresholds
    satisfying `positiveMeaning`. -/
theorem thresholdCount_tall_eq_card :
    ∀ h : Height, thresholdCount .tall h =
      (Finset.univ.filter (λ θ : Threshold 10 => positiveMeaning h θ)).card := by
  native_decide

/-- Grounding: `thresholdCount .short` equals the count of thresholds
    satisfying `negativeMeaning`. -/
theorem thresholdCount_short_eq_card :
    ∀ h : Height, thresholdCount .short h =
      (Finset.univ.filter (λ θ : Threshold 10 => negativeMeaning h θ)).card := by
  native_decide

-- ============================================================================
-- § 4. Comparison Class Inference Model (mathlib-PMF pipeline)
-- ============================================================================

open scoped ENNReal

/-! The model is [lassiter-goodman-2017]'s threshold RSA with the threshold θ
marginalised analytically (into `thresholdCount`) and the comparison class `c`
promoted to the `Latent` variable the listener infers:

    L₀(x | u, c) ∝ P(x | c) · |{θ : ⟦u⟧(x, θ)}|         (`meaningE`, `L0k`)
    S₁(u | x, c) ∝ L₀(x | u, c)  (α = 1, no cost)       (`Sk`)
    L₁(x, c | u, k) ∝ S₁(u | x, c) · P(x | k) · P(c | k) (`listenerK`)

`Sk` is a *total* speaker (a `dite` wrapper over `PMF.normalize`): at heights
with zero prior weight for a kind (`basketball` at h ∈ {0,1}, `jockey` at
h ∈ {9,10}) every utterance has literal mass `0`, so the softmax normaliser
vanishes and no `ViableSpeaker` instance exists; the junk uniform branch there
is harmless because those heights carry joint prior weight `0` in `L1`. -/

/-- Graded literal meaning `P(h | c) · |{θ : ⟦u⟧(h, θ)}|`, the `ℕ` product
`l0HeightWeight · thresholdCount` cast to `ℝ≥0∞`. -/
def meaningE (k : Kind) (c : ComparisonClass) (u : Utterance) (h : Height) : ℝ≥0∞ :=
  ((l0HeightWeight c k h * thresholdCount u h : ℕ) : ℝ≥0∞)

private theorem meaning_tsum_ne_zero (k : Kind) (c : ComparisonClass) (u : Utterance)
    {h₀ : Height} (h : l0HeightWeight c k h₀ * thresholdCount u h₀ ≠ 0) :
    (∑' h, meaningE k c u h) ≠ 0 :=
  ENNReal.summable.tsum_ne_zero_iff.mpr ⟨h₀, by simpa [meaningE] using h⟩

private theorem meaning_tsum_ne_top (k : Kind) (c : ComparisonClass) (u : Utterance) :
    (∑' h, meaningE k c u h) ≠ ⊤ := by
  rw [tsum_fintype]; exact ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.natCast_ne_top _

/-- Height enumeration: a `tsum`/`Finset.sum` over the 11 heights expands into
its `deg 0 … deg 10` summands. -/
private theorem sumH (f : Height → ℝ≥0∞) :
    (∑ h : Height, f h) = f (deg 0) + f (deg 1) + f (deg 2) + f (deg 3) + f (deg 4)
      + f (deg 5) + f (deg 6) + f (deg 7) + f (deg 8) + f (deg 9) + f (deg 10) := by
  rw [show (Finset.univ : Finset Height)
    = {deg 0, deg 1, deg 2, deg 3, deg 4, deg 5, deg 6, deg 7, deg 8, deg 9, deg 10} from by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]; ring

/-- Utterance enumeration: a `tsum` over the three utterances. -/
private theorem sumU (f : Utterance → ℝ≥0∞) :
    (∑' u, f u) = f .tall + f .short + f .silent := by
  rw [tsum_fintype, show (Finset.univ : Finset Utterance) = {.tall, .short, .silent} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton, add_assoc]

/-- The literal-listener denominator `D_c(u) = Σ_h P(h|c)·|{θ:⟦u⟧}|` as an
`ℝ≥0∞` cast of its `ℕ` value. -/
private theorem meaning_tsum_eq {k : Kind} {c : ComparisonClass} {u : Utterance} {D : ℕ}
    (hD : (∑ h : Height, l0HeightWeight c k h * thresholdCount u h) = D) :
    (∑' h, meaningE k c u h) = (D : ℝ≥0∞) := by
  simp only [meaningE]; rw [tsum_fintype, ← Nat.cast_sum, hD]

/-- Per-kind literal listener `L₀(· | u, c) : PMF Height`, uniform-in-θ meaning
normalised over heights. -/
noncomputable def L0k (k : Kind) (c : ComparisonClass) (u : Utterance) : PMF Height :=
  RSA.L0OfMeaning (meaningE k c) u
    (meaning_tsum_ne_zero k c u (h₀ := deg 5) (by cases c <;> cases k <;> cases u <;> decide))
    (meaning_tsum_ne_top k c u)

/-- **L0 value**: `L₀(h | u, c) = P(h|c)·|{θ:⟦u⟧(h)}| / D_c(u)`, an exact
`ENNReal.ofReal` rational. -/
theorem L0_val (N D : ℕ) {k : Kind} {c : ComparisonClass} {u : Utterance} {h : Height} {q : ℝ}
    (hN : l0HeightWeight c k h * thresholdCount u h = N)
    (hD : (∑ h' : Height, l0HeightWeight c k h' * thresholdCount u h') = D)
    (hDpos : 0 < D) (hq : (N : ℝ) / D = q) :
    L0k k c u h = ENNReal.ofReal q := by
  rw [L0k, RSA.L0OfMeaning_apply, meaning_tsum_eq hD]
  have hm : meaningE k c u h = ((N : ℕ) : ℝ≥0∞) := by rw [meaningE, hN]
  rw [hm, ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_natCast D,
    ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hDpos),
    ← ENNReal.ofReal_mul (by positivity), ← div_eq_mul_inv, hq]

private theorem L0k_tsum_ne_top (k : Kind) (c : ComparisonClass) (h : Height) :
    (∑' u, L0k k c u h) ≠ ⊤ := PMF.tsum_apply_ne_top (fun u => L0k k c u) h

/-- **Total speaker** `S₁(· | h, c) : PMF Utterance`, the `α = 1` softmax of the
literal listener, guarded by a `dite` so it is defined even where the softmax
normaliser vanishes (see the section note). -/
noncomputable def Sk (k : Kind) (s : Height × ComparisonClass) : PMF Utterance :=
  if hne : (∑' u, L0k k s.2 u s.1) ≠ 0 then
    PMF.normalize (fun u => L0k k s.2 u s.1) hne (L0k_tsum_ne_top k s.2 s.1)
  else PMF.pure .silent

private theorem Sk_eq {k : Kind} {c : ComparisonClass} {h : Height}
    (hne : (∑' u, L0k k c u h) ≠ 0) :
    Sk k (h, c) = PMF.normalize (fun u => L0k k c u h) hne (L0k_tsum_ne_top k c h) := by
  rw [Sk]; exact dif_pos hne

/-- **Z value**: the speaker normaliser `Z(h, c) = Σ_u L₀(h | u, c)` as an
`ENNReal.ofReal` rational, assembled from the three `L0_val`s. -/
private theorem Z_val {k : Kind} {c : ComparisonClass} {h : Height} {pt ps po z : ℝ}
    (ht : L0k k c .tall h = ENNReal.ofReal pt) (hs : L0k k c .short h = ENNReal.ofReal ps)
    (ho : L0k k c .silent h = ENNReal.ofReal po)
    (hpt : 0 ≤ pt) (hps : 0 ≤ ps) (hpo : 0 ≤ po) (hz : pt + ps + po = z) :
    (∑' u, L0k k c u h) = ENNReal.ofReal z := by
  rw [sumU, ht, hs, ho, ← ENNReal.ofReal_add hpt hps,
    ← ENNReal.ofReal_add (add_nonneg hpt hps) hpo, hz]

/-- **Speaker value**: `S₁(u | h, c) = L₀(h | u, c) / Z(h, c)`, an exact
`ENNReal.ofReal` rational. -/
theorem Sk_val {k : Kind} {c : ComparisonClass} {u : Utterance} {h : Height} {p z q : ℝ}
    (hp : L0k k c u h = ENNReal.ofReal p) (hZ : (∑' u', L0k k c u' h) = ENNReal.ofReal z)
    (hppos : 0 ≤ p) (hz : 0 < z) (hq : p / z = q) :
    Sk k (h, c) u = ENNReal.ofReal q := by
  rw [Sk_eq (by rw [hZ]; exact (ENNReal.ofReal_pos.mpr hz).ne'), PMF.normalize_apply]
  show L0k k c u h * (∑' u', L0k k c u' h)⁻¹ = _
  rw [hp, hZ, ← ENNReal.ofReal_inv_of_pos hz, ← ENNReal.ofReal_mul hppos,
    ← div_eq_mul_inv, hq]

private theorem L0k_ne_zero {k : Kind} {c : ComparisonClass} {u : Utterance} {h : Height}
    (hmul : l0HeightWeight c k h * thresholdCount u h ≠ 0) : L0k k c u h ≠ 0 := by
  rw [L0k, ← PMF.mem_support_iff, RSA.L0OfMeaning, PMF.mem_support_normalize_iff]
  simpa only [meaningE, ne_eq, Nat.cast_eq_zero] using hmul

private theorem Sk_pos_of_L0 {k : Kind} {c : ComparisonClass} {u : Utterance} {h : Height}
    (hne : (∑' u', L0k k c u' h) ≠ 0) (hu : L0k k c u h ≠ 0) : Sk k (h, c) u ≠ 0 := by
  rw [Sk_eq hne, ← PMF.mem_support_iff, PMF.mem_support_normalize_iff]; exact hu

-- ============================================================================
-- § 4a. Listener joint prior and marginal
-- ============================================================================

/-- Unnormalised joint prior `P(x | k) · P(c | k)` — world prior is the kind's
height distribution, latent (comparison-class) prior is flat, so the weight is
`P(x | k)`, independent of `c`. -/
def jointW (k : Kind) (s : Height × ComparisonClass) : ℝ≥0∞ := (heightWeight k s.1 : ℝ≥0∞)

private theorem jointW_tsum_ne_zero (k : Kind) : (∑' s, jointW k s) ≠ 0 := by
  refine ENNReal.summable.tsum_ne_zero_iff.mpr ⟨(deg 5, .subordinate), ?_⟩
  have h : heightWeight k (deg 5) ≠ 0 := by cases k <;> decide
  simpa only [jointW, ne_eq, Nat.cast_eq_zero] using h

private theorem jointW_tsum_ne_top (k : Kind) : (∑' s, jointW k s) ≠ ⊤ := by
  rw [tsum_fintype]; exact ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.natCast_ne_top _

/-- The listener's joint prior over `Height × ComparisonClass`. -/
noncomputable def jointK (k : Kind) : PMF (Height × ComparisonClass) :=
  PMF.normalize (jointW k) (jointW_tsum_ne_zero k) (jointW_tsum_ne_top k)

private theorem jointK_ne_zero {k : Kind} {s : Height × ComparisonClass}
    (h : jointW k s ≠ 0) : jointK k s ≠ 0 := by
  rw [jointK, ← PMF.mem_support_iff, PMF.mem_support_normalize_iff]; exact h

/-- The listener marginal is non-zero for every kind and utterance: at
`(deg 5, subordinate)` the joint prior and the literal listener are both
positive (all height weights and threshold counts are non-zero at h = 5). -/
theorem margK (k : Kind) (u : Utterance) : PMF.marginal (Sk k) (jointK k) u ≠ 0 := by
  have hL0 : L0k k .subordinate u (deg 5) ≠ 0 := L0k_ne_zero (by cases k <;> cases u <;> decide)
  refine PMF.marginal_ne_zero (Sk k) (jointK k) u (a := (deg 5, .subordinate))
    (jointK_ne_zero ?_) (Sk_pos_of_L0 (ENNReal.summable.tsum_ne_zero_iff.mpr ⟨u, hL0⟩) hL0)
  have h : heightWeight k (deg 5) ≠ 0 := by cases k <;> decide
  simpa only [jointW, ne_eq, Nat.cast_eq_zero] using h

/-- The pragmatic listener `L₁(x, c | u, k) : PMF (Height × ComparisonClass)`. -/
noncomputable def listenerK (k : Kind) (u : Utterance) : PMF (Height × ComparisonClass) :=
  RSA.Canonical.L1 (Sk k) (jointK k) u (margK k u)

private theorem sum_scaledW (z : ℝ≥0∞) (g f : Height → ℝ≥0∞) :
    (∑ w : Height, g w * z * f w) = z * ∑ w : Height, g w * f w := by
  rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring

/-- **Listener latent preference** reduces to prior-weighted pooled speaker
sums (the joint normaliser cancels); the prior weight `P(x | k)` stays inside
the sum since it varies with the height `x`. -/
private theorem listener_snd_lt (k : Kind) (u : Utterance) (c₁ c₂ : ComparisonClass) :
    (listenerK k u).snd c₁ < (listenerK k u).snd c₂ ↔
      (∑ w : Height, (heightWeight k w : ℝ≥0∞) * Sk k (w, c₁) u) <
        ∑ w : Height, (heightWeight k w : ℝ≥0∞) * Sk k (w, c₂) u := by
  unfold listenerK
  rw [RSA.Canonical.L1_latent_prefers_iff]
  simp only [jointK, PMF.normalize_apply, jointW]
  rw [sum_scaledW, sum_scaledW]
  exact ENNReal.mul_lt_mul_iff_right
    (ENNReal.inv_ne_zero.mpr (jointW_tsum_ne_top k))
    (ENNReal.inv_ne_top.mpr (jointW_tsum_ne_zero k))

/-- One pooled-sum term `P(x|k)·S₁(u|x,c)` as an `ENNReal.ofReal` rational. -/
private theorem wterm (W : ℕ) {k : Kind} {c : ComparisonClass} {u : Utterance} {w : Height} {sk : ℝ}
    (hw : heightWeight k w = W) (hsk : Sk k (w, c) u = ENNReal.ofReal sk) :
    (heightWeight k w : ℝ≥0∞) * Sk k (w, c) u = ENNReal.ofReal ((W : ℝ) * sk) := by
  rw [hw, hsk, ← ENNReal.ofReal_natCast W, ← ENNReal.ofReal_mul (by positivity)]

/-- A pooled-sum term at a zero-prior height vanishes. -/
private theorem wterm_zero {k : Kind} {c : ComparisonClass} {u : Utterance} {w : Height}
    (hw : heightWeight k w = 0) :
    (heightWeight k w : ℝ≥0∞) * Sk k (w, c) u = ENNReal.ofReal 0 := by
  rw [hw, Nat.cast_zero, zero_mul, ENNReal.ofReal_zero]

/-- **Endorsement reduction (`<`)**: at a fixed `(h, c)` the speaker normaliser
cancels, so `S₁` prefers `u₂` iff `L₀` does. -/
private theorem Sk_lt_iff {k : Kind} {c : ComparisonClass} {h : Height} (u₁ u₂ : Utterance)
    (hne : (∑' u, L0k k c u h) ≠ 0) :
    Sk k (h, c) u₁ < Sk k (h, c) u₂ ↔ L0k k c u₁ h < L0k k c u₂ h := by
  rw [Sk_eq hne, PMF.normalize_lt_iff_lt]

/-- The `≤` companion of `Sk_lt_iff`. -/
private theorem Sk_le_iff {k : Kind} {c : ComparisonClass} {h : Height} (u₁ u₂ : Utterance)
    (hne : (∑' u, L0k k c u h) ≠ 0) :
    Sk k (h, c) u₁ ≤ Sk k (h, c) u₂ ↔ L0k k c u₁ h ≤ L0k k c u₂ h := by
  rw [Sk_eq hne, PMF.normalize_le_iff_le]

/-- The speaker normaliser is non-zero, read off a positive `Z_val`. -/
private theorem Z_ne {k : Kind} {c : ComparisonClass} {h : Height} {z : ℝ}
    (hZ : (∑' u, L0k k c u h) = ENNReal.ofReal z) (hz : 0 < z) :
    (∑' u, L0k k c u h) ≠ 0 := by rw [hZ]; exact (ENNReal.ofReal_pos.mpr hz).ne'

-- ============================================================================
-- § 4b. Certified numeric values (literal listener, normaliser, speaker)
-- ============================================================================

/-! The per-`(kind, class, height)` literal-listener values `L₀`, speaker
normalisers `Z`, and speaker masses `S₁` below are exact `ENNReal.ofReal`
rationals, verified by `decide` (integer denominators) and `norm_num`
(rational arithmetic). They feed the endorsement comparisons (§ 6) and the
pooled listener sums (§ 8). -/

/-! ### Bball literal listener, normaliser, and speaker values -/

private theorem L0_bb_sub_tall_h2 :
    L0k .basketballPlayer .subordinate .tall (deg 2) = ENNReal.ofReal (1/284) :=
  L0_val 2 568 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_short_h2 :
    L0k .basketballPlayer .subordinate .short (deg 2) = ENNReal.ofReal (7/184) :=
  L0_val 7 184 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_silent_h2 :
    L0k .basketballPlayer .subordinate .silent (deg 2) = ENNReal.ofReal (1/83) :=
  L0_val 10 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sub_h2 :
    (∑' u, L0k .basketballPlayer .subordinate u (deg 2)) = ENNReal.ofReal (58133/1084312) :=
  Z_val L0_bb_sub_tall_h2 L0_bb_sub_short_h2 L0_bb_sub_silent_h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_tall_h2 :
    Sk .basketballPlayer (deg 2, .subordinate) .tall = ENNReal.ofReal (3818/58133) :=
  Sk_val L0_bb_sub_tall_h2 Z_bb_sub_h2 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_short_h2 :
    Sk .basketballPlayer (deg 2, .subordinate) .short = ENNReal.ofReal (41251/58133) :=
  Sk_val L0_bb_sub_short_h2 Z_bb_sub_h2 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sub_tall_h3 :
    L0k .basketballPlayer .subordinate .tall (deg 3) = ENNReal.ofReal (3/284) :=
  L0_val 6 568 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_short_h3 :
    L0k .basketballPlayer .subordinate .short (deg 3) = ENNReal.ofReal (3/46) :=
  L0_val 12 184 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_silent_h3 :
    L0k .basketballPlayer .subordinate .silent (deg 3) = ENNReal.ofReal (2/83) :=
  L0_val 20 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sub_h3 :
    (∑' u, L0k .basketballPlayer .subordinate u (deg 3)) = ENNReal.ofReal (54149/542156) :=
  Z_val L0_bb_sub_tall_h3 L0_bb_sub_short_h3 L0_bb_sub_silent_h3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_tall_h3 :
    Sk .basketballPlayer (deg 3, .subordinate) .tall = ENNReal.ofReal (5727/54149) :=
  Sk_val L0_bb_sub_tall_h3 Z_bb_sub_h3 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_short_h3 :
    Sk .basketballPlayer (deg 3, .subordinate) .short = ENNReal.ofReal (35358/54149) :=
  Sk_val L0_bb_sub_short_h3 Z_bb_sub_h3 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sub_tall_h4 :
    L0k .basketballPlayer .subordinate .tall (deg 4) = ENNReal.ofReal (5/142) :=
  L0_val 20 568 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_short_h4 :
    L0k .basketballPlayer .subordinate .short (deg 4) = ENNReal.ofReal (25/184) :=
  L0_val 25 184 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_silent_h4 :
    L0k .basketballPlayer .subordinate .silent (deg 4) = ENNReal.ofReal (5/83) :=
  L0_val 50 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sub_h4 :
    (∑' u, L0k .basketballPlayer .subordinate u (deg 4)) = ENNReal.ofReal (250825/1084312) :=
  Z_val L0_bb_sub_tall_h4 L0_bb_sub_short_h4 L0_bb_sub_silent_h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_tall_h4 :
    Sk .basketballPlayer (deg 4, .subordinate) .tall = ENNReal.ofReal (7636/50165) :=
  Sk_val L0_bb_sub_tall_h4 Z_bb_sub_h4 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_short_h4 :
    Sk .basketballPlayer (deg 4, .subordinate) .short = ENNReal.ofReal (5893/10033) :=
  Sk_val L0_bb_sub_short_h4 Z_bb_sub_h4 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sub_tall_h5 :
    L0k .basketballPlayer .subordinate .tall (deg 5) = ENNReal.ofReal (25/284) :=
  L0_val 50 568 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_short_h5 :
    L0k .basketballPlayer .subordinate .short (deg 5) = ENNReal.ofReal (5/23) :=
  L0_val 40 184 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_silent_h5 :
    L0k .basketballPlayer .subordinate .silent (deg 5) = ENNReal.ofReal (10/83) :=
  L0_val 100 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sub_h5 :
    (∑' u, L0k .basketballPlayer .subordinate u (deg 5)) = ENNReal.ofReal (230905/542156) :=
  Z_val L0_bb_sub_tall_h5 L0_bb_sub_short_h5 L0_bb_sub_silent_h5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_tall_h5 :
    Sk .basketballPlayer (deg 5, .subordinate) .tall = ENNReal.ofReal (9545/46181) :=
  Sk_val L0_bb_sub_tall_h5 Z_bb_sub_h5 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_short_h5 :
    Sk .basketballPlayer (deg 5, .subordinate) .short = ENNReal.ofReal (23572/46181) :=
  Sk_val L0_bb_sub_short_h5 Z_bb_sub_h5 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sub_tall_h6 :
    L0k .basketballPlayer .subordinate .tall (deg 6) = ENNReal.ofReal (45/284) :=
  L0_val 90 568 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_short_h6 :
    L0k .basketballPlayer .subordinate .short (deg 6) = ENNReal.ofReal (45/184) :=
  L0_val 45 184 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_silent_h6 :
    L0k .basketballPlayer .subordinate .silent (deg 6) = ENNReal.ofReal (15/83) :=
  L0_val 150 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sub_h6 :
    (∑' u, L0k .basketballPlayer .subordinate u (deg 6)) = ENNReal.ofReal (632955/1084312) :=
  Z_val L0_bb_sub_tall_h6 L0_bb_sub_short_h6 L0_bb_sub_silent_h6
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_tall_h6 :
    Sk .basketballPlayer (deg 6, .subordinate) .tall = ENNReal.ofReal (11454/42197) :=
  Sk_val L0_bb_sub_tall_h6 Z_bb_sub_h6 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_short_h6 :
    Sk .basketballPlayer (deg 6, .subordinate) .short = ENNReal.ofReal (17679/42197) :=
  Sk_val L0_bb_sub_short_h6 Z_bb_sub_h6 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sub_tall_h7 :
    L0k .basketballPlayer .subordinate .tall (deg 7) = ENNReal.ofReal (35/142) :=
  L0_val 140 568 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_short_h7 :
    L0k .basketballPlayer .subordinate .short (deg 7) = ENNReal.ofReal (5/23) :=
  L0_val 40 184 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_silent_h7 :
    L0k .basketballPlayer .subordinate .silent (deg 7) = ENNReal.ofReal (20/83) :=
  L0_val 200 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sub_h7 :
    (∑' u, L0k .basketballPlayer .subordinate u (deg 7)) = ENNReal.ofReal (191065/271078) :=
  Z_val L0_bb_sub_tall_h7 L0_bb_sub_short_h7 L0_bb_sub_silent_h7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_tall_h7 :
    Sk .basketballPlayer (deg 7, .subordinate) .tall = ENNReal.ofReal (1909/5459) :=
  Sk_val L0_bb_sub_tall_h7 Z_bb_sub_h7 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_short_h7 :
    Sk .basketballPlayer (deg 7, .subordinate) .short = ENNReal.ofReal (11786/38213) :=
  Sk_val L0_bb_sub_short_h7 Z_bb_sub_h7 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sub_tall_h8 :
    L0k .basketballPlayer .subordinate .tall (deg 8) = ENNReal.ofReal (15/71) :=
  L0_val 120 568 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_short_h8 :
    L0k .basketballPlayer .subordinate .short (deg 8) = ENNReal.ofReal (15/184) :=
  L0_val 15 184 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_silent_h8 :
    L0k .basketballPlayer .subordinate .silent (deg 8) = ENNReal.ofReal (15/83) :=
  L0_val 150 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sub_h8 :
    (∑' u, L0k .basketballPlayer .subordinate u (deg 8)) = ENNReal.ofReal (513435/1084312) :=
  Z_val L0_bb_sub_tall_h8 L0_bb_sub_short_h8 L0_bb_sub_silent_h8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_tall_h8 :
    Sk .basketballPlayer (deg 8, .subordinate) .tall = ENNReal.ofReal (15272/34229) :=
  Sk_val L0_bb_sub_tall_h8 Z_bb_sub_h8 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_short_h8 :
    Sk .basketballPlayer (deg 8, .subordinate) .short = ENNReal.ofReal (5893/34229) :=
  Sk_val L0_bb_sub_short_h8 Z_bb_sub_h8 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sub_tall_h9 :
    L0k .basketballPlayer .subordinate .tall (deg 9) = ENNReal.ofReal (45/284) :=
  L0_val 90 568 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_short_h9 :
    L0k .basketballPlayer .subordinate .short (deg 9) = ENNReal.ofReal 0 :=
  L0_val 0 184 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_silent_h9 :
    L0k .basketballPlayer .subordinate .silent (deg 9) = ENNReal.ofReal (10/83) :=
  L0_val 100 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sub_h9 :
    (∑' u, L0k .basketballPlayer .subordinate u (deg 9)) = ENNReal.ofReal (6575/23572) :=
  Z_val L0_bb_sub_tall_h9 L0_bb_sub_short_h9 L0_bb_sub_silent_h9
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_tall_h9 :
    Sk .basketballPlayer (deg 9, .subordinate) .tall = ENNReal.ofReal (747/1315) :=
  Sk_val L0_bb_sub_tall_h9 Z_bb_sub_h9 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_short_h9 :
    Sk .basketballPlayer (deg 9, .subordinate) .short = ENNReal.ofReal 0 :=
  Sk_val L0_bb_sub_short_h9 Z_bb_sub_h9 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sub_tall_h10 :
    L0k .basketballPlayer .subordinate .tall (deg 10) = ENNReal.ofReal (25/284) :=
  L0_val 50 568 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_short_h10 :
    L0k .basketballPlayer .subordinate .short (deg 10) = ENNReal.ofReal 0 :=
  L0_val 0 184 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sub_silent_h10 :
    L0k .basketballPlayer .subordinate .silent (deg 10) = ENNReal.ofReal (5/83) :=
  L0_val 50 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sub_h10 :
    (∑' u, L0k .basketballPlayer .subordinate u (deg 10)) = ENNReal.ofReal (3495/23572) :=
  Z_val L0_bb_sub_tall_h10 L0_bb_sub_short_h10 L0_bb_sub_silent_h10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_tall_h10 :
    Sk .basketballPlayer (deg 10, .subordinate) .tall = ENNReal.ofReal (415/699) :=
  Sk_val L0_bb_sub_tall_h10 Z_bb_sub_h10 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sub_short_h10 :
    Sk .basketballPlayer (deg 10, .subordinate) .short = ENNReal.ofReal 0 :=
  Sk_val L0_bb_sub_short_h10 Z_bb_sub_h10 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sup_tall_h2 :
    L0k .basketballPlayer .superordinate .tall (deg 2) = ENNReal.ofReal (1/43) :=
  L0_val 10 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_short_h2 :
    L0k .basketballPlayer .superordinate .short (deg 2) = ENNReal.ofReal (7/69) :=
  L0_val 35 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_silent_h2 :
    L0k .basketballPlayer .superordinate .silent (deg 2) = ENNReal.ofReal (5/86) :=
  L0_val 50 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sup_h2 :
    (∑' u, L0k .basketballPlayer .superordinate u (deg 2)) = ENNReal.ofReal (1085/5934) :=
  Z_val L0_bb_sup_tall_h2 L0_bb_sup_short_h2 L0_bb_sup_silent_h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_tall_h2 :
    Sk .basketballPlayer (deg 2, .superordinate) .tall = ENNReal.ofReal (138/1085) :=
  Sk_val L0_bb_sup_tall_h2 Z_bb_sup_h2 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_short_h2 :
    Sk .basketballPlayer (deg 2, .superordinate) .short = ENNReal.ofReal (86/155) :=
  Sk_val L0_bb_sup_short_h2 Z_bb_sup_h2 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sup_tall_h3 :
    L0k .basketballPlayer .superordinate .tall (deg 3) = ENNReal.ofReal (3/43) :=
  L0_val 30 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_short_h3 :
    L0k .basketballPlayer .superordinate .short (deg 3) = ENNReal.ofReal (4/23) :=
  L0_val 60 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_silent_h3 :
    L0k .basketballPlayer .superordinate .silent (deg 3) = ENNReal.ofReal (5/43) :=
  L0_val 100 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sup_h3 :
    (∑' u, L0k .basketballPlayer .superordinate u (deg 3)) = ENNReal.ofReal (356/989) :=
  Z_val L0_bb_sup_tall_h3 L0_bb_sup_short_h3 L0_bb_sup_silent_h3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_tall_h3 :
    Sk .basketballPlayer (deg 3, .superordinate) .tall = ENNReal.ofReal (69/356) :=
  Sk_val L0_bb_sup_tall_h3 Z_bb_sup_h3 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_short_h3 :
    Sk .basketballPlayer (deg 3, .superordinate) .short = ENNReal.ofReal (43/89) :=
  Sk_val L0_bb_sup_short_h3 Z_bb_sup_h3 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sup_tall_h4 :
    L0k .basketballPlayer .superordinate .tall (deg 4) = ENNReal.ofReal (6/43) :=
  L0_val 60 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_short_h4 :
    L0k .basketballPlayer .superordinate .short (deg 4) = ENNReal.ofReal (5/23) :=
  L0_val 75 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_silent_h4 :
    L0k .basketballPlayer .superordinate .silent (deg 4) = ENNReal.ofReal (15/86) :=
  L0_val 150 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sup_h4 :
    (∑' u, L0k .basketballPlayer .superordinate u (deg 4)) = ENNReal.ofReal (1051/1978) :=
  Z_val L0_bb_sup_tall_h4 L0_bb_sup_short_h4 L0_bb_sup_silent_h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_tall_h4 :
    Sk .basketballPlayer (deg 4, .superordinate) .tall = ENNReal.ofReal (276/1051) :=
  Sk_val L0_bb_sup_tall_h4 Z_bb_sup_h4 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_short_h4 :
    Sk .basketballPlayer (deg 4, .superordinate) .short = ENNReal.ofReal (430/1051) :=
  Sk_val L0_bb_sup_short_h4 Z_bb_sup_h4 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sup_tall_h5 :
    L0k .basketballPlayer .superordinate .tall (deg 5) = ENNReal.ofReal (10/43) :=
  L0_val 100 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_short_h5 :
    L0k .basketballPlayer .superordinate .short (deg 5) = ENNReal.ofReal (16/69) :=
  L0_val 80 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_silent_h5 :
    L0k .basketballPlayer .superordinate .silent (deg 5) = ENNReal.ofReal (10/43) :=
  L0_val 200 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sup_h5 :
    (∑' u, L0k .basketballPlayer .superordinate u (deg 5)) = ENNReal.ofReal (2068/2967) :=
  Z_val L0_bb_sup_tall_h5 L0_bb_sup_short_h5 L0_bb_sup_silent_h5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_tall_h5 :
    Sk .basketballPlayer (deg 5, .superordinate) .tall = ENNReal.ofReal (345/1034) :=
  Sk_val L0_bb_sup_tall_h5 Z_bb_sup_h5 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_short_h5 :
    Sk .basketballPlayer (deg 5, .superordinate) .short = ENNReal.ofReal (172/517) :=
  Sk_val L0_bb_sup_short_h5 Z_bb_sup_h5 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sup_tall_h6 :
    L0k .basketballPlayer .superordinate .tall (deg 6) = ENNReal.ofReal (9/43) :=
  L0_val 90 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_short_h6 :
    L0k .basketballPlayer .superordinate .short (deg 6) = ENNReal.ofReal (3/23) :=
  L0_val 45 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_silent_h6 :
    L0k .basketballPlayer .superordinate .silent (deg 6) = ENNReal.ofReal (15/86) :=
  L0_val 150 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sup_h6 :
    (∑' u, L0k .basketballPlayer .superordinate u (deg 6)) = ENNReal.ofReal (1017/1978) :=
  Z_val L0_bb_sup_tall_h6 L0_bb_sup_short_h6 L0_bb_sup_silent_h6
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_tall_h6 :
    Sk .basketballPlayer (deg 6, .superordinate) .tall = ENNReal.ofReal (46/113) :=
  Sk_val L0_bb_sup_tall_h6 Z_bb_sup_h6 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_short_h6 :
    Sk .basketballPlayer (deg 6, .superordinate) .short = ENNReal.ofReal (86/339) :=
  Sk_val L0_bb_sup_short_h6 Z_bb_sup_h6 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sup_tall_h7 :
    L0k .basketballPlayer .superordinate .tall (deg 7) = ENNReal.ofReal (7/43) :=
  L0_val 70 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_short_h7 :
    L0k .basketballPlayer .superordinate .short (deg 7) = ENNReal.ofReal (4/69) :=
  L0_val 20 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_silent_h7 :
    L0k .basketballPlayer .superordinate .silent (deg 7) = ENNReal.ofReal (5/43) :=
  L0_val 100 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sup_h7 :
    (∑' u, L0k .basketballPlayer .superordinate u (deg 7)) = ENNReal.ofReal (1000/2967) :=
  Z_val L0_bb_sup_tall_h7 L0_bb_sup_short_h7 L0_bb_sup_silent_h7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_tall_h7 :
    Sk .basketballPlayer (deg 7, .superordinate) .tall = ENNReal.ofReal (483/1000) :=
  Sk_val L0_bb_sup_tall_h7 Z_bb_sup_h7 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_short_h7 :
    Sk .basketballPlayer (deg 7, .superordinate) .short = ENNReal.ofReal (43/250) :=
  Sk_val L0_bb_sup_short_h7 Z_bb_sup_h7 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sup_tall_h8 :
    L0k .basketballPlayer .superordinate .tall (deg 8) = ENNReal.ofReal (4/43) :=
  L0_val 40 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_short_h8 :
    L0k .basketballPlayer .superordinate .short (deg 8) = ENNReal.ofReal (1/69) :=
  L0_val 5 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_silent_h8 :
    L0k .basketballPlayer .superordinate .silent (deg 8) = ENNReal.ofReal (5/86) :=
  L0_val 50 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sup_h8 :
    (∑' u, L0k .basketballPlayer .superordinate u (deg 8)) = ENNReal.ofReal (983/5934) :=
  Z_val L0_bb_sup_tall_h8 L0_bb_sup_short_h8 L0_bb_sup_silent_h8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_tall_h8 :
    Sk .basketballPlayer (deg 8, .superordinate) .tall = ENNReal.ofReal (552/983) :=
  Sk_val L0_bb_sup_tall_h8 Z_bb_sup_h8 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_short_h8 :
    Sk .basketballPlayer (deg 8, .superordinate) .short = ENNReal.ofReal (86/983) :=
  Sk_val L0_bb_sup_short_h8 Z_bb_sup_h8 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sup_tall_h9 :
    L0k .basketballPlayer .superordinate .tall (deg 9) = ENNReal.ofReal (9/215) :=
  L0_val 18 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_short_h9 :
    L0k .basketballPlayer .superordinate .short (deg 9) = ENNReal.ofReal 0 :=
  L0_val 0 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_silent_h9 :
    L0k .basketballPlayer .superordinate .silent (deg 9) = ENNReal.ofReal (1/43) :=
  L0_val 20 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sup_h9 :
    (∑' u, L0k .basketballPlayer .superordinate u (deg 9)) = ENNReal.ofReal (14/215) :=
  Z_val L0_bb_sup_tall_h9 L0_bb_sup_short_h9 L0_bb_sup_silent_h9
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_tall_h9 :
    Sk .basketballPlayer (deg 9, .superordinate) .tall = ENNReal.ofReal (9/14) :=
  Sk_val L0_bb_sup_tall_h9 Z_bb_sup_h9 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_short_h9 :
    Sk .basketballPlayer (deg 9, .superordinate) .short = ENNReal.ofReal 0 :=
  Sk_val L0_bb_sup_short_h9 Z_bb_sup_h9 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_bb_sup_tall_h10 :
    L0k .basketballPlayer .superordinate .tall (deg 10) = ENNReal.ofReal (1/43) :=
  L0_val 10 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_short_h10 :
    L0k .basketballPlayer .superordinate .short (deg 10) = ENNReal.ofReal 0 :=
  L0_val 0 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_bb_sup_silent_h10 :
    L0k .basketballPlayer .superordinate .silent (deg 10) = ENNReal.ofReal (1/86) :=
  L0_val 10 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_bb_sup_h10 :
    (∑' u, L0k .basketballPlayer .superordinate u (deg 10)) = ENNReal.ofReal (3/86) :=
  Z_val L0_bb_sup_tall_h10 L0_bb_sup_short_h10 L0_bb_sup_silent_h10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_tall_h10 :
    Sk .basketballPlayer (deg 10, .superordinate) .tall = ENNReal.ofReal (2/3) :=
  Sk_val L0_bb_sup_tall_h10 Z_bb_sup_h10 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_bb_sup_short_h10 :
    Sk .basketballPlayer (deg 10, .superordinate) .short = ENNReal.ofReal 0 :=
  Sk_val L0_bb_sup_short_h10 Z_bb_sup_h10 (by norm_num) (by norm_num) (by norm_num)

/-! ### Jockey literal listener, normaliser, and speaker values -/

private theorem L0_jk_sub_tall_h0 :
    L0k .jockey .subordinate .tall (deg 0) = ENNReal.ofReal 0 :=
  L0_val 0 262 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_short_h0 :
    L0k .jockey .subordinate .short (deg 0) = ENNReal.ofReal (9/97) :=
  L0_val 45 485 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_silent_h0 :
    L0k .jockey .subordinate .silent (deg 0) = ENNReal.ofReal (5/83) :=
  L0_val 50 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sub_h0 :
    (∑' u, L0k .jockey .subordinate u (deg 0)) = ENNReal.ofReal (1232/8051) :=
  Z_val L0_jk_sub_tall_h0 L0_jk_sub_short_h0 L0_jk_sub_silent_h0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_tall_h0 :
    Sk .jockey (deg 0, .subordinate) .tall = ENNReal.ofReal 0 :=
  Sk_val L0_jk_sub_tall_h0 Z_jk_sub_h0 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_short_h0 :
    Sk .jockey (deg 0, .subordinate) .short = ENNReal.ofReal (747/1232) :=
  Sk_val L0_jk_sub_short_h0 Z_jk_sub_h0 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sub_tall_h1 :
    L0k .jockey .subordinate .tall (deg 1) = ENNReal.ofReal (5/131) :=
  L0_val 10 262 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_short_h1 :
    L0k .jockey .subordinate .short (deg 1) = ENNReal.ofReal (16/97) :=
  L0_val 80 485 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_silent_h1 :
    L0k .jockey .subordinate .silent (deg 1) = ENNReal.ofReal (10/83) :=
  L0_val 100 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sub_h1 :
    (∑' u, L0k .jockey .subordinate u (deg 1)) = ENNReal.ofReal (341293/1054681) :=
  Z_val L0_jk_sub_tall_h1 L0_jk_sub_short_h1 L0_jk_sub_silent_h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_tall_h1 :
    Sk .jockey (deg 1, .subordinate) .tall = ENNReal.ofReal (40255/341293) :=
  Sk_val L0_jk_sub_tall_h1 Z_jk_sub_h1 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_short_h1 :
    Sk .jockey (deg 1, .subordinate) .short = ENNReal.ofReal (173968/341293) :=
  Sk_val L0_jk_sub_short_h1 Z_jk_sub_h1 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sub_tall_h2 :
    L0k .jockey .subordinate .tall (deg 2) = ENNReal.ofReal (15/131) :=
  L0_val 30 262 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_short_h2 :
    L0k .jockey .subordinate .short (deg 2) = ENNReal.ofReal (21/97) :=
  L0_val 105 485 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_silent_h2 :
    L0k .jockey .subordinate .silent (deg 2) = ENNReal.ofReal (15/83) :=
  L0_val 150 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sub_h2 :
    (∑' u, L0k .jockey .subordinate u (deg 2)) = ENNReal.ofReal (539703/1054681) :=
  Z_val L0_jk_sub_tall_h2 L0_jk_sub_short_h2 L0_jk_sub_silent_h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_tall_h2 :
    Sk .jockey (deg 2, .subordinate) .tall = ENNReal.ofReal (40255/179901) :=
  Sk_val L0_jk_sub_tall_h2 Z_jk_sub_h2 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_short_h2 :
    Sk .jockey (deg 2, .subordinate) .short = ENNReal.ofReal (76111/179901) :=
  Sk_val L0_jk_sub_short_h2 Z_jk_sub_h2 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sub_tall_h3 :
    L0k .jockey .subordinate .tall (deg 3) = ENNReal.ofReal (30/131) :=
  L0_val 60 262 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_short_h3 :
    L0k .jockey .subordinate .short (deg 3) = ENNReal.ofReal (24/97) :=
  L0_val 120 485 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_silent_h3 :
    L0k .jockey .subordinate .silent (deg 3) = ENNReal.ofReal (20/83) :=
  L0_val 200 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sub_h3 :
    (∑' u, L0k .jockey .subordinate u (deg 3)) = ENNReal.ofReal (756622/1054681) :=
  Z_val L0_jk_sub_tall_h3 L0_jk_sub_short_h3 L0_jk_sub_silent_h3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_tall_h3 :
    Sk .jockey (deg 3, .subordinate) .tall = ENNReal.ofReal (120765/378311) :=
  Sk_val L0_jk_sub_tall_h3 Z_jk_sub_h3 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_short_h3 :
    Sk .jockey (deg 3, .subordinate) .short = ENNReal.ofReal (130476/378311) :=
  Sk_val L0_jk_sub_short_h3 Z_jk_sub_h3 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sub_tall_h4 :
    L0k .jockey .subordinate .tall (deg 4) = ENNReal.ofReal (30/131) :=
  L0_val 60 262 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_short_h4 :
    L0k .jockey .subordinate .short (deg 4) = ENNReal.ofReal (15/97) :=
  L0_val 75 485 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_silent_h4 :
    L0k .jockey .subordinate .silent (deg 4) = ENNReal.ofReal (15/83) :=
  L0_val 150 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sub_h4 :
    (∑' u, L0k .jockey .subordinate u (deg 4)) = ENNReal.ofReal (595230/1054681) :=
  Z_val L0_jk_sub_tall_h4 L0_jk_sub_short_h4 L0_jk_sub_silent_h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_tall_h4 :
    Sk .jockey (deg 4, .subordinate) .tall = ENNReal.ofReal (8051/19841) :=
  Sk_val L0_jk_sub_tall_h4 Z_jk_sub_h4 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_short_h4 :
    Sk .jockey (deg 4, .subordinate) .short = ENNReal.ofReal (10873/39682) :=
  Sk_val L0_jk_sub_short_h4 Z_jk_sub_h4 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sub_tall_h5 :
    L0k .jockey .subordinate .tall (deg 5) = ENNReal.ofReal (25/131) :=
  L0_val 50 262 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_short_h5 :
    L0k .jockey .subordinate .short (deg 5) = ENNReal.ofReal (8/97) :=
  L0_val 40 485 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_silent_h5 :
    L0k .jockey .subordinate .silent (deg 5) = ENNReal.ofReal (10/83) :=
  L0_val 100 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sub_h5 :
    (∑' u, L0k .jockey .subordinate u (deg 5)) = ENNReal.ofReal (415329/1054681) :=
  Z_val L0_jk_sub_tall_h5 L0_jk_sub_short_h5 L0_jk_sub_silent_h5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_tall_h5 :
    Sk .jockey (deg 5, .subordinate) .tall = ENNReal.ofReal (201275/415329) :=
  Sk_val L0_jk_sub_tall_h5 Z_jk_sub_h5 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_short_h5 :
    Sk .jockey (deg 5, .subordinate) .short = ENNReal.ofReal (86984/415329) :=
  Sk_val L0_jk_sub_short_h5 Z_jk_sub_h5 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sub_tall_h6 :
    L0k .jockey .subordinate .tall (deg 6) = ENNReal.ofReal (15/131) :=
  L0_val 30 262 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_short_h6 :
    L0k .jockey .subordinate .short (deg 6) = ENNReal.ofReal (3/97) :=
  L0_val 15 485 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_silent_h6 :
    L0k .jockey .subordinate .silent (deg 6) = ENNReal.ofReal (5/83) :=
  L0_val 50 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sub_h6 :
    (∑' u, L0k .jockey .subordinate u (deg 6)) = ENNReal.ofReal (216919/1054681) :=
  Z_val L0_jk_sub_tall_h6 L0_jk_sub_short_h6 L0_jk_sub_silent_h6
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_tall_h6 :
    Sk .jockey (deg 6, .subordinate) .tall = ENNReal.ofReal (120765/216919) :=
  Sk_val L0_jk_sub_tall_h6 Z_jk_sub_h6 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_short_h6 :
    Sk .jockey (deg 6, .subordinate) .short = ENNReal.ofReal (32619/216919) :=
  Sk_val L0_jk_sub_short_h6 Z_jk_sub_h6 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sub_tall_h7 :
    L0k .jockey .subordinate .tall (deg 7) = ENNReal.ofReal (7/131) :=
  L0_val 14 262 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_short_h7 :
    L0k .jockey .subordinate .short (deg 7) = ENNReal.ofReal (4/485) :=
  L0_val 4 485 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_silent_h7 :
    L0k .jockey .subordinate .silent (deg 7) = ENNReal.ofReal (2/83) :=
  L0_val 20 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sub_h7 :
    (∑' u, L0k .jockey .subordinate u (deg 7)) = ENNReal.ofReal (452347/5273405) :=
  Z_val L0_jk_sub_tall_h7 L0_jk_sub_short_h7 L0_jk_sub_silent_h7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_tall_h7 :
    Sk .jockey (deg 7, .subordinate) .tall = ENNReal.ofReal (40255/64621) :=
  Sk_val L0_jk_sub_tall_h7 Z_jk_sub_h7 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_short_h7 :
    Sk .jockey (deg 7, .subordinate) .short = ENNReal.ofReal (43492/452347) :=
  Sk_val L0_jk_sub_short_h7 Z_jk_sub_h7 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sub_tall_h8 :
    L0k .jockey .subordinate .tall (deg 8) = ENNReal.ofReal (4/131) :=
  L0_val 8 262 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_short_h8 :
    L0k .jockey .subordinate .short (deg 8) = ENNReal.ofReal (1/485) :=
  L0_val 1 485 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sub_silent_h8 :
    L0k .jockey .subordinate .silent (deg 8) = ENNReal.ofReal (1/83) :=
  L0_val 10 830 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sub_h8 :
    (∑' u, L0k .jockey .subordinate u (deg 8)) = ENNReal.ofReal (235428/5273405) :=
  Z_val L0_jk_sub_tall_h8 L0_jk_sub_short_h8 L0_jk_sub_silent_h8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_tall_h8 :
    Sk .jockey (deg 8, .subordinate) .tall = ENNReal.ofReal (40255/58857) :=
  Sk_val L0_jk_sub_tall_h8 Z_jk_sub_h8 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sub_short_h8 :
    Sk .jockey (deg 8, .subordinate) .short = ENNReal.ofReal (10873/235428) :=
  Sk_val L0_jk_sub_short_h8 Z_jk_sub_h8 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sup_tall_h0 :
    L0k .jockey .superordinate .tall (deg 0) = ENNReal.ofReal 0 :=
  L0_val 0 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_short_h0 :
    L0k .jockey .superordinate .short (deg 0) = ENNReal.ofReal (3/115) :=
  L0_val 9 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_silent_h0 :
    L0k .jockey .superordinate .silent (deg 0) = ENNReal.ofReal (1/86) :=
  L0_val 10 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sup_h0 :
    (∑' u, L0k .jockey .superordinate u (deg 0)) = ENNReal.ofReal (373/9890) :=
  Z_val L0_jk_sup_tall_h0 L0_jk_sup_short_h0 L0_jk_sup_silent_h0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_tall_h0 :
    Sk .jockey (deg 0, .superordinate) .tall = ENNReal.ofReal 0 :=
  Sk_val L0_jk_sup_tall_h0 Z_jk_sup_h0 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_short_h0 :
    Sk .jockey (deg 0, .superordinate) .short = ENNReal.ofReal (258/373) :=
  Sk_val L0_jk_sup_short_h0 Z_jk_sup_h0 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sup_tall_h1 :
    L0k .jockey .superordinate .tall (deg 1) = ENNReal.ofReal (1/215) :=
  L0_val 2 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_short_h1 :
    L0k .jockey .superordinate .short (deg 1) = ENNReal.ofReal (16/345) :=
  L0_val 16 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_silent_h1 :
    L0k .jockey .superordinate .silent (deg 1) = ENNReal.ofReal (1/43) :=
  L0_val 20 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sup_h1 :
    (∑' u, L0k .jockey .superordinate u (deg 1)) = ENNReal.ofReal (1102/14835) :=
  Z_val L0_jk_sup_tall_h1 L0_jk_sup_short_h1 L0_jk_sup_silent_h1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_tall_h1 :
    Sk .jockey (deg 1, .superordinate) .tall = ENNReal.ofReal (69/1102) :=
  Sk_val L0_jk_sup_tall_h1 Z_jk_sup_h1 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_short_h1 :
    Sk .jockey (deg 1, .superordinate) .short = ENNReal.ofReal (344/551) :=
  Sk_val L0_jk_sup_short_h1 Z_jk_sup_h1 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sup_tall_h2 :
    L0k .jockey .superordinate .tall (deg 2) = ENNReal.ofReal (1/43) :=
  L0_val 10 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_short_h2 :
    L0k .jockey .superordinate .short (deg 2) = ENNReal.ofReal (7/69) :=
  L0_val 35 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_silent_h2 :
    L0k .jockey .superordinate .silent (deg 2) = ENNReal.ofReal (5/86) :=
  L0_val 50 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sup_h2 :
    (∑' u, L0k .jockey .superordinate u (deg 2)) = ENNReal.ofReal (1085/5934) :=
  Z_val L0_jk_sup_tall_h2 L0_jk_sup_short_h2 L0_jk_sup_silent_h2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_tall_h2 :
    Sk .jockey (deg 2, .superordinate) .tall = ENNReal.ofReal (138/1085) :=
  Sk_val L0_jk_sup_tall_h2 Z_jk_sup_h2 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_short_h2 :
    Sk .jockey (deg 2, .superordinate) .short = ENNReal.ofReal (86/155) :=
  Sk_val L0_jk_sup_short_h2 Z_jk_sup_h2 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sup_tall_h3 :
    L0k .jockey .superordinate .tall (deg 3) = ENNReal.ofReal (3/43) :=
  L0_val 30 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_short_h3 :
    L0k .jockey .superordinate .short (deg 3) = ENNReal.ofReal (4/23) :=
  L0_val 60 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_silent_h3 :
    L0k .jockey .superordinate .silent (deg 3) = ENNReal.ofReal (5/43) :=
  L0_val 100 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sup_h3 :
    (∑' u, L0k .jockey .superordinate u (deg 3)) = ENNReal.ofReal (356/989) :=
  Z_val L0_jk_sup_tall_h3 L0_jk_sup_short_h3 L0_jk_sup_silent_h3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_tall_h3 :
    Sk .jockey (deg 3, .superordinate) .tall = ENNReal.ofReal (69/356) :=
  Sk_val L0_jk_sup_tall_h3 Z_jk_sup_h3 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_short_h3 :
    Sk .jockey (deg 3, .superordinate) .short = ENNReal.ofReal (43/89) :=
  Sk_val L0_jk_sup_short_h3 Z_jk_sup_h3 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sup_tall_h4 :
    L0k .jockey .superordinate .tall (deg 4) = ENNReal.ofReal (6/43) :=
  L0_val 60 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_short_h4 :
    L0k .jockey .superordinate .short (deg 4) = ENNReal.ofReal (5/23) :=
  L0_val 75 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_silent_h4 :
    L0k .jockey .superordinate .silent (deg 4) = ENNReal.ofReal (15/86) :=
  L0_val 150 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sup_h4 :
    (∑' u, L0k .jockey .superordinate u (deg 4)) = ENNReal.ofReal (1051/1978) :=
  Z_val L0_jk_sup_tall_h4 L0_jk_sup_short_h4 L0_jk_sup_silent_h4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_tall_h4 :
    Sk .jockey (deg 4, .superordinate) .tall = ENNReal.ofReal (276/1051) :=
  Sk_val L0_jk_sup_tall_h4 Z_jk_sup_h4 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_short_h4 :
    Sk .jockey (deg 4, .superordinate) .short = ENNReal.ofReal (430/1051) :=
  Sk_val L0_jk_sup_short_h4 Z_jk_sup_h4 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sup_tall_h5 :
    L0k .jockey .superordinate .tall (deg 5) = ENNReal.ofReal (10/43) :=
  L0_val 100 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_short_h5 :
    L0k .jockey .superordinate .short (deg 5) = ENNReal.ofReal (16/69) :=
  L0_val 80 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_silent_h5 :
    L0k .jockey .superordinate .silent (deg 5) = ENNReal.ofReal (10/43) :=
  L0_val 200 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sup_h5 :
    (∑' u, L0k .jockey .superordinate u (deg 5)) = ENNReal.ofReal (2068/2967) :=
  Z_val L0_jk_sup_tall_h5 L0_jk_sup_short_h5 L0_jk_sup_silent_h5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_tall_h5 :
    Sk .jockey (deg 5, .superordinate) .tall = ENNReal.ofReal (345/1034) :=
  Sk_val L0_jk_sup_tall_h5 Z_jk_sup_h5 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_short_h5 :
    Sk .jockey (deg 5, .superordinate) .short = ENNReal.ofReal (172/517) :=
  Sk_val L0_jk_sup_short_h5 Z_jk_sup_h5 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sup_tall_h6 :
    L0k .jockey .superordinate .tall (deg 6) = ENNReal.ofReal (9/43) :=
  L0_val 90 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_short_h6 :
    L0k .jockey .superordinate .short (deg 6) = ENNReal.ofReal (3/23) :=
  L0_val 45 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_silent_h6 :
    L0k .jockey .superordinate .silent (deg 6) = ENNReal.ofReal (15/86) :=
  L0_val 150 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sup_h6 :
    (∑' u, L0k .jockey .superordinate u (deg 6)) = ENNReal.ofReal (1017/1978) :=
  Z_val L0_jk_sup_tall_h6 L0_jk_sup_short_h6 L0_jk_sup_silent_h6
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_tall_h6 :
    Sk .jockey (deg 6, .superordinate) .tall = ENNReal.ofReal (46/113) :=
  Sk_val L0_jk_sup_tall_h6 Z_jk_sup_h6 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_short_h6 :
    Sk .jockey (deg 6, .superordinate) .short = ENNReal.ofReal (86/339) :=
  Sk_val L0_jk_sup_short_h6 Z_jk_sup_h6 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sup_tall_h7 :
    L0k .jockey .superordinate .tall (deg 7) = ENNReal.ofReal (7/43) :=
  L0_val 70 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_short_h7 :
    L0k .jockey .superordinate .short (deg 7) = ENNReal.ofReal (4/69) :=
  L0_val 20 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_silent_h7 :
    L0k .jockey .superordinate .silent (deg 7) = ENNReal.ofReal (5/43) :=
  L0_val 100 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sup_h7 :
    (∑' u, L0k .jockey .superordinate u (deg 7)) = ENNReal.ofReal (1000/2967) :=
  Z_val L0_jk_sup_tall_h7 L0_jk_sup_short_h7 L0_jk_sup_silent_h7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_tall_h7 :
    Sk .jockey (deg 7, .superordinate) .tall = ENNReal.ofReal (483/1000) :=
  Sk_val L0_jk_sup_tall_h7 Z_jk_sup_h7 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_short_h7 :
    Sk .jockey (deg 7, .superordinate) .short = ENNReal.ofReal (43/250) :=
  Sk_val L0_jk_sup_short_h7 Z_jk_sup_h7 (by norm_num) (by norm_num) (by norm_num)

private theorem L0_jk_sup_tall_h8 :
    L0k .jockey .superordinate .tall (deg 8) = ENNReal.ofReal (4/43) :=
  L0_val 40 430 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_short_h8 :
    L0k .jockey .superordinate .short (deg 8) = ENNReal.ofReal (1/69) :=
  L0_val 5 345 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem L0_jk_sup_silent_h8 :
    L0k .jockey .superordinate .silent (deg 8) = ENNReal.ofReal (5/86) :=
  L0_val 50 860 (by decide) (by decide) (by norm_num) (by norm_num)
private theorem Z_jk_sup_h8 :
    (∑' u, L0k .jockey .superordinate u (deg 8)) = ENNReal.ofReal (983/5934) :=
  Z_val L0_jk_sup_tall_h8 L0_jk_sup_short_h8 L0_jk_sup_silent_h8
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_tall_h8 :
    Sk .jockey (deg 8, .superordinate) .tall = ENNReal.ofReal (552/983) :=
  Sk_val L0_jk_sup_tall_h8 Z_jk_sup_h8 (by norm_num) (by norm_num) (by norm_num)
private theorem Sk_jk_sup_short_h8 :
    Sk .jockey (deg 8, .superordinate) .short = ENNReal.ofReal (86/983) :=
  Sk_val L0_jk_sup_short_h8 Z_jk_sup_h8 (by norm_num) (by norm_num) (by norm_num)

-- ============================================================================
-- § 4c. Pooled speaker sums `Σ_x P(x|k)·S₁(u|x,c)`
-- ============================================================================

/-! Each listener latent comparison reduces (`listener_snd_lt`) to these
prior-weighted pooled speaker sums, one per `(kind, utterance, class)`. -/

private theorem pooled_bb_sup_tall :
    (∑ w : Height, (heightWeight .basketballPlayer w : ℝ≥0∞)
      * Sk .basketballPlayer (w, .superordinate) .tall) = ENNReal.ofReal
      (3419696012976237098/87425117428785675)
      := by
  rw [sumH, wterm_zero (by decide),
    wterm_zero (by decide),
    wterm 1 (by decide) Sk_bb_sup_tall_h2,
    wterm 2 (by decide) Sk_bb_sup_tall_h3,
    wterm 5 (by decide) Sk_bb_sup_tall_h4,
    wterm 10 (by decide) Sk_bb_sup_tall_h5,
    wterm 15 (by decide) Sk_bb_sup_tall_h6,
    wterm 20 (by decide) Sk_bb_sup_tall_h7,
    wterm 15 (by decide) Sk_bb_sup_tall_h8,
    wterm 10 (by decide) Sk_bb_sup_tall_h9,
    wterm 5 (by decide) Sk_bb_sup_tall_h10]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem pooled_bb_sub_tall :
    (∑ w : Height, (heightWeight .basketballPlayer w : ℝ≥0∞)
      * Sk .basketballPlayer (w, .subordinate) .tall) = ENNReal.ofReal
      (62392760462018538238286254570496496613/2114117529465183969687002824590045939)
      := by
  rw [sumH, wterm_zero (by decide),
    wterm_zero (by decide),
    wterm 1 (by decide) Sk_bb_sub_tall_h2,
    wterm 2 (by decide) Sk_bb_sub_tall_h3,
    wterm 5 (by decide) Sk_bb_sub_tall_h4,
    wterm 10 (by decide) Sk_bb_sub_tall_h5,
    wterm 15 (by decide) Sk_bb_sub_tall_h6,
    wterm 20 (by decide) Sk_bb_sub_tall_h7,
    wterm 15 (by decide) Sk_bb_sub_tall_h8,
    wterm 10 (by decide) Sk_bb_sub_tall_h9,
    wterm 5 (by decide) Sk_bb_sub_tall_h10]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem pooled_bb_sub_short :
    (∑ w : Height, (heightWeight .basketballPlayer w : ℝ≥0∞)
      * Sk .basketballPlayer (w, .subordinate) .short) = ENNReal.ofReal
      (2019907516260676484938710855389624/80499696504274372339676016101929)
      := by
  rw [sumH, wterm_zero (by decide),
    wterm_zero (by decide),
    wterm 1 (by decide) Sk_bb_sub_short_h2,
    wterm 2 (by decide) Sk_bb_sub_short_h3,
    wterm 5 (by decide) Sk_bb_sub_short_h4,
    wterm 10 (by decide) Sk_bb_sub_short_h5,
    wterm 15 (by decide) Sk_bb_sub_short_h6,
    wterm 20 (by decide) Sk_bb_sub_short_h7,
    wterm 15 (by decide) Sk_bb_sub_short_h8,
    wterm 10 (by decide) Sk_bb_sub_short_h9,
    wterm 5 (by decide) Sk_bb_sub_short_h10]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem pooled_bb_sup_short :
    (∑ w : Height, (heightWeight .basketballPlayer w : ℝ≥0∞)
      * Sk .basketballPlayer (w, .superordinate) .short) = ENNReal.ofReal
      (64325346939647892/4163100829942175)
      := by
  rw [sumH, wterm_zero (by decide),
    wterm_zero (by decide),
    wterm 1 (by decide) Sk_bb_sup_short_h2,
    wterm 2 (by decide) Sk_bb_sup_short_h3,
    wterm 5 (by decide) Sk_bb_sup_short_h4,
    wterm 10 (by decide) Sk_bb_sup_short_h5,
    wterm 15 (by decide) Sk_bb_sup_short_h6,
    wterm 20 (by decide) Sk_bb_sup_short_h7,
    wterm 15 (by decide) Sk_bb_sup_short_h8,
    wterm 10 (by decide) Sk_bb_sup_short_h9,
    wterm 5 (by decide) Sk_bb_sup_short_h10]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem pooled_jk_sub_tall :
    (∑ w : Height, (heightWeight .jockey w : ℝ≥0∞)
      * Sk .jockey (w, .subordinate) .tall) = ENNReal.ofReal
      (155384429852493476056570952810479211813570/5848861896507015285081311272942631063223)
      := by
  rw [sumH, wterm 5 (by decide) Sk_jk_sub_tall_h0,
    wterm 10 (by decide) Sk_jk_sub_tall_h1,
    wterm 15 (by decide) Sk_jk_sub_tall_h2,
    wterm 20 (by decide) Sk_jk_sub_tall_h3,
    wterm 15 (by decide) Sk_jk_sub_tall_h4,
    wterm 10 (by decide) Sk_jk_sub_tall_h5,
    wterm 5 (by decide) Sk_jk_sub_tall_h6,
    wterm 2 (by decide) Sk_jk_sub_tall_h7,
    wterm 1 (by decide) Sk_jk_sub_tall_h8,
    wterm_zero (by decide),
    wterm_zero (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem pooled_jk_sup_tall :
    (∑ w : Height, (heightWeight .jockey w : ℝ≥0∞)
      * Sk .jockey (w, .superordinate) .tall) = ENNReal.ofReal
      (5539365029597220640097/321141598021739379500)
      := by
  rw [sumH, wterm 5 (by decide) Sk_jk_sup_tall_h0,
    wterm 10 (by decide) Sk_jk_sup_tall_h1,
    wterm 15 (by decide) Sk_jk_sup_tall_h2,
    wterm 20 (by decide) Sk_jk_sup_tall_h3,
    wterm 15 (by decide) Sk_jk_sup_tall_h4,
    wterm 10 (by decide) Sk_jk_sup_tall_h5,
    wterm 5 (by decide) Sk_jk_sup_tall_h6,
    wterm 2 (by decide) Sk_jk_sup_tall_h7,
    wterm 1 (by decide) Sk_jk_sup_tall_h8,
    wterm_zero (by decide),
    wterm_zero (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem pooled_jk_sup_short :
    (∑ w : Height, (heightWeight .jockey w : ℝ≥0∞)
      * Sk .jockey (w, .superordinate) .short) = ENNReal.ofReal
      (498620823017054555970079/12834194578083084487875)
      := by
  rw [sumH, wterm 5 (by decide) Sk_jk_sup_short_h0,
    wterm 10 (by decide) Sk_jk_sup_short_h1,
    wterm 15 (by decide) Sk_jk_sup_short_h2,
    wterm 20 (by decide) Sk_jk_sup_short_h3,
    wterm 15 (by decide) Sk_jk_sup_short_h4,
    wterm 10 (by decide) Sk_jk_sup_short_h5,
    wterm 5 (by decide) Sk_jk_sup_short_h6,
    wterm 2 (by decide) Sk_jk_sup_short_h7,
    wterm 1 (by decide) Sk_jk_sup_short_h8,
    wterm_zero (by decide),
    wterm_zero (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

private theorem pooled_jk_sub_short :
    (∑ w : Height, (heightWeight .jockey w : ℝ≥0∞)
      * Sk .jockey (w, .subordinate) .short) = ENNReal.ofReal
      (205852396724165537349246288847942543830997093/7205797856496642831220175488265321469890736)
      := by
  rw [sumH, wterm 5 (by decide) Sk_jk_sub_short_h0,
    wterm 10 (by decide) Sk_jk_sub_short_h1,
    wterm 15 (by decide) Sk_jk_sub_short_h2,
    wterm 20 (by decide) Sk_jk_sub_short_h3,
    wterm 15 (by decide) Sk_jk_sub_short_h4,
    wterm 10 (by decide) Sk_jk_sub_short_h5,
    wterm 5 (by decide) Sk_jk_sub_short_h6,
    wterm 2 (by decide) Sk_jk_sub_short_h7,
    wterm 1 (by decide) Sk_jk_sub_short_h8,
    wterm_zero (by decide),
    wterm_zero (by decide)]
  repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; norm_num

-- ============================================================================
-- § 5. Semantic Properties
-- ============================================================================

/-- Basketball players' weighted height sum exceeds the person mean:
    Σ P(h|bball)·h = 568 > 430 = Σ P(h|person)·h (unnormalized). -/
theorem basketball_expected_taller_than_person :
    (Finset.univ.sum λ h : Height => basketballHeightWeight h * h.toNat) >
    (Finset.univ.sum λ h : Height => personHeightWeight h * h.toNat) := by native_decide

/-- Jockeys' weighted height sum is below the person mean. -/
theorem jockey_expected_shorter_than_person :
    (Finset.univ.sum λ h : Height => jockeyHeightWeight h * h.toNat) <
    (Finset.univ.sum λ h : Height => personHeightWeight h * h.toNat) := by native_decide

/-- For person, subordinate and superordinate use the same height distribution,
    so comparison class makes no difference. -/
theorem person_classes_identical :
    ∀ h : Height, l0HeightWeight .subordinate .person h =
                  l0HeightWeight .superordinate .person h := by
  native_decide

/-- Sanity check: silence doesn't discriminate between comparison classes.

    For the person kind (where subordinate = superordinate by
    `person_classes_identical`), L1 hearing silence assigns equal
    posterior to both comparison classes. This confirms the model's
    baseline: only informative utterances (tall/short) shift CC inference. -/
theorem silent_no_cc_preference :
    (listenerK .person .silent).snd .subordinate =
    (listenerK .person .silent).snd .superordinate := by
  unfold listenerK
  rw [RSA.Canonical.L1_latent_eq_iff]
  rfl

-- ============================================================================
-- § 6. S1 Endorsement Predictions — Polarity × Expectations Interaction
-- ============================================================================

/-! ### Basketball Player (expected tall)

At height 6 (above person mean 5, below basketball mean ~6.8):
- Under superordinate (people): "tall" IS endorsed (h=6 > E[person]=5)
- Under subordinate (basketball): "tall" NOT endorsed (h=6 < E[basketball]≈6.8)

At height 5 (at person mean, well below basketball mean):
- Under subordinate (basketball): "short" IS endorsed
- Under superordinate (people): "short" NOT endorsed (h=5 ≈ E[person]=5) -/

/-- "Tall" endorsed under superordinate at h=6: a basketball player of height 6
    is tall for a person (6 > person mean = 5). -/
theorem basketball_tall_endorsed_super :
    Sk .basketballPlayer (deg 6, .superordinate) .tall
      > Sk .basketballPlayer (deg 6, .superordinate) .silent := by
  rw [gt_iff_lt, Sk_lt_iff _ _ (Z_ne Z_bb_sup_h6 (by norm_num)),
    L0_bb_sup_silent_h6, L0_bb_sup_tall_h6, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- "Tall" NOT endorsed under subordinate at h=6: a basketball player of
    height 6 is average for a basketball player (6 < basketball mean ≈ 6.8). -/
theorem basketball_tall_not_endorsed_sub :
    ¬(Sk .basketballPlayer (deg 6, .subordinate) .tall
      > Sk .basketballPlayer (deg 6, .subordinate) .silent) := by
  rw [gt_iff_lt, not_lt, Sk_le_iff _ _ (Z_ne Z_bb_sub_h6 (by norm_num)),
    L0_bb_sub_tall_h6, L0_bb_sub_silent_h6, ENNReal.ofReal_le_ofReal_iff (by norm_num)]
  norm_num

/-- "Short" endorsed under subordinate at h=5: height 5 is well below the
    basketball mean, so "short" is informative within basketball players. -/
theorem basketball_short_endorsed_sub :
    Sk .basketballPlayer (deg 5, .subordinate) .short
      > Sk .basketballPlayer (deg 5, .subordinate) .silent := by
  rw [gt_iff_lt, Sk_lt_iff _ _ (Z_ne Z_bb_sub_h5 (by norm_num)),
    L0_bb_sub_silent_h5, L0_bb_sub_short_h5, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- "Short" NOT endorsed under superordinate at h=5: height 5 is exactly
    the person mean, so "short" is uninformative relative to people. -/
theorem basketball_short_not_endorsed_super :
    ¬(Sk .basketballPlayer (deg 5, .superordinate) .short
      > Sk .basketballPlayer (deg 5, .superordinate) .silent) := by
  rw [gt_iff_lt, not_lt, Sk_le_iff _ _ (Z_ne Z_bb_sup_h5 (by norm_num)),
    L0_bb_sup_short_h5, L0_bb_sup_silent_h5, ENNReal.ofReal_le_ofReal_iff (by norm_num)]
  norm_num

/-! ### Jockey (expected short)

At height 4 (below person mean 5, above jockey mean ~3.2):
- Under subordinate (jockeys): "tall" IS endorsed (h=4 > E[jockey]≈3.2)
- Under superordinate (people): "tall" NOT endorsed (h=4 < E[person]=5)
- Under superordinate (people): "short" IS endorsed (h=4 < E[person]=5)
- Under subordinate (jockeys): "short" NOT endorsed (h=4 > E[jockey]≈3.2) -/

/-- "Tall" endorsed under subordinate at h=4: a jockey of height 4
    is tall for a jockey (4 > jockey mean ≈ 3.2). -/
theorem jockey_tall_endorsed_sub :
    Sk .jockey (deg 4, .subordinate) .tall
      > Sk .jockey (deg 4, .subordinate) .silent := by
  rw [gt_iff_lt, Sk_lt_iff _ _ (Z_ne Z_jk_sub_h4 (by norm_num)),
    L0_jk_sub_silent_h4, L0_jk_sub_tall_h4, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- "Tall" NOT endorsed under superordinate at h=4: height 4 is below the
    person mean, so "tall" is uninformative relative to people. -/
theorem jockey_tall_not_endorsed_super :
    ¬(Sk .jockey (deg 4, .superordinate) .tall
      > Sk .jockey (deg 4, .superordinate) .silent) := by
  rw [gt_iff_lt, not_lt, Sk_le_iff _ _ (Z_ne Z_jk_sup_h4 (by norm_num)),
    L0_jk_sup_tall_h4, L0_jk_sup_silent_h4, ENNReal.ofReal_le_ofReal_iff (by norm_num)]
  norm_num

/-- "Short" endorsed under superordinate at h=4: height 4 is below the
    person mean (4 < E[person]=5). -/
theorem jockey_short_endorsed_super :
    Sk .jockey (deg 4, .superordinate) .short
      > Sk .jockey (deg 4, .superordinate) .silent := by
  rw [gt_iff_lt, Sk_lt_iff _ _ (Z_ne Z_jk_sup_h4 (by norm_num)),
    L0_jk_sup_silent_h4, L0_jk_sup_short_h4, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- "Short" NOT endorsed under subordinate at h=4: a jockey of height 4
    is average for a jockey, so "short" is uninformative. -/
theorem jockey_short_not_endorsed_sub :
    ¬(Sk .jockey (deg 4, .subordinate) .short
      > Sk .jockey (deg 4, .subordinate) .silent) := by
  rw [gt_iff_lt, not_lt, Sk_le_iff _ _ (Z_ne Z_jk_sub_h4 (by norm_num)),
    L0_jk_sub_short_h4, L0_jk_sub_silent_h4, ENNReal.ofReal_le_ofReal_iff (by norm_num)]
  norm_num

-- ============================================================================
-- § 7. Cross-Study Bridge: [lassiter-goodman-2017]
-- ============================================================================

/-! This model extends [lassiter-goodman-2017]'s threshold RSA.
The key structural relationship:
- LG2017 treats the threshold θ as a `Latent` variable (L1 infers θ)
- TG2022 marginalizes θ analytically (via `thresholdCount`) and adds
  comparison class c as the `Latent` variable (L1 infers c)

The height priors used here (`personHeightWeight`, `basketballHeightWeight`)
match [lassiter-goodman-2017]'s general-population and
basketball-player priors respectively — same empirical domain, different
question. The cross-paper compatibility was previously enforced via
`personWeight_eq_lassiterGoodman` / `basketballWeight_eq_lassiterGoodman`
bridge theorems referencing `RSA.LassiterGoodman2017.heightPrior`; those
were removed when L&G's old bundled-config formalisation was retired.
The PMF formalisation (`LassiterGoodman2017PMF.lean`) does not duplicate
the empirical priors. -/

-- ============================================================================
-- § 8. L1 Comparison Class Inference (Eq. 1)
-- ============================================================================

/-! ### The paper's main prediction: L1 comparison class inference

The S1 endorsement theorems (§ 6) show that S1 behaves differently under
each comparison class. The paper's Eq. 1 prediction is about the LISTENER:
after hearing an adjective about a kind, which comparison class does L1 infer?

    L₁(x, c | u, k) ∝ S₁(u | x, c) · P(x | k) · P(c | k)

After marginalizing over height x, the posterior over comparison classes is
`(listenerK k u).snd`. The polarity × expectations interaction:

- **Expected adjective** (tall basketball, short jockey) → **superordinate**
- **Unexpected adjective** (short basketball, tall jockey) → **subordinate** -/

/-- Basketball + "tall" → listener infers superordinate: a basketball player
    described as "tall" is tall even for a person — unexpected, hence
    informative under the superordinate comparison class. -/
theorem basketball_tall_infers_super :
    (listenerK .basketballPlayer .tall).snd .superordinate >
    (listenerK .basketballPlayer .tall).snd .subordinate := by
  rw [gt_iff_lt, listener_snd_lt, pooled_bb_sub_tall, pooled_bb_sup_tall,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- Basketball + "short" → listener infers subordinate: "short for a
    basketball player" is more informative than "short for a person"
    (since basketball players are expected to be tall). -/
theorem basketball_short_infers_sub :
    (listenerK .basketballPlayer .short).snd .subordinate >
    (listenerK .basketballPlayer .short).snd .superordinate := by
  rw [gt_iff_lt, listener_snd_lt, pooled_bb_sup_short, pooled_bb_sub_short,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- Jockey + "tall" → listener infers subordinate: "tall for a jockey"
    is more informative than "tall for a person" (since jockeys are
    expected to be short). -/
theorem jockey_tall_infers_sub :
    (listenerK .jockey .tall).snd .subordinate >
    (listenerK .jockey .tall).snd .superordinate := by
  rw [gt_iff_lt, listener_snd_lt, pooled_jk_sup_tall, pooled_jk_sub_tall,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- Jockey + "short" → listener infers superordinate: a jockey described
    as "short" is short even for a person — unexpected, hence informative
    under the superordinate comparison class. -/
theorem jockey_short_infers_super :
    (listenerK .jockey .short).snd .superordinate >
    (listenerK .jockey .short).snd .subordinate := by
  rw [gt_iff_lt, listener_snd_lt, pooled_jk_sub_short, pooled_jk_sup_short,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

-- ============================================================================
-- § 9. Grounding: Polarity × Expectations Rows
-- ============================================================================

/-! The polarity × expectations interaction from §§ 6, 8 grounds the rows in
`Data/Examples/TesslerGoodman2022.json` (§3.2.1, Fig. 3): in every row, the
EXPECTED adjective (consistent with the kind's height distribution) is
attested with SUPERORDINATE comparison and the UNEXPECTED adjective with
SUBORDINATE comparison. `L1_matches_all_rows` replicates the paper's Eq. 1
prediction for each row. -/

open Data.Examples

/-- Kind adapter: the row's `noun` feature as a `Kind`. -/
def kindOf (row : LinguisticExample) : Option Kind :=
  match row.feature? "noun" with
  | some "basketball player" => some .basketballPlayer
  | some "jockey"            => some .jockey
  | _ => none

/-- Utterance adapter: the row's `adjective` feature as an `Utterance`. -/
def uttOf (row : LinguisticExample) : Option Utterance :=
  match row.feature? "adjective" with
  | some "tall"  => some .tall
  | some "short" => some .short
  | _ => none

/-- Comparison-class adapter: the row's attested `inferred_class` feature. -/
def ccOf (row : LinguisticExample) : Option ComparisonClass :=
  match row.feature? "inferred_class" with
  | some "subordinate"   => some .subordinate
  | some "superordinate" => some .superordinate
  | _ => none

/-- The alternative comparison class. -/
def ComparisonClass.flip : ComparisonClass → ComparisonClass
  | .subordinate   => .superordinate
  | .superordinate => .subordinate

/-- The pragmatic listener prefers the row's attested comparison class over
    the alternative (vacuous when a row lacks the adapter features). -/
def L1Matches (row : LinguisticExample) : Prop :=
  match kindOf row, uttOf row, ccOf row with
  | some k, some u, some c =>
      (listenerK k u).snd c > (listenerK k u).snd c.flip
  | _, _, _ => True

/-- **Transfer theorem** (Eq. 1, Fig. 3): on every row, L1's posterior
    prefers the attested comparison class. -/
theorem L1_matches_all_rows : ∀ row ∈ Examples.all, L1Matches row := by
  intro row hrow
  fin_cases hrow
  · exact basketball_tall_infers_super
  · exact basketball_short_infers_sub
  · exact jockey_tall_infers_sub
  · exact jockey_short_infers_super

-- ============================================================================
-- § 10. Alternative: Literal Listener Model (Eq. 6, Fig. 2)
-- ============================================================================

/-! ### The literal model makes the OPPOSITE predictions

[tessler-goodman-2022] §2 contrasts the pragmatic listener (Eq. 1) with
an alternative literal listener (Eq. 6) that does not reason about a rational
speaker:

    L₀(x, θ, c | u, k) ∝ δ_{⟦u⟧}(x,θ) · P(x | c) · P(θ) · P(c | k)

This model updates beliefs about x and c jointly via the literal meaning,
using the comparison-class-specific prior P(x | c), but without S1
informativity. It effectively asks: under which comparison class is the
utterance more likely to be literally true? For "tall basketball player,"
tallness is more probable under the basketball distribution (shifted right),
so the literal model prefers subordinate — the OPPOSITE of the pragmatic
model and the data.

The pragmatic model inverts this because S1 normalizes by the total
literal-listener mass Z_c(u), penalizing classes where the utterance is
uninformative (too many heights satisfy it) and rewarding classes where the
utterance is surprising. -/

/-- Unnormalized literal score: Σ_h P(h|c) · |{θ : ⟦u⟧(h,θ)}|.
    Total literal-listener mass for comparison class c, marginalized
    over heights and thresholds. -/
def literalClassScore (k : Kind) (c : ComparisonClass) (u : Utterance) : Nat :=
  Finset.univ.sum λ h : Height => l0HeightWeight c k h * thresholdCount u h

/-- Literal: basketball + "tall" → subordinate.
    Basketball players' rightward-shifted heights make "tall" more often
    literally true under subordinate comparison.
    Opposite of pragmatic `basketball_tall_infers_super`. -/
theorem literal_basketball_tall_sub :
    literalClassScore .basketballPlayer .subordinate .tall >
    literalClassScore .basketballPlayer .superordinate .tall := by native_decide

/-- Literal: basketball + "short" → superordinate.
    Opposite of pragmatic `basketball_short_infers_sub`. -/
theorem literal_basketball_short_super :
    literalClassScore .basketballPlayer .superordinate .short >
    literalClassScore .basketballPlayer .subordinate .short := by native_decide

/-- Literal: jockey + "tall" → superordinate.
    Opposite of pragmatic `jockey_tall_infers_sub`. -/
theorem literal_jockey_tall_super :
    literalClassScore .jockey .superordinate .tall >
    literalClassScore .jockey .subordinate .tall := by native_decide

/-- Literal: jockey + "short" → subordinate.
    Opposite of pragmatic `jockey_short_infers_super`. -/
theorem literal_jockey_short_sub :
    literalClassScore .jockey .subordinate .short >
    literalClassScore .jockey .superordinate .short := by native_decide

/-- Every literal prediction is reversed by the pragmatic model (Fig. 2).
    This is the paper's key scientific claim: comparison class inference
    requires social reasoning via S1, not just Bayesian updating on
    literal truth conditions. -/
theorem pragmatic_reverses_literal :
    (listenerK .basketballPlayer .tall).snd .superordinate >
    (listenerK .basketballPlayer .tall).snd .subordinate ∧
    (listenerK .basketballPlayer .short).snd .subordinate >
    (listenerK .basketballPlayer .short).snd .superordinate ∧
    (listenerK .jockey .tall).snd .subordinate >
    (listenerK .jockey .tall).snd .superordinate ∧
    (listenerK .jockey .short).snd .superordinate >
    (listenerK .jockey .short).snd .subordinate :=
  ⟨basketball_tall_infers_super, basketball_short_infers_sub,
   jockey_tall_infers_sub, jockey_short_infers_super⟩

-- ============================================================================
-- § 11. Dimension Generality: "Warm (for Winter)"
-- ============================================================================

/-! The paper's title example uses temperature, not height. The model is
dimension-general: any relative gradable adjective whose comparison class
shifts the degree prior produces the polarity × expectations interaction.

The temperature domain maps onto the height domain:
- Winter (expected cold) ↔ Jockey (expected short): prior peaked at 3
- Summer (expected warm) ↔ Basketball (expected tall): prior peaked at 7
- warm ↔ tall (positive adjective), cold ↔ short (negative adjective)

Since the weight functions are identical, the § 8 predictions transfer:

| Context | Adjective | Inferred CC | Height analogue |
|---------|-----------|-------------|-----------------|
| winter  | warm  | subordinate   | `jockey_tall_infers_sub` |
| winter  | cold  | superordinate | `jockey_short_infers_super` |
| summer  | warm  | superordinate | `basketball_tall_infers_super` |
| summer  | cold  | subordinate   | `basketball_short_infers_sub` |

This connects to `Degree.Dimension.temperature`: temperature
adjectives (*warm*/*cold*) are open-scale relative gradable adjectives, so — like
*tall* — they require a comparison class (`open_scale_requires_cc_inference`;
[kennedy-2007]). -/

/-- The literal/pragmatic reversal transfers to temperature via the
    winter ↔ jockey mapping. The literal model predicts "warm in winter"
    → superordinate (warm is more often literally true in the general
    population than in winter), but the pragmatic model correctly predicts
    subordinate: "warm for winter" is informative within the season. -/
theorem literal_reversal_transfers_to_temp :
    -- Literal: "winter + warm" ↔ "jockey + tall" → superordinate
    literalClassScore .jockey .superordinate .tall >
    literalClassScore .jockey .subordinate .tall ∧
    -- Pragmatic: "winter + warm" ↔ "jockey + tall" → subordinate
    (listenerK .jockey .tall).snd .subordinate >
    (listenerK .jockey .tall).snd .superordinate :=
  ⟨literal_jockey_tall_super, jockey_tall_infers_sub⟩

-- ============================================================================
-- § 12. [kennedy-2007] Applicability Chain
-- ============================================================================

/-! ### Why this model applies to "tall" but not "full"

[kennedy-2007]'s Interpretive Economy (§4.3, p. 36) determines the
standard of comparison from scale structure. For open-scale (relative)
adjectives like "tall", the standard-fixing function **s** requires
contextual domain information — "the distribution of objects in some
domain (a comparison class)" (p. 42). For closed-scale (absolute)
adjectives like "full", the standard is the scale endpoint — fixed
regardless of context.

Crucially, Kennedy argues (§2.3, p. 16) that the comparison class is
NOT a semantic argument of *pos* (contra [klein-1980]), but rather
contextual information that feeds into **s**. [tessler-goodman-2022]
provides the computational mechanism for determining this contextual
parameter: the comparison class is inferred pragmatically via RSA as a
latent variable. This is architecturally compatible with Kennedy's view —
the CC is pragmatic/contextual, not a constituent of the logical form.

    open scale → contextual standard → CC feeds into s → L1 infers it
    bounded scale → endpoint standard → s fixed by scale → nothing to infer

The chain connects three independent modules:
1. `Degree.interpretiveEconomy` (Theory: scale → standard type)
2. `Degree.PositiveStandard.RequiresComparisonClass` (Theory: standard → domain-dependent?)
3. `listenerK` with latent `ComparisonClass` (this file: infer CC) -/

open Degree (interpretiveEconomy PositiveStandard IsClassA)

/-- Height is an open-scale dimension: "tall" is relative (Class A). -/
theorem height_is_classA : IsClassA Core.Order.Boundedness.open_ := trivial

/-- Open scale → contextual domain inference applies (the full chain).
    This is a three-step argument:
    1. "tall" has an open scale (lexical fact)
    2. Open scale → contextual standard via **s** (Interpretive Economy)
    3. Contextual **s** → needs domain information (Kennedy 2007, p. 42)
    Therefore the domain (descriptively: comparison class) must be inferred
    — exactly what `listenerK` models with latent `ComparisonClass`.
    This is compatible with Kennedy's view: the CC is pragmatic/contextual
    (inferred by L1), not a semantic argument of *pos*. -/
theorem open_scale_requires_cc_inference :
    (interpretiveEconomy .open_).RequiresComparisonClass := trivial

/-- Closed scale → contextual domain inference is irrelevant.
    "Full" has an endpoint standard via Interpretive Economy; the threshold
    is the scale maximum regardless of context. No domain to infer. -/
theorem closed_scale_no_cc_inference :
    ¬ (interpretiveEconomy .closed).RequiresComparisonClass := id

-- ============================================================================
-- § 13. Connection to Generic Language ([tessler-goodman-2019])
-- ============================================================================

/-! Threshold semantics for gradable adjectives generalizes to generic
language: "Birds fly south in the winter" ≈ P(x flies south | x is a bird) > θ
([tessler-goodman-2019]). Both models share:

1. A threshold variable θ setting the standard
2. A prior P(x | c) conditioned on category membership
3. Pragmatic inference about the contextually appropriate threshold/class

The comparison class model (this file) infers which c maximizes the pragmatic
listener's posterior. The generics model infers which θ is pragmatically
optimal. Same RSA machinery applied to different latent variables. -/

-- ============================================================================
-- § 14. Comparison Class as Nested Domain Restriction
-- ============================================================================

/-! The comparison class hierarchy is structurally a `DDRP`:
subordinate (restricted) ⊆ superordinate (unrestricted). Going from subordinate
to superordinate widens the reference population.

This connects comparison class inference to the same nesting pattern used
by [ritchie-schiller-2024]'s domain restriction possibilities. -/

open Quantification.DomainRestriction (DDRP)

private def ComparisonClass.toFin : ComparisonClass → Fin 2
  | .subordinate => 0
  | .superordinate => 1

private theorem ComparisonClass.toFin_injective :
    Function.Injective ComparisonClass.toFin := by
  intro a b h; cases a <;> cases b <;> simp_all [ComparisonClass.toFin]

instance : LinearOrder ComparisonClass :=
  LinearOrder.lift' ComparisonClass.toFin ComparisonClass.toFin_injective

instance : OrderTop ComparisonClass where
  top := .superordinate
  le_top a := by cases a <;> decide

/-- Whether a height has nonzero prior weight for a given kind. -/
def isTypical (k : Kind) (h : Height) : Bool :=
  heightWeight k h > 0

/-- The comparison class hierarchy as a nested restriction on heights. -/
def compClassRestriction (k : Kind) : DDRP ComparisonClass Height where
  region
    | .subordinate => λ h => isTypical k h = true
    | .superordinate => Set.univ
  monotone s₁ s₂ h d hr := by
    cases s₁ <;> cases s₂ <;> simp_all [Set.mem_univ]
    · exact absurd h (by decide)
  top_total := rfl

/-- Nesting: subordinate ⊆ superordinate for all kinds. -/
theorem compClass_nesting (k : Kind) (h : Height) :
    h ∈ (compClassRestriction k).region .subordinate →
    h ∈ (compClassRestriction k).region .superordinate :=
  λ hr => (compClassRestriction k).monotone (by decide) hr

end TesslerGoodman2022
