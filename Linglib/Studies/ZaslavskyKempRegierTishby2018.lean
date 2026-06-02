import Linglib.Pragmatics.Efficiency
import Linglib.Fragments.English.Color
import Linglib.Fragments.French.Color
import Linglib.Fragments.German.Color
import Linglib.Fragments.Japanese.Color
import Linglib.Fragments.Korean.Color
import Linglib.Fragments.Mandarin.Color
import Linglib.Fragments.Spanish.Color
import Linglib.Fragments.Slavic.Russian.Color

/-!
# Zaslavsky, Kemp, Regier & Tishby (2018): efficient compression in color naming
[zaslavsky-kemp-regier-tishby-2018] [berlin-kay-1969] [wals-2013]

[zaslavsky-kemp-regier-tishby-2018] argue that color-naming systems
efficiently compress meanings into words by optimizing the Information
Bottleneck (IB) trade-off between lexicon **complexity** (the information rate
`I(M;W)`) and **accuracy** (`I(W;U)`). Cross-language variation is captured by a
single trade-off parameter β, and the Berlin & Kay evolutionary sequence
([berlin-kay-1969]: dark/light, then red, then green/yellow, then blue, …)
falls out as motion *up the complexity axis* — successive systems carve color
space more finely, paying complexity for accuracy.

This file is the consumer that makes the per-language WALS color profiles
(`Fragments/{Lang}/Color.lean`, typed by `Typology.ColorProfile`) observable
through the efficient-communication framework in `Pragmatics.Efficiency`
(`CostPair`, `weightedCost = cost₂ + β·cost₁`, `efficiencyLossAt`).

## What is derived vs. cited

* **Derived** (from the WALS-sourced Fragment profiles): the Berlin-Kay
  *complexity coordinate* of each sampled language — the number of basic color
  categories (WALS Ch 133). The IB complexity `I(M;W)` of a deterministic
  K-word system is bounded by `log K`, so the category count is a monotone
  *handle* on the complexity axis (not `I(M;W)` itself).
* **Bridge** (via `Pragmatics.Efficiency`): the β-scalarized IB objective
  `weightedCost` is monotone in this complexity coordinate, so the Berlin-Kay
  category ordering is exactly an ordering on the IB complexity axis.
* **Cited stimulus** (from the paper, not formalized): real languages are
  *near*-optimal — they lie close to the IB curve with small efficiency loss
  `ε_l`, at a fitted `β_l ≳ 1` (e.g. English `β_l ≈ 1.085`, Fig. 4). The
  formal anchor here is only the idealized optimum (zero loss at coincidence);
  the empirical near-optimality is the paper's measured result.

## Main results

* `bk_complexity_strictMono`: the category-count handle is strictly monotone in
  the WALS Ch 133 ordering (the Berlin-Kay sequence).
* `weightedCost_mono_in_complexity`: more categories ⇒ higher β-scalarized IB
  complexity cost, for every β ≥ 0 — the structural bridge.
* `sample_all_warm_and_cool_split`: every sampled language distinguishes both
  red/yellow and green/blue (all are high-complexity, late-sequence systems).
-/

namespace ZaslavskyKempRegierTishby2018

open Typology Pragmatics.Efficiency

/-! ### The Berlin-Kay complexity coordinate -/

/-- A representative basic-category count for each WALS Ch 133 bucket (its lower
    bound). Only the *ordering* matters: this is a monotone handle on the IB
    complexity axis `I(M;W) ≤ log K`, where `K` is the number of color words. -/
def basicCount : BasicColorCount → ℕ
  | .v3to4  => 3
  | .v4to5  => 4
  | .v6to6h => 6
  | .v7to7h => 7
  | .v8to8h => 8
  | .v9to10 => 9
  | .v11    => 11

/-- IB complexity handle for a color profile: its basic-category count
    (`0` when WALS records no Ch 133 datum). -/
def ibComplexity (p : ColorProfile) : ℕ := (p.basic.map basicCount).getD 0

/-- The category-count handle is strictly monotone along the WALS Ch 133
    ordering — i.e. along the Berlin & Kay evolutionary sequence
    ([berlin-kay-1969]). -/
theorem bk_complexity_strictMono :
    basicCount .v3to4 < basicCount .v4to5 ∧
    basicCount .v4to5 < basicCount .v6to6h ∧
    basicCount .v6to6h < basicCount .v7to7h ∧
    basicCount .v7to7h < basicCount .v8to8h ∧
    basicCount .v8to8h < basicCount .v9to10 ∧
    basicCount .v9to10 < basicCount .v11 := by decide

/-! ### Bridge to the Information-Bottleneck objective -/

/-- A color system as a `Pragmatics.Efficiency.CostPair`: `cost₁` is the IB
    complexity handle (category count), `cost₂` is the system's accuracy/
    distortion component, left abstract (WALS does not record it per language). -/
def ibCost (p : ColorProfile) (acc : ℝ) : CostPair :=
  { cost₁ := (ibComplexity p : ℝ), cost₂ := acc }

/-- **Structural bridge.** Under the β-scalarized IB objective `weightedCost`,
    a system with more basic categories has at least as high a complexity cost,
    for every β ≥ 0 and any fixed accuracy. The Berlin-Kay category ordering is
    therefore an ordering on the IB complexity axis the paper plots. -/
theorem weightedCost_mono_in_complexity
    {p q : ColorProfile} (acc β : ℝ) (hβ : 0 ≤ β)
    (h : ibComplexity p ≤ ibComplexity q) :
    weightedCost (ibCost p acc) β ≤ weightedCost (ibCost q acc) β := by
  have hc : (ibComplexity p : ℝ) ≤ (ibComplexity q : ℝ) := by exact_mod_cast h
  have := mul_le_mul_of_nonneg_left hc hβ
  simp only [weightedCost, ibCost]
  linarith

/-- The idealized anchor of the paper's near-optimality finding: a color system
    that coincides with the IB-optimal system at its fitted β has zero
    efficiency loss. Real languages are *near*-optimal (small nonzero `ε_l`),
    which is the paper's measured result rather than a theorem here. -/
theorem optimal_system_zero_loss (c : CostPair) (β : ℝ) :
    efficiencyLossAt c c β = 0 := efficiencyLossAt_self c β

/-! ### The Fragment sample -/

/-- The eight WALS-sourced color profiles formalized as Fragments. All are
    industrialized-language systems near the top of the Berlin & Kay sequence. -/
def sample : List ColorProfile :=
  [English.colorProfile, French.colorProfile, German.colorProfile,
   Japanese.colorProfile, Korean.colorProfile, Mandarin.colorProfile,
   Spanish.colorProfile, Russian.colorProfile]

/-- Every sampled language draws both the warm (red/yellow) and cool
    (green/blue) boundaries — all are high-complexity, late-sequence systems,
    consistent with their high category counts and fitted `β_l > 1`. -/
theorem sample_all_warm_and_cool_split :
    ∀ p ∈ sample, p.redYellow = some .distinct ∧ p.greenBlue = some .distinct := by
  decide

/-- Concrete complexity contrast: English (11 basic terms) sits higher on the IB
    complexity axis than Mandarin (8–8.5), as the Berlin-Kay sequence predicts. -/
theorem english_more_complex_than_mandarin :
    ibComplexity Mandarin.colorProfile < ibComplexity English.colorProfile := by
  decide

/-- The contrast lifts to the IB objective: for every β ≥ 0 (and any fixed
    accuracy), English's β-scalarized complexity cost is at least Mandarin's. -/
theorem english_weightedCost_ge_mandarin (acc β : ℝ) (hβ : 0 ≤ β) :
    weightedCost (ibCost Mandarin.colorProfile acc) β ≤
    weightedCost (ibCost English.colorProfile acc) β :=
  weightedCost_mono_in_complexity acc β hβ
    (le_of_lt english_more_complex_than_mandarin)

end ZaslavskyKempRegierTishby2018
