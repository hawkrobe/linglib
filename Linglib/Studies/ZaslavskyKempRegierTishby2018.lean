import Linglib.Pragmatics.Efficiency
import Linglib.Data.WALS.Features.F132A
import Linglib.Data.WALS.Features.F133A
import Linglib.Data.WALS.Features.F134A
import Linglib.Data.WALS.Features.F135A

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

This file formalizes the per-language WALS color profiles (the eight
WALS-sourced `ColorProfile`s below, derived via `ColorProfile.fromWALS`) observable
through the efficient-communication framework in `Pragmatics.Efficiency`
(`CostPair`, `weightedCost = cost₂ + β·cost₁`, `efficiencyLossAt`).

## What is derived vs. cited

* **Derived** (from the WALS-sourced color profiles): the Berlin-Kay
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

open Pragmatics.Efficiency
/-! ### WALS Ch 132: Number of non-derived basic color categories -/

/-- Number of non-derived basic color categories (WALS Ch 132,
    [kay-maffi-2013]). Ranges from 3 to 6 along the Berlin & Kay
    sequence; transitional half-values represent languages with one
    composite category undergoing splitting. -/
inductive NonDerivedColorCount where
  | three
  | threeHalf
  | four
  | fourHalf
  | five
  | fiveHalf
  | six
  deriving DecidableEq, Repr

/-! ### WALS Ch 133: Total number of basic color categories -/

/-- Total number of basic color categories including derived ones
    (WALS Ch 133, [kay-maffi-2013a]). Ranges from 3–4 (minimal systems)
    to the top bucket, WALS's "more than 10" — canonically 11 basic terms,
    the Berlin & Kay Stage-VII maximum (e.g., English, Russian). -/
inductive BasicColorCount where
  | v3to4
  | v4to5
  | v6to6h
  | v7to7h
  | v8to8h
  | v9to10
  | v11
  deriving DecidableEq, Repr

/-! ### WALS Ch 134: Green and blue -/

/-- How a language treats the green-blue region of color space
    (WALS Ch 134, [kay-maffi-2013b]). The classic *grue* / green-blue
    composite distinction, with several other composite patterns
    (with black, with yellow). -/
inductive GreenBlueRelation where
  /-- Separate terms for green and blue. -/
  | distinct
  /-- A single *grue* term covering both green and blue. -/
  | merged
  /-- A single term covering black, green, and blue. -/
  | blackGreenBlue
  /-- Black/blue merged, green separate. -/
  | blackBlueVsGreen
  /-- Yellow, green, blue all merged. -/
  | yellowGreenBlue
  /-- Yellow/green merged, blue separate. -/
  | yellowGreenVsBlue
  /-- No green or blue term at all. -/
  | noTerm
  deriving DecidableEq, Repr

/-! ### WALS Ch 135: Red and yellow -/

/-- How a language treats the red-yellow region of color space
    (WALS Ch 135, [kay-maffi-2013c]). -/
inductive RedYellowRelation where
  /-- Separate terms for red and yellow. -/
  | distinct
  /-- A single term covering both red and yellow. -/
  | merged
  /-- Yellow/green/blue merged, vs red. -/
  | yellowGreenBlueVsRed
  /-- Yellow/green merged, vs red. -/
  | yellowGreenVsRed
  /-- No red or yellow term at all. -/
  | noTerm
  deriving DecidableEq, Repr

/-! ### Per-language profile -/

/-- A language's color-naming profile across [wals-2013] Chs 132–135.
    Coverage is sparse (~120 languages); fields are optional. -/
structure ColorProfile where
  language : String
  iso : String := ""
  family : String := ""
  /-- Ch 132: non-derived basic color categories. -/
  nonDerived : Option NonDerivedColorCount := none
  /-- Ch 133: total basic color categories. -/
  basic : Option BasicColorCount := none
  /-- Ch 134: green-blue relation. -/
  greenBlue : Option GreenBlueRelation := none
  /-- Ch 135: red-yellow relation. -/
  redYellow : Option RedYellowRelation := none
  deriving Repr

/-! ### WALS converters -/

/-- Convert WALS 132A non-derived-color-count values into the substrate enum. -/
def fromWALS132A : Data.WALS.F132A.NumberOfNonDerivedBasicColourCategories → NonDerivedColorCount
  | .v3  => .three
  | .v35 => .threeHalf
  | .v4  => .four
  | .v45 => .fourHalf
  | .v5  => .five
  | .v55 => .fiveHalf
  | .v6  => .six

/-- Convert WALS 133A basic-color-count values into the substrate enum. -/
def fromWALS133A : Data.WALS.F133A.NumberOfBasicColourCategories → BasicColorCount
  | .v34   => .v3to4
  | .v4555 => .v4to5
  | .v665  => .v6to6h
  | .v775  => .v7to7h
  | .v885  => .v8to8h
  | .v910  => .v9to10
  | .v11   => .v11

/-- Convert WALS 134A green-blue values into the substrate enum. -/
def fromWALS134A : Data.WALS.F134A.GreenAndBlue → GreenBlueRelation
  | .greenVsBlue       => .distinct
  | .greenBlue         => .merged
  | .blackGreenBlue    => .blackGreenBlue
  | .blackBlueVsGreen  => .blackBlueVsGreen
  | .yellowGreenBlue   => .yellowGreenBlue
  | .yellowGreenVsBlue => .yellowGreenVsBlue
  | .none              => .noTerm

/-- Convert WALS 135A red-yellow values into the substrate enum. -/
def fromWALS135A : Data.WALS.F135A.RedAndYellow → RedYellowRelation
  | .redVsYellow          => .distinct
  | .redYellow            => .merged
  | .yellowGreenBlueVsRed => .yellowGreenBlueVsRed
  | .yellowGreenVsRed     => .yellowGreenVsRed
  | .none                 => .noTerm

/-- Build a `ColorProfile` from the WALS Chs 132–135 rows for an ISO 639-3
    code, mapping each chapter's datapoint through its converter; a field for
    which WALS has no row is `none`. Makes the per-language Fragment profiles
    true-by-construction from the auto-generated WALS tables rather than
    hand-transcribed literals. -/
def ColorProfile.fromWALS (language iso family : String) : ColorProfile :=
  { language := language
  , iso := iso
  , family := family
  , nonDerived := (Data.WALS.F132A.lookupISO iso).map (λ d => fromWALS132A d.value)
  , basic := (Data.WALS.F133A.lookupISO iso).map (λ d => fromWALS133A d.value)
  , greenBlue := (Data.WALS.F134A.lookupISO iso).map (λ d => fromWALS134A d.value)
  , redYellow := (Data.WALS.F135A.lookupISO iso).map (λ d => fromWALS135A d.value) }

/-! ### The eight WALS-sourced sample profiles -/

def english : ColorProfile := ColorProfile.fromWALS "English" "eng" "Indo-European"
def french : ColorProfile := ColorProfile.fromWALS "French" "fra" "Indo-European"
def german : ColorProfile := ColorProfile.fromWALS "German" "deu" "Indo-European"
def japanese : ColorProfile := ColorProfile.fromWALS "Japanese" "jpn" "Japonic"
def korean : ColorProfile := ColorProfile.fromWALS "Korean" "kor" "Koreanic"
def mandarin : ColorProfile := ColorProfile.fromWALS "Mandarin Chinese" "cmn" "Sino-Tibetan"
def russian : ColorProfile := ColorProfile.fromWALS "Russian" "rus" "Indo-European"
def spanish : ColorProfile := ColorProfile.fromWALS "Spanish" "spa" "Indo-European"


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
  [english, french, german, japanese, korean, mandarin, spanish, russian]

/-- Every sampled language draws both the warm (red/yellow) and cool
    (green/blue) boundaries — all are high-complexity, late-sequence systems,
    consistent with their high category counts and fitted `β_l > 1`. -/
theorem sample_all_warm_and_cool_split :
    ∀ p ∈ sample, p.redYellow = some .distinct ∧ p.greenBlue = some .distinct := by
  decide

/-- Concrete complexity contrast: English (11 basic terms) sits higher on the IB
    complexity axis than Mandarin (8–8.5), as the Berlin-Kay sequence predicts. -/
theorem english_more_complex_than_mandarin :
    ibComplexity mandarin < ibComplexity english := by
  decide

/-- The contrast lifts to the IB objective: for every β ≥ 0 (and any fixed
    accuracy), English's β-scalarized complexity cost is at least Mandarin's. -/
theorem english_weightedCost_ge_mandarin (acc β : ℝ) (hβ : 0 ≤ β) :
    weightedCost (ibCost mandarin acc) β ≤
    weightedCost (ibCost english acc) β :=
  weightedCost_mono_in_complexity acc β hβ
    (le_of_lt english_more_complex_than_mandarin)

end ZaslavskyKempRegierTishby2018
