import Linglib.Semantics.Degree.Kennedy
import Linglib.Semantics.Degree.Comparative
import Linglib.Semantics.Degree.Gradability.Basic
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Core.Order.Boundedness
import Linglib.Semantics.Degree.DirectedMeasure
import Linglib.Features.PropertyDomain
import Linglib.Features.Antonymy

/-!
# Kennedy 2007: Relative vs Absolute Gradable Adjectives

Study of [kennedy-2007] ("Vagueness and grammar"), grounding the paper's
central claims against the degree substrate and the English adjective Fragment.
[kennedy-mcnally-2005] [rotstein-winter-2004]

1. **Scale structure fixes the standard.** Interpretive Economy
   ([kennedy-2007] eq. (66)) derives a contextual standard for open scales and
   an endpoint standard for closed ones, building on the scale typology of
   [kennedy-mcnally-2005] and [rotstein-winter-2004]. A *totally closed* scale
   is interpretively variable: both endpoint standards are admitted (eq.
   (67)–(68), *opaque/transparent*, *open/exposed*), with the maximum a mere
   out-of-context pragmatic default.

2. **The relative/absolute split surfaces in comparatives.** Comparatives with
   absolute adjectives carry an entailment to the bare positive form whose
   *direction* is fixed by the standard type — minimum-standard absolutes
   (*wet*, *bent*) give a positive entailment (eq. (49)), maximum-standard
   absolutes (*dry*, *straight*) a negative one (eq. (50)) — whereas relative
   adjectives (*long*, *tall*) carry neither (eq. (51)–(52)).

3. **Scale structure licenses degree modifiers.** [kennedy-2007] eq. (61)
   (= [kennedy-mcnally-2005] eq. (15)): maximizers/proportional modifiers
   (*completely*, *half*) require an upper endpoint, minimizers/diminishers
   (*slightly*) a lower one. The `Licenses` matrix encodes this, and the
   bridges below check it against the English Fragment entries (*tall*, *full*,
   *wet*, *dry*) and the `LicensingPipeline` substrate.

## Main results

* `closed_admits_both_endpoints` — totally closed scales are interpretively
  variable.
* `minStandard_comparative_entails_positive` / `maxStandard_comparative_entails_negative`
  / `relative_comparative_not_entails_positive` — the eq. (49)–(52) asymmetry.
* `Licenses` — the eq. (61) modifier-class licensing matrix.
* `k2007_matrix_agrees_with_typology`, `k2007_modifier_data_agrees`,
  `pipeline_agrees_with_measure` — the matrix agrees with the per-adjective
  typology data and with the `DirectedMeasure` / `LicensingPipeline` substrate.
* `tall_requires_cc`, `full_no_cc` (etc.) — comparison-class sensitivity
  read off each Fragment adjective's scale structure.
-/

namespace Kennedy2007

open Degree

/-! ### Scale structure and Interpretive Economy

[kennedy-2007]'s generalisation: open scales take a contextual standard, closed
scales an endpoint standard. The content beyond the substrate's default table
is the interpretive *variability* of totally closed scales. -/

/-- Open-scale (relative) adjectives — *tall*, *expensive*, *big* — take a
contextual standard, so their interpretation requires a comparison class. -/
theorem open_requires_comparison_class :
    (interpretiveEconomy .open_).RequiresComparisonClass :=
  trivial

/-- Totally closed scales are *interpretively variable*: Interpretive Economy
admits both the minimum and the maximum endpoint standard ([kennedy-2007]
eq. (67)–(68), *opaque/transparent*, *open/exposed*). The substrate's
single-valued `interpretiveEconomy .closed = .maxEndpoint` is only the
out-of-context pragmatic default, not an IE determination. -/
theorem closed_admits_both_endpoints :
    ieAdmits .closed .minEndpoint ∧ ieAdmits .closed .maxEndpoint :=
  ⟨ieAdmits_closed_minEndpoint, ieAdmits_closed_maxEndpoint⟩

/-! ### Relative vs absolute adjectives in comparatives

[kennedy-2007] eq. (49)–(52): the standard type of an absolute adjective
surfaces as an entailment from the comparative to the bare positive form. On a
scale `D`, a *minimum-standard* absolute (*wet*) is positive iff its degree is
above the scale bottom (`PositiveStandard.minEndpoint`), a *maximum-standard*
absolute (*dry*) iff its degree is the scale top (`PositiveStandard.maxEndpoint`),
and a *relative* adjective (*long*) iff its degree exceeds a contextual
threshold (`PositiveStandard.contextual`). -/

section Entailments

variable {Entity D : Type*} [LinearOrder D]

/-- Positive form of a minimum-standard absolute adjective: `x` is *wet* iff its
degree is strictly above the scale minimum. -/
def MinStandardPos [OrderBot D] (μ : Entity → D) (x : Entity) : Prop := ⊥ < μ x

/-- Positive form of a maximum-standard absolute adjective: `x` is *dry* iff its
degree is the scale maximum. -/
def MaxStandardPos [OrderTop D] (μ : Entity → D) (x : Entity) : Prop := μ x = ⊤

/-- Positive form of a relative adjective: `x` is *long* iff its degree exceeds
the contextual threshold `θ`. -/
def RelativePos (μ : Entity → D) (θ : D) (x : Entity) : Prop := θ < μ x

/-- **Eq. (49): minimum-standard positive entailment.** "The floor is wetter
than the countertop" entails "the floor is wet": exceeding another degree puts
you strictly above the scale minimum. -/
theorem minStandard_comparative_entails_positive [OrderBot D] (μ : Entity → D)
    (a b : Entity) (h : comparativeSem μ a b .positive) : MinStandardPos μ a := by
  simp only [comparativeSem] at h
  exact bot_le.trans_lt h

/-- **Eq. (50): maximum-standard negative entailment.** "The floor is drier than
the countertop" entails "the countertop is *not* dry": being exceeded keeps you
strictly below the scale maximum. -/
theorem maxStandard_comparative_entails_negative [OrderTop D] (μ : Entity → D)
    (a b : Entity) (h : comparativeSem μ a b .positive) : ¬ MaxStandardPos μ b := by
  simp only [comparativeSem] at h
  intro hb
  rw [MaxStandardPos] at hb
  exact not_lt.mpr le_top (hb ▸ h)

end Entailments

/-! Relative adjectives carry *no* entailment from the comparative to the
positive form ([kennedy-2007] eq. (51)–(52)): "Rod A is longer than Rod B"
entails neither that A is long nor that B is not long, because the standard is
contextual. Non-entailment is witnessed by concrete `ℕ`-valued models in which
the comparative holds but the positive form goes either way. -/

/-- "Longer than" does not entail "long": a model where `a` exceeds `b` yet `a`
falls below the contextual threshold. -/
theorem relative_comparative_not_entails_positive :
    ∃ (μ : Bool → ℕ) (θ : ℕ) (a b : Bool),
      comparativeSem μ a b .positive ∧ ¬ RelativePos μ θ a := by
  refine ⟨fun x => if x then 1 else 0, 5, true, false, ?_, ?_⟩ <;>
    simp only [comparativeSem, RelativePos] <;> decide

/-- "Longer than" does not entail "not long" either: a model where `a` exceeds
`b` and is also above the threshold. Together with the previous theorem this
shows the comparative leaves a relative adjective's positive form undetermined. -/
theorem relative_comparative_not_entails_negative :
    ∃ (μ : Bool → ℕ) (θ : ℕ) (a b : Bool),
      comparativeSem μ a b .positive ∧ RelativePos μ θ a := by
  refine ⟨fun x => if x then 1 else 0, 0, true, false, ?_, ?_⟩ <;>
    simp only [comparativeSem, RelativePos] <;> decide

/-! ### Concrete entailment witnesses

The general entailments fire on the paper's scenarios, here on a 0–3 scale
(`Fin 4`, with `⊥ = 0` and `⊤ = 3`). -/

/-- Eq. (49) on a concrete wetness scale: a floor (degree 2) wetter than the
countertop (degree 1) is wet. -/
example : MinStandardPos (D := Fin 4) (fun b => if b then 2 else 1) true :=
  minStandard_comparative_entails_positive (fun b : Bool => if b then (2 : Fin 4) else 1)
    true false (by simp only [comparativeSem]; decide)

/-- Eq. (50) on a concrete dryness scale: when the floor (degree 3 = ⊤) is drier
than the countertop (degree 2), the countertop is not dry. -/
example : ¬ MaxStandardPos (D := Fin 4) (fun b => if b then 3 else 2) false :=
  maxStandard_comparative_entails_negative (fun b : Bool => if b then (3 : Fin 4) else 2)
    true false (by simp only [comparativeSem]; decide)

/-! ### Empirical data

Hand-typed stimulus tables recording [kennedy-2007]'s descriptive patterns:
comparison-class shift, antonym scales, the adjective typology, and degree
modifier compatibility. -/

/--
Empirical pattern: Scalar adjective thresholds shift with comparison class.

The same individual can be "tall" relative to one class but "not tall"
relative to another. The threshold tracks statistical properties of
the comparison class (especially mean and variance).

Examples:
- 5'10" is tall for a jockey but not tall for a basketball player
- $500,000 is expensive for Atlanta but cheap for San Francisco

Source: [kennedy-2007], [fara-2000], [lassiter-goodman-2017]
-/
structure ContextShiftDatum where
  /-- The adjective being used -/
  adjective : String
  /-- The individual/item being described -/
  individual : String
  /-- The value on the underlying scale (as string for flexibility) -/
  scaleValue : String
  /-- First comparison class -/
  comparisonClass1 : String
  /-- Second comparison class -/
  comparisonClass2 : String
  /-- Judgment in first class (true = adjective applies) -/
  judgmentInClass1 : Bool
  /-- Judgment in second class -/
  judgmentInClass2 : Bool
  deriving Repr

/-- Classic height example: 5'10" person. -/
def jockeyBasketball : ContextShiftDatum :=
  { adjective := "tall"
  , individual := "person X"
  , scaleValue := "5'10\""
  , comparisonClass1 := "jockeys"
  , comparisonClass2 := "basketball players"
  , judgmentInClass1 := true   -- tall for a jockey
  , judgmentInClass2 := false  -- not tall for a basketball player
  }

/-- House price example. -/
def atlantaSanFrancisco : ContextShiftDatum :=
  { adjective := "expensive"
  , individual := "house Y"
  , scaleValue := "$500,000"
  , comparisonClass1 := "houses in Atlanta"
  , comparisonClass2 := "houses in San Francisco"
  , judgmentInClass1 := true   -- expensive for Atlanta
  , judgmentInClass2 := false  -- not expensive for SF
  }

/-- Size example across orders of magnitude. -/
def microbePlanet : ContextShiftDatum :=
  { adjective := "big"
  , individual := "entity Z"
  , scaleValue := "10 micrometers"
  , comparisonClass1 := "microbes"
  , comparisonClass2 := "planets"
  , judgmentInClass1 := true   -- big for a microbe
  , judgmentInClass2 := false  -- definitely not big for a planet
  }

def contextShiftExamples : List ContextShiftDatum :=
  [jockeyBasketball, atlantaSanFrancisco, microbePlanet]

/--
Empirical pattern: Antonym pairs share a scale with reversed polarity.

"Tall" and "short" live on the same height scale but point in opposite
directions. This creates the "excluded middle gap" where neither applies
clearly (the borderline region).

Source: [kennedy-2007], [lassiter-goodman-2017]
-/
structure AntonymDatum where
  /-- The positive adjective -/
  positive : String
  /-- The negative adjective -/
  negative : String
  /-- The underlying scale -/
  scale : String
  /-- Contradictory (A ≡ ¬B, no gap) or contrary (can both be false, gap). -/
  negationType : Features.NegationType
  /-- Example where positive applies -/
  positiveExample : String
  /-- Example where negative applies -/
  negativeExample : String
  /-- Example where neither clearly applies -/
  neitherExample : String
  deriving Repr

def tallShortAntonym : AntonymDatum :=
  { positive := "tall"
  , negative := "short"
  , scale := "height"
  , negationType := .contrary  -- both can be false
  , positiveExample := "7-footer is tall"
  , negativeExample := "5-footer is short"
  , neitherExample := "5'9\" person is neither clearly tall nor clearly short"
  }

def expensiveCheapAntonym : AntonymDatum :=
  { positive := "expensive"
  , negative := "cheap"
  , scale := "price"
  , negationType := .contrary
  , positiveExample := "$1M house is expensive"
  , negativeExample := "$50K house is cheap"
  , neitherExample := "$400K house is neither clearly expensive nor cheap"
  }

def antonymExamples : List AntonymDatum :=
  [tallShortAntonym, expensiveCheapAntonym]

/--
Data capturing Kennedy's adjective typology predictions.

Key diagnostic: behavior with degree modifiers
- RGA: "??slightly tall", "??completely tall" (odd)
- AGA-max: "slightly bent", "completely straight" (natural)
- AGA-min: "slightly wet", "??completely wet" (asymmetric)

Source: [kennedy-2007] §3
-/
structure AdjectiveTypologyDatum where
  /-- The adjective -/
  adjective : String
  /-- Its classification -/
  classification : Degree.AdjectiveClass
  /-- The underlying scale name (e.g., "height", "fullness") -/
  scale : String
  /-- Scale structure (Kennedy 2007's 4-way typology), the canonical
      `Boundedness` enum rather than a `Bool`-pair re-encoding. -/
  scaleType : Core.Order.Boundedness
  /-- Natural with "slightly X"? -/
  naturalWithSlightly : Bool
  /-- Natural with "completely X"? -/
  naturalWithCompletely : Bool
  /-- Threshold shifts with comparison class? -/
  thresholdShifts : Bool
  deriving Repr

/-- "Tall" — prototypical relative gradable adjective; open scale. -/
def tallTypology : AdjectiveTypologyDatum :=
  { adjective := "tall"
  , classification := .relativeGradable
  , scale := "height"
  , scaleType := .open_  -- matches `Adjectival.tall.scaleType`
  , naturalWithSlightly := false  -- "??slightly tall"
  , naturalWithCompletely := false  -- "??completely tall"
  , thresholdShifts := true
  }

/-- "Full" — absolute maximum standard adjective; totally closed scale. -/
def fullTypology : AdjectiveTypologyDatum :=
  { adjective := "full"
  , classification := .absoluteMaximum
  , scale := "fullness"
  , scaleType := .closed  -- matches `Adjectival.full.scaleType`
  , naturalWithSlightly := true   -- "slightly full" (= almost full)
  , naturalWithCompletely := true -- "completely full"
  , thresholdShifts := false
  }

/-- "Wet" — absolute minimum standard adjective; lower-bounded scale. -/
def wetTypology : AdjectiveTypologyDatum :=
  { adjective := "wet"
  , classification := .absoluteMinimum
  , scale := "wetness"
  , scaleType := .lowerBounded  -- Kennedy's datum; the Fragment models this as
                                -- closed + lower pole (same absoluteMinimum class)
  , naturalWithSlightly := true  -- "slightly wet"
  , naturalWithCompletely := false  -- "??completely wet"
  , thresholdShifts := false
  }

/-- "Straight" — absolute maximum standard adjective; totally closed scale. -/
def straightTypology : AdjectiveTypologyDatum :=
  { adjective := "straight"
  , classification := .absoluteMaximum
  , scale := "straightness"
  , scaleType := .closed  -- matches `Adjectival.straight.scaleType`
  , naturalWithSlightly := true
  , naturalWithCompletely := true
  , thresholdShifts := false
  }

/-- "Bent" — absolute minimum standard adjective; lower-bounded scale. -/
def bentTypology : AdjectiveTypologyDatum :=
  { adjective := "bent"
  , classification := .absoluteMinimum
  , scale := "bentness"
  , scaleType := .lowerBounded  -- Kennedy's datum; the Fragment models this as
                                -- closed + lower pole (same absoluteMinimum class)
  , naturalWithSlightly := true   -- "slightly bent"
  , naturalWithCompletely := false -- "??completely bent" (odd)
  , thresholdShifts := false
  }

def adjectiveTypologyExamples : List AdjectiveTypologyDatum :=
  [tallTypology, fullTypology, wetTypology, straightTypology, bentTypology]

/--
The key prediction: RGAs are context-sensitive, AGAs are not.

This is testable: change comparison class, see if threshold shifts.
- "tall for a basketball player" vs "tall for a jockey" - shifts
- "wet for a desert" vs "wet for a rainforest" - does NOT shift
-/
structure RGAvsAGAPrediction where
  rgaAdjective : String
  agaAdjective : String
  rgaShifts : Bool
  agaShifts : Bool
  rgaShiftExample : String
  agaNonShiftExample : String
  deriving Repr

def rgaVsAgaPrediction : RGAvsAGAPrediction :=
  { rgaAdjective := "tall"
  , agaAdjective := "wet"
  , rgaShifts := true
  , agaShifts := false
  , rgaShiftExample := "5'10\" is tall for a jockey, not tall for a basketball player"
  , agaNonShiftExample := "A damp cloth is wet whether comparing to deserts or rainforests"
  }

/--
Degree modifiers and their interactions with adjective types.

Key modifiers:
- Proportional: "half", "completely", "partially"
- Measure phrases: "6 feet tall", "3 degrees warmer"
- Intensifiers: "very", "extremely", "incredibly"
- Diminishers: "slightly", "somewhat", "a bit"

Source: [kennedy-mcnally-2005], [burnett-2017]
-/
inductive DegreeModifierType where
  | proportional    -- half, completely, partially (require bounded scale)
  | measurePhrase   -- 6 feet tall (require dimensional scale)
  | intensifier     -- very, extremely (shift threshold up)
  | diminisher      -- slightly, somewhat (shift threshold down)
  deriving Repr, DecidableEq

/--
Data capturing degree modifier compatibility patterns.

The puzzle: Why can you say "completely full" but not "??completely tall"?

Answer: Proportional modifiers require a BOUNDED scale (endpoints).
- "Full" has a maximum → "completely full" works
- "Tall" has no maximum → "??completely tall" is odd

Source: [kennedy-mcnally-2005]
-/
structure DegreeModifierDatum where
  modifier : String
  modifierType : DegreeModifierType
  worksWithRGA : Bool
  worksWithAGAMax : Bool
  worksWithAGAMin : Bool
  goodExample : String
  badExample : String
  deriving Repr

def completelyModifier : DegreeModifierDatum :=
  { modifier := "completely"
  , modifierType := .proportional
  , worksWithRGA := false    -- "??completely tall"
  , worksWithAGAMax := true  -- "completely full/straight"
  , worksWithAGAMin := false -- "??completely wet/bent"
  , goodExample := "The glass is completely full"
  , badExample := "??John is completely tall"
  }

def slightlyModifier : DegreeModifierDatum :=
  { modifier := "slightly"
  , modifierType := .diminisher
  , worksWithRGA := false    -- "??slightly tall"
  , worksWithAGAMax := true  -- "slightly less than full" → "slightly full"
  , worksWithAGAMin := true  -- "slightly wet"
  , goodExample := "The towel is slightly wet"
  , badExample := "??John is slightly tall"
  }

def veryModifier : DegreeModifierDatum :=
  { modifier := "very"
  , modifierType := .intensifier
  , worksWithRGA := true     -- "very tall"
  , worksWithAGAMax := true  -- "very full" (though less natural)
  , worksWithAGAMin := true  -- "very wet"
  , goodExample := "John is very tall"
  , badExample := "(all combinations are acceptable)"
  }

def halfModifier : DegreeModifierDatum :=
  { modifier := "half"
  , modifierType := .proportional
  , worksWithRGA := false    -- "??half tall"
  , worksWithAGAMax := true  -- "half full"
  , worksWithAGAMin := false -- "??half wet" (no clear midpoint)
  , goodExample := "The glass is half full"
  , badExample := "??John is half tall"
  }

def degreeModifierExamples : List DegreeModifierDatum :=
  [completelyModifier, slightlyModifier, veryModifier, halfModifier]

/--
The degree modifier puzzle: Why the distribution?

Formal constraint: Proportional modifiers require a CLOSED scale.
- Closed scale: has both minimum and maximum endpoints
- Open scale: missing at least one endpoint

This explains:
- "completely full" ✓ (fullness scale: empty to full)
- "??completely tall" ✗ (height scale: 0 to... what?)

Source: [kennedy-mcnally-2005], [rotstein-winter-2004]
-/
structure ScaleClosurePuzzle where
  closedScaleAdj : String
  openScaleAdj : String
  modifier : String
  worksWithClosed : Bool
  worksWithOpen : Bool
  deriving Repr

def closurePuzzle : ScaleClosurePuzzle :=
  { closedScaleAdj := "full"
  , openScaleAdj := "tall"
  , modifier := "completely"
  , worksWithClosed := true
  , worksWithOpen := false
  }

/-! ### Modifier-class licensing matrix (eq. (61))

[kennedy-2007] eq. (61) (= [kennedy-mcnally-2005] eq. (15)) is the central
typological prediction: which scale-structure types license which modifier
classes. The matrix is the load-bearing connection between the data fields
above (`completelyModifier`/`slightlyModifier`/`halfModifier`/`veryModifier`)
and the `Boundedness` scale-structure substrate.

Per the matrix:
- **Maximizers / proportional** (*completely, perfectly, absolutely, half*)
  require an UPPER endpoint → license iff `Boundedness.HasMax`.
- **Minimizers / diminishers** (*slightly, partially, somewhat*) require a
  LOWER endpoint → license iff `Boundedness.HasMin`.
- **Intensifiers** (*very, extremely*) work on all scales (modulo pragmatic
  considerations).
- **Measure phrases** (*6 feet tall*) work on all dimensional scales
  ([hay-kennedy-levin-1999]). -/
def Licenses : DegreeModifierType → Core.Order.Boundedness → Prop
  | .proportional, b => b.HasMax
  | .diminisher, b => b.HasMin
  | .intensifier, _ => True
  | .measurePhrase, _ => True

instance : ∀ (m : DegreeModifierType) (b : Core.Order.Boundedness),
    Decidable (Licenses m b)
  | .proportional, b => inferInstanceAs (Decidable b.HasMax)
  | .diminisher, b => inferInstanceAs (Decidable b.HasMin)
  | .intensifier, _ => isTrue trivial
  | .measurePhrase, _ => isTrue trivial

/-! ### Fragment licensing bridges

Connects the abstract `adjMeasure` and `LicensingPipeline` algebra to the
concrete English Fragment entries (*tall*, *full*, *wet*, *dry*) and the
empirical data above, and verifies the per-entry typology data against the
Fragment annotations. -/

section Bridge

open Degree
open English.Predicates.Adjectival
open Core.Order

/-! #### Fragment → DirectedMeasure licensing -/

/-- "tall" (open scale) → DirectedMeasure blocks degree modification. -/
theorem tall_blocks_completely {max : Nat} {W : Type*} (μ : W → Degree max) :
    ¬ (adjMeasure μ tall).IsLicensed :=
  openAdj_blocked μ tall rfl

/-- "full" (closed scale) → DirectedMeasure licenses degree modification. -/
theorem full_licenses_completely {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ full).IsLicensed :=
  closedAdj_licensed μ full rfl

/-- "wet" (closed scale) → DirectedMeasure licenses. -/
theorem wet_licensed {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ wet).IsLicensed :=
  closedAdj_licensed μ wet rfl

/-- "dry" (closed scale) → DirectedMeasure licenses. -/
theorem dry_licensed {max : Nat} {W : Type*} (μ : W → Degree max) :
    (adjMeasure μ dry).IsLicensed :=
  closedAdj_licensed μ dry rfl

/-! #### DirectedMeasure → data bridges -/

/-- The closure puzzle is predicted by DirectedMeasure:
    closed-scale adjectives license "completely", open-scale ones don't.
    Matches `closurePuzzle.worksWithClosed` / `.worksWithOpen`. -/
theorem closurePuzzle_predicted {max : Nat} {W : Type*} (μ : W → Degree max) :
    ((adjMeasure μ full).IsLicensed ↔ closurePuzzle.worksWithClosed = true) ∧
    ((adjMeasure μ tall).IsLicensed ↔ closurePuzzle.worksWithOpen = true) :=
  ⟨iff_of_true (closedAdj_licensed μ full rfl) rfl,
   iff_of_false (openAdj_blocked μ tall rfl) (by decide)⟩

/-- "completely" works with AGA-max (closed) but not RGA (open).
    `adjMeasure` licensing matches `completelyModifier` fields. -/
theorem completely_distribution {max : Nat} {W : Type*} (μ : W → Degree max) :
    ((adjMeasure μ full).IsLicensed ↔ completelyModifier.worksWithAGAMax = true) ∧
    ((adjMeasure μ tall).IsLicensed ↔ completelyModifier.worksWithRGA = true) :=
  ⟨iff_of_true (closedAdj_licensed μ full rfl) rfl,
   iff_of_false (openAdj_blocked μ tall rfl) (by decide)⟩

/-! #### LicensingPipeline bridges -/

/-- "tall" through the universal pipeline: open_ → blocked. -/
theorem adj_pipeline_tall :
    ¬ LicensingPipeline.IsLicensed tall.scaleType := id

/-- "full" through the universal pipeline: closed → licensed. -/
theorem adj_pipeline_full :
    LicensingPipeline.IsLicensed full.scaleType := trivial

/-- "wet" through the universal pipeline: closed (endpoint) → licensed. -/
theorem adj_pipeline_wet :
    LicensingPipeline.IsLicensed wet.scaleType := trivial

/-- "dry" through the universal pipeline: closed (endpoint) → licensed. -/
theorem adj_pipeline_dry :
    LicensingPipeline.IsLicensed dry.scaleType := trivial

/-- Pipeline agrees with DirectedMeasure for all four test adjectives. -/
theorem pipeline_agrees_with_measure {max : Nat} {W : Type*} (μ : W → Degree max) :
    (LicensingPipeline.IsLicensed tall.scaleType ↔ (adjMeasure μ tall).IsLicensed) ∧
    (LicensingPipeline.IsLicensed full.scaleType ↔ (adjMeasure μ full).IsLicensed) ∧
    (LicensingPipeline.IsLicensed wet.scaleType ↔ (adjMeasure μ wet).IsLicensed) ∧
    (LicensingPipeline.IsLicensed dry.scaleType ↔ (adjMeasure μ dry).IsLicensed) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! #### Scale structure → comparison-class sensitivity

Whether an adjective's standard depends on contextual domain information is
read off its scale structure ([kennedy-2007]): `scaleType → interpretiveEconomy
→ PositiveStandard → PositiveStandard.RequiresComparisonClass`. An open scale
yields a contextual **s** (requires a comparison class); a closed scale fixes
the standard at an endpoint via Interpretive Economy.

Kennedy argues that the comparison class is descriptively real but NOT a
semantic argument of *pos*; it feeds into **s** contextually rather than as a
constituent of logical form. -/

/-- "tall": open scale ⇒ CC-dependence. -/
theorem tall_requires_cc :
    (interpretiveEconomy tall.scaleType).RequiresComparisonClass := trivial

/-- "full": maximum-standard (closed scale) ⇒ CC-independence. -/
theorem full_no_cc :
    ¬ (interpretiveEconomy full.scaleType).RequiresComparisonClass := id

/-- "wet": closed scale ⇒ endpoint standard ⇒ CC-independence. -/
theorem wet_no_cc :
    ¬ (interpretiveEconomy wet.scaleType).RequiresComparisonClass := id

/-- "dry": closed scale ⇒ endpoint standard ⇒ CC-independence. -/
theorem dry_no_cc :
    ¬ (interpretiveEconomy dry.scaleType).RequiresComparisonClass := id

/-! #### MPA classification ([beltrama-2025]) -/

/-- MPAs are the mildly-positive class: an open `.value` scale carrying a
    functional (necessity) standard via `standardOverride`. Their special status
    is the standard, not scale boundedness — so on scale shape they pattern with
    the relative adjectives (not endpoint-licensed), and their resistance to
    *very*/*extremely* is pragmatic (conflicts with the middling inference). -/
theorem mpa_mildly_positive :
    decent.adjectiveClass = .mildlyPositive ∧
    acceptable.adjectiveClass = .mildlyPositive ∧
    adequate.adjectiveClass = .mildlyPositive := ⟨rfl, rfl, rfl⟩

/-- MPAs and *good* share scale-structure licensing status: both sit on the open
    `.value` scale, so neither is endpoint-licensed. Their difference is in
    standard type (functional vs contextual), not in structural licensing. -/
theorem mpa_good_same_licensing :
    LicensingPipeline.IsLicensed decent.scaleType ↔
    LicensingPipeline.IsLicensed good.scaleType := Iff.rfl

/-- IE path diverges for MPAs: the open-scale shape-default is a *contextual*
    standard (`interpretiveEconomy .open_`), yet MPAs actually receive a
    *functional* standard via `standardOverride`. A genuine exception to
    Interpretive Economy, distinct from *good*'s (which keeps the contextual
    default). -/
theorem mpa_ie_exception :
    interpretiveEconomy decent.scaleType = .contextual ∧
    decent.standard = .functional := ⟨rfl, rfl⟩

/-! #### Modifier-class matrix consistency (eq. (61)) -/

/-- The `Licenses` matrix agrees with the per-adjective typology data in
    `adjectiveTypologyExamples`: for each of the 5 adjectives spanning the 4-way
    `Boundedness` typology, the matrix predicts `naturalWithSlightly` from
    `Licenses .diminisher` and `naturalWithCompletely` from
    `Licenses .proportional`. -/
theorem k2007_matrix_agrees_with_typology :
    ∀ d ∈ adjectiveTypologyExamples,
      (Licenses .diminisher d.scaleType ↔ d.naturalWithSlightly = true) ∧
      (Licenses .proportional d.scaleType ↔ d.naturalWithCompletely = true) := by
  decide

/-- Per-modifier consistency: each `DegreeModifierDatum`'s
    `worksWithRGA` / `worksWithAGAMax` / `worksWithAGAMin` fields agree with
    `Licenses` on the corresponding `Boundedness` cases. The AGA-max cases are
    read at the canonical totally-closed scale (`.closed`, e.g. *full*). -/
theorem k2007_modifier_data_agrees :
    ∀ d ∈ degreeModifierExamples,
      (Licenses d.modifierType .closed ↔ d.worksWithAGAMax = true) ∧
      (Licenses d.modifierType .lowerBounded ↔ d.worksWithAGAMin = true) ∧
      (Licenses d.modifierType .open_ ↔ d.worksWithRGA = true) := by
  decide

/-- `closurePuzzle` (full vs tall, *completely*) is a direct corollary of the
    matrix: `Licenses .proportional .closed = true` matches `worksWithClosed`,
    and `Licenses .proportional .open_ = false` matches `worksWithOpen`. -/
theorem closurePuzzle_via_matrix :
    (Licenses .proportional .closed ↔ closurePuzzle.worksWithClosed = true) ∧
    (Licenses .proportional .open_ ↔ closurePuzzle.worksWithOpen = true) := by
  decide

/-! #### Per-entry typology consistency

For each adjective with both a typology datum above and a Fragment entry, verify
form match, scale-type consistency, and licensing/threshold agreement. -/

/-- "tall" typology datum matches Fragment form. -/
theorem tall_form_match : tallTypology.adjective = tall.form := rfl

/-- "full" typology datum matches Fragment form. -/
theorem full_form_match : fullTypology.adjective = full.form := rfl

/-- "wet" typology datum matches Fragment form. -/
theorem wet_form_match : wetTypology.adjective = wet.form := rfl

/-- "tall" (open): Data scaleType matches Fragment scaleType. -/
theorem tall_scaleType_consistency :
    tallTypology.scaleType = tall.scaleType := rfl

/-- "full" (closed): Data scaleType matches Fragment scaleType. -/
theorem full_scaleType_consistency :
    fullTypology.scaleType = full.scaleType := rfl

/-- "wet": Fragment's derived Kennedy class matches the paper typology datum.
    The raw `Boundedness` labels now differ — the Fragment models wetness as one
    closed scale with `wet` at the lower pole, where Kennedy's datum labels it
    lower-bounded — but both yield the same absolute-minimum class. -/
theorem wet_class_consistency :
    wet.adjectiveClass = wetTypology.classification := rfl

/-- "straight" (closed): Data scaleType matches Fragment scaleType. -/
theorem straight_scaleType_consistency :
    straightTypology.scaleType = straight.scaleType := rfl

/-- "bent": Fragment's derived Kennedy class matches the paper typology datum
    (closed + lower pole vs Kennedy's lower-bounded label; same absolute-minimum
    class). -/
theorem bent_class_consistency :
    bent.adjectiveClass = bentTypology.classification := rfl

/-- "tall" (open scale): pipeline blocked = "completely" doesn't work with RGA. -/
theorem tall_completely_agrees :
    LicensingPipeline.IsLicensed tall.scaleType ↔
    completelyModifier.worksWithRGA = true := by decide

/-- "full" (closed scale): pipeline licensed = "completely" works with AGA-max. -/
theorem full_completely_agrees :
    LicensingPipeline.IsLicensed full.scaleType ↔
    completelyModifier.worksWithAGAMax = true := by decide

/-- "tall": typology's naturalWithCompletely matches pipeline prediction. -/
theorem tall_completely_from_pipeline :
    tallTypology.naturalWithCompletely = true ↔
    LicensingPipeline.IsLicensed tall.scaleType := by decide

/-- "full": typology's naturalWithCompletely matches pipeline prediction. -/
theorem full_completely_from_pipeline :
    fullTypology.naturalWithCompletely = true ↔
    LicensingPipeline.IsLicensed full.scaleType := by decide

/-- "tall" (open): threshold shifts with comparison class. -/
theorem tall_threshold_shifts :
    tallTypology.thresholdShifts = true ∧ tall.scaleType = .open_ :=
  ⟨rfl, rfl⟩

/-- "full" (closed): threshold does NOT shift. -/
theorem full_threshold_stable :
    fullTypology.thresholdShifts = false ∧ full.scaleType = .closed :=
  ⟨rfl, rfl⟩

end Bridge

end Kennedy2007
