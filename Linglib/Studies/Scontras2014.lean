import Linglib.Semantics.Degree.Measurement.Basic
import Linglib.Fragments.English.MeasurePhrases

/-!
# [scontras-2014] — The Semantics of Measurement
[chierchia-1998] [krifka-1989] [scontras-2014] [zabbal-2005]

Empirical observations and bridge theorems for Scontras's quantizing noun
typology (Ch. 3).

## Key Empirical Claim

The three classes of quantizing nouns differ systematically in whether they
license a MEASURE reading (Scontras Ch. 3, Table 3.5 p. 89). The MEASURE
reading is the one in which a quantizing noun functions as a unit-name for
the substance, rather than denoting the substance's containers or atoms.

- **Measure terms** (kilo, liter): ALWAYS license MEASURE.
  "Three kilos of rice" is necessarily a 3-kilo quantity of rice.

- **Container nouns** (glass, box): AMBIGUOUS.
  - CONTAINER reading (default): "three glasses of water in the cupboard" —
    three individual glass-objects.
  - MEASURE reading (forced by recipe context, etc.): "add three glasses of
    water" — a quantity of water equal to three glass-volumes.

- **Atomizers** (grain, piece): NEVER license MEASURE.
  Atomizers' semantics is inherently relational and partitioning
  (Scontras eqs. (77), (87), pp. 89-90): they take a substance noun
  and impose a partition into self-connected atoms via π. They are
  then *counted* by CARD over the partition (Scontras p. 100).
  The atoms-after-partition predicate IS quantity-uniform under μ_CARD —
  atomizers fail MEASURE-licensing because their semantics is relational
  / partitioning rather than measure-naming, not because the resulting
  predicate is non-uniform under every conceivable μ.

## Diagnostics for the MEASURE/CONTAINER ambiguity

Container nouns can be disambiguated:

- **Locative "in X"**: "three glasses of water in the pitcher" → CONTAINER
- **Recipe context**: "three glasses of water in the recipe" → MEASURE
- **Demonstratives**: "those three glasses" → CONTAINER (individuated)

## Architecture

This file encodes empirical observations and proves that
the Fragment entries (class assignments) correctly predict the Theory's
MEASURE-reading licensing.

Dependency chain:
  Theory (`licensesMeasureReading`) → Fragment (`QuantizingNounEntry.nounClass`)
    → Studies (this file)

-/

namespace Scontras2014

open Semantics.Measurement
  (QuantizingNounClass ContainerReading licensesMeasureReading)
open English.MeasurePhrases

-- ============================================================================
-- § 1. Empirical Observations: MEASURE Licensing
-- ============================================================================

/-- An observed MEASURE-licensing judgment for a quantizing noun in a
specific context. -/
structure MeasureObservation where
  /-- The quantizing noun being tested. -/
  noun : QuantizingNounEntry
  /-- The mass noun complement (e.g., "rice", "water"). -/
  complement : String
  /-- Which reading is active (for container nouns). -/
  reading : Option ContainerReading
  /-- The test sentence. -/
  sentence : String
  /-- Observed: does the phrase license a MEASURE-quantity reading? -/
  licensesMeasure : Bool
  deriving Repr, BEq

-- Measure terms: always MEASURE

/-- "Three kilos of rice" — a measure of rice. -/
def obs_kilo_rice : MeasureObservation where
  noun := { form := "kilo", formPlural := "kilos",
            nounClass := .measureTerm, measureDimension := some .mass }
  complement := "rice"
  reading := none
  sentence := "Three kilos of rice (a 3-kilo quantity)"
  licensesMeasure := true

def obs_liter_water : MeasureObservation where
  noun := { form := "liter", formPlural := "liters",
            nounClass := .measureTerm, measureDimension := some .volume }
  complement := "water"
  reading := none
  sentence := "Three liters of water (a 3-liter quantity)"
  licensesMeasure := true

-- Container nouns, CONTAINER reading: NOT MEASURE

/-- "Three glasses of water in the cupboard" — three individual glass-objects.
The CONTAINER reading is forced by the locative; MEASURE is unavailable. -/
def obs_glass_water_container : MeasureObservation where
  noun := glass
  complement := "water"
  reading := some .container
  sentence := "Three glasses of water in the cupboard (CONTAINER, not MEASURE)"
  licensesMeasure := false

def obs_box_books_container : MeasureObservation where
  noun := box
  complement := "books"
  reading := some .container
  sentence := "Three boxes of books on the shelf (CONTAINER, not MEASURE)"
  licensesMeasure := false

-- Container nouns, MEASURE reading: IS MEASURE

/-- "Add three glasses of water" — a 3-glass-volume quantity of water.
The MEASURE reading is forced by the recipe context. -/
def obs_glass_water_measure : MeasureObservation where
  noun := glass
  complement := "water"
  reading := some .measure
  sentence := "Add three glasses of water to the recipe (MEASURE)"
  licensesMeasure := true

def obs_cup_flour_measure : MeasureObservation where
  noun := cup
  complement := "flour"
  reading := some .measure
  sentence := "Three cups of flour, doubled to six (MEASURE)"
  licensesMeasure := true

-- Atomizers: NOT MEASURE (counted by CARD instead)

/-- "Three grains of rice" — three rice-grain individuals.
Atomizers' semantics is inherently relational and partitioning
(Scontras eqs. (77), (87), pp. 89-90): grain takes the substance noun rice
and imposes a partition into self-connected rice-atoms via π. The atoms
are then counted by CARD (Scontras p. 100). MEASURE-reading fails because
the semantics is partitioning rather than measure-naming. -/
def obs_grain_rice : MeasureObservation where
  noun := grain
  complement := "rice"
  reading := none
  sentence := "Three grains of rice (counted via CARD over π(rice); atomizers are relational/partitioning, not measure-naming)"
  licensesMeasure := false

def obs_drop_water : MeasureObservation where
  noun := drop
  complement := "water"
  reading := none
  sentence := "Three drops of water (counted via CARD over π(water); atomizers are relational/partitioning, not measure-naming)"
  licensesMeasure := false

def obs_piece_cake : MeasureObservation where
  noun := piece
  complement := "cake"
  reading := none
  sentence := "Three pieces of cake (counted via CARD over π(cake); atomizers are relational/partitioning, not measure-naming)"
  licensesMeasure := false

def allObservations : List MeasureObservation :=
  [ obs_kilo_rice, obs_liter_water
  , obs_glass_water_container, obs_box_books_container
  , obs_glass_water_measure, obs_cup_flour_measure
  , obs_grain_rice, obs_drop_water, obs_piece_cake ]

-- ============================================================================
-- § 2. Bridge Theorems: Fragment Class Predicts Observed MEASURE Licensing
-- ============================================================================

/-! ### The central bridge

The Fragment assigns each noun a `nounClass` (from the Theory's
`QuantizingNounClass`). The Theory defines `licensesMeasureReading` mapping
class + reading to a MEASURE-licensing prediction (Scontras Table 3.5 p. 89).
We prove that this prediction matches the empirical observation for EVERY
example in our data.

This is the payoff of the Theories → Fragments → Studies architecture: if
someone changes a noun's class assignment in the Fragment, or changes the
`licensesMeasureReading` function in the Theory, the bridge theorems break. -/

/-- The Theory's MEASURE-licensing prediction matches the empirical
observation for every example in our data set. -/
theorem theory_predicts_observations :
    ∀ obs ∈ allObservations,
      licensesMeasureReading obs.noun.nounClass obs.reading ↔ obs.licensesMeasure = true := by
  simp [allObservations]; decide

/-- For measure term observations: the Theory predicts MEASURE = true. -/
theorem measureTerm_observations_licenseMeasure :
    ∀ obs ∈ allObservations, obs.noun.nounClass = .measureTerm →
      obs.licensesMeasure = true := by
  simp [allObservations]; decide

/-- For atomizer observations: the Theory predicts MEASURE = false
(atomizers are counted by CARD, not measured). -/
theorem atomizer_observations_no_MEASURE :
    ∀ obs ∈ allObservations, obs.noun.nounClass = .atomizer →
      obs.licensesMeasure = false := by
  simp [allObservations]; decide

/-- For container noun observations: MEASURE-licensing depends on the reading.
CONTAINER → not MEASURE; MEASURE → MEASURE. -/
theorem container_MEASURE_depends_on_reading :
    ∀ obs ∈ allObservations, obs.noun.nounClass = .containerNoun →
      (obs.licensesMeasure = true ↔ obs.reading = some .measure) := by
  simp [allObservations]; decide

-- ============================================================================
-- § 3. Bridge: Fragment Entry Class = Observation Class
-- ============================================================================

/-! ### Fragment consistency

We also verify that the Fragment entries used in our observations have
the same class assignment as the observations themselves. This catches
the case where someone defines `glass.nounClass :=.atomizer` in the
Fragment but uses `.containerNoun` in the observation. -/

/-- The Fragment's `glass` entry matches the observation's class. -/
theorem glass_class_consistent :
    glass.nounClass = obs_glass_water_container.noun.nounClass ∧
    glass.nounClass = obs_glass_water_measure.noun.nounClass := ⟨rfl, rfl⟩

/-- The Fragment's `grain` entry matches the observation's class. -/
theorem grain_class_consistent :
    grain.nounClass = obs_grain_rice.noun.nounClass := rfl

/-- The Fragment's `drop` entry matches the observation's class. -/
theorem drop_class_consistent :
    drop.nounClass = obs_drop_water.noun.nounClass := rfl

-- ============================================================================
-- § 4. Disambiguation Context Predictions
-- ============================================================================

/-- Disambiguation contexts for container nouns (Scontras Ch. 3 §3.2.1).

A sentence context can force one reading of an ambiguous container noun:
- Locative PPs ("in the cupboard") → CONTAINER (the physical objects are located)
- Recipe/instruction context → MEASURE (amount of substance)
- Demonstratives ("those three glasses") → CONTAINER (individuated)
- Generic quantity context ("add three glasses") → MEASURE -/
structure DisambiguationContext where
  /-- The noun being disambiguated. -/
  noun : QuantizingNounEntry
  /-- Context type. -/
  contextType : String
  /-- Example sentence. -/
  sentence : String
  /-- Which reading the context forces. -/
  forcedReading : ContainerReading
  deriving Repr, BEq

def disamb_glass_locative : DisambiguationContext where
  noun := glass
  contextType := "locative PP"
  sentence := "Three glasses of water are in the cupboard"
  forcedReading := .container

def disamb_glass_recipe : DisambiguationContext where
  noun := glass
  contextType := "recipe/instruction"
  sentence := "Add three glasses of water to the mixture"
  forcedReading := .measure

def disamb_box_demonstrative : DisambiguationContext where
  noun := box
  contextType := "demonstrative"
  sentence := "Those three boxes of books are heavy"
  forcedReading := .container

def disamb_cup_recipe : DisambiguationContext where
  noun := cup
  contextType := "recipe/instruction"
  sentence := "Use three cups of flour for the dough"
  forcedReading := .measure

def allDisambiguations : List DisambiguationContext :=
  [disamb_glass_locative, disamb_glass_recipe,
   disamb_box_demonstrative, disamb_cup_recipe]

/-- All disambiguation contexts involve container nouns (not measure terms
or atomizers — only container nouns are ambiguous). -/
theorem disambiguations_only_containers :
    ∀ d ∈ allDisambiguations, d.noun.nounClass = .containerNoun := by
  simp [allDisambiguations]; decide

/-- Locative/demonstrative contexts force CONTAINER; recipe contexts force MEASURE. -/
theorem locative_forces_container :
    disamb_glass_locative.forcedReading = .container ∧
    disamb_box_demonstrative.forcedReading = .container := ⟨rfl, rfl⟩

theorem recipe_forces_measure :
    disamb_glass_recipe.forcedReading = .measure ∧
    disamb_cup_recipe.forcedReading = .measure := ⟨rfl, rfl⟩

/-- Combining disambiguation with the licensing prediction:
recipe contexts yield MEASURE, locative contexts yield non-MEASURE. -/
theorem recipe_context_yields_MEASURE :
    ∀ d ∈ allDisambiguations, d.forcedReading = .measure →
      licensesMeasureReading d.noun.nounClass (some d.forcedReading) := by
  simp [allDisambiguations]; decide

theorem locative_context_yields_no_MEASURE :
    ∀ d ∈ allDisambiguations, d.forcedReading = .container →
      ¬ licensesMeasureReading d.noun.nounClass (some d.forcedReading) := by
  simp [allDisambiguations]; decide

end Scontras2014
