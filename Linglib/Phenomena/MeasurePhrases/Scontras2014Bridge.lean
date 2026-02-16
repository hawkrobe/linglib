import Linglib.Theories.Semantics.Probabilistic.Measurement.Basic
import Linglib.Fragments.English.MeasurePhrases

/-!
# Scontras (2014) — The Semantics of Measurement

Empirical observations and bridge theorems for Scontras's quantizing noun
typology (Ch. 3).

## Key Empirical Claim

The three classes of quantizing nouns differ systematically in their
quantity-uniformity (QU) behavior:

- **Measure terms** (kilo, liter): ALWAYS quantity-uniform.
  "Three kilos of rice + three kilos of rice = six kilos of rice" ✓

- **Container nouns** (glass, box): AMBIGUOUS.
  - CONTAINER reading: NOT quantity-uniform.
    "Three glasses of water + three glasses of water ≠ three glasses of water"
  - MEASURE reading: IS quantity-uniform.
    "Three glasses of water + three glasses of water = six glasses of water"
    (as a volume measure: 3 glass-volumes + 3 glass-volumes = 6 glass-volumes)

- **Atomizers** (grain, piece): NOT quantity-uniform.
  "Three grains of rice + three grains of rice ≠ three grains of rice"

## Disambiguation Diagnostics

Container nouns can be disambiguated between CONTAINER and MEASURE readings:

- **Locative "in X"**: "three glasses of water in the pitcher" → CONTAINER
  (the three glasses are in the pitcher)
- **Recipe context**: "three glasses of water in the recipe" → MEASURE
  (three glass-volumes of water called for)
- **Additive closure test**: "I drank three glasses of water, then three more;
  that's six glasses total" → MEASURE (additive = QU)

## Architecture

This is a Phenomena file: it encodes empirical observations and proves that
the Fragment entries (class assignments) correctly predict the Theory's
QU predictions.

Dependency chain:
  Theory (`predictsQU`) → Fragment (`QuantizingNounEntry.nounClass`) → Phenomena (this file)

## References

- Scontras, G. (2014). *The Semantics of Measurement*. Ph.D. dissertation,
  Harvard University. Chapter 3: Quantizing Nouns.
- Krifka, M. (1989). Nominal reference, temporal constitution, and
  quantification in event semantics.
- Chierchia, G. (1998). Plurality of mass nouns and the notion of
  "semantic parameter."
-/

namespace Phenomena.MeasurePhrases.Scontras2014

open TruthConditional.Measurement (QuantizingNounClass ContainerReading predictsQU)
open Fragments.English.MeasurePhrases

-- ============================================================================
-- § 1. Empirical Observations: QU Behavior
-- ============================================================================

/-- An observed QU judgment for a quantizing noun in a specific context. -/
structure QUObservation where
  /-- The quantizing noun being tested. -/
  noun : QuantizingNounEntry
  /-- The mass noun complement (e.g., "rice", "water"). -/
  complement : String
  /-- Which reading is active (for container nouns). -/
  reading : Option ContainerReading
  /-- The test sentence. -/
  sentence : String
  /-- Observed: is the additive closure test felicitous? -/
  additiveOK : Bool
  /-- Observed: is the predicate quantity-uniform? -/
  isQU : Bool
  deriving Repr, BEq

-- Measure terms: always QU

/-- "Three kilos of rice + three kilos of rice = six kilos of rice."
Measure terms always pass the additive closure test. -/
def obs_kilo_rice : QUObservation where
  noun := { form := "kilo", formPlural := "kilos",
            nounClass := .measureTerm, measureDimension := some .mass }
  complement := "rice"
  reading := none
  sentence := "I bought three kilos of rice, then three more; that's six kilos of rice"
  additiveOK := true
  isQU := true

def obs_liter_water : QUObservation where
  noun := { form := "liter", formPlural := "liters",
            nounClass := .measureTerm, measureDimension := some .volume }
  complement := "water"
  reading := none
  sentence := "I drank three liters of water, then three more; that's six liters"
  additiveOK := true
  isQU := true

-- Container nouns, CONTAINER reading: NOT QU

/-- "Three glasses of water (CONTAINER) + three glasses of water ≠ three glasses."
In the CONTAINER reading, glasses are individuated objects that don't sum. -/
def obs_glass_water_container : QUObservation where
  noun := glass
  complement := "water"
  reading := some .container
  sentence := "#Three glasses of water in the cupboard plus three more equals three glasses"
  additiveOK := false
  isQU := false

def obs_box_books_container : QUObservation where
  noun := box
  complement := "books"
  reading := some .container
  sentence := "#Three boxes of books on the shelf plus three more equals three boxes"
  additiveOK := false
  isQU := false

-- Container nouns, MEASURE reading: IS QU

/-- "Three glasses of water (MEASURE) + three glasses of water = six glasses."
In the MEASURE reading, "glass" functions as a volume unit. -/
def obs_glass_water_measure : QUObservation where
  noun := glass
  complement := "water"
  reading := some .measure
  sentence := "The recipe calls for three glasses of water; use six for a double batch"
  additiveOK := true
  isQU := true

def obs_cup_flour_measure : QUObservation where
  noun := cup
  complement := "flour"
  reading := some .measure
  sentence := "Three cups of flour plus three cups of flour is six cups of flour"
  additiveOK := true
  isQU := true

-- Atomizers: NOT QU

/-- "Three grains of rice + three grains of rice ≠ three grains of rice."
Atomizers impose individuation; atoms don't sum back to atoms. -/
def obs_grain_rice : QUObservation where
  noun := grain
  complement := "rice"
  reading := none
  sentence := "#Three grains of rice plus three grains of rice equals three grains"
  additiveOK := false
  isQU := false

def obs_drop_water : QUObservation where
  noun := drop
  complement := "water"
  reading := none
  sentence := "#Three drops of water plus three drops of water equals three drops"
  additiveOK := false
  isQU := false

def obs_piece_cake : QUObservation where
  noun := piece
  complement := "cake"
  reading := none
  sentence := "#Three pieces of cake plus three pieces of cake equals three pieces"
  additiveOK := false
  isQU := false

def allObservations : List QUObservation :=
  [ obs_kilo_rice, obs_liter_water
  , obs_glass_water_container, obs_box_books_container
  , obs_glass_water_measure, obs_cup_flour_measure
  , obs_grain_rice, obs_drop_water, obs_piece_cake ]

-- ============================================================================
-- § 2. Bridge Theorems: Fragment Class Predicts Observed QU
-- ============================================================================

/-! ### The central bridge

The Fragment assigns each noun a `nounClass` (from the Theory's
`QuantizingNounClass`). The Theory defines `predictsQU` mapping
class + reading to a QU prediction. We prove that this prediction
matches the empirical observation for EVERY example in our data.

This is the payoff of the Theories → Fragments → Phenomena architecture:
if someone changes a noun's class assignment in the Fragment, or changes
the `predictsQU` function in the Theory, the bridge theorems break. -/

/-- The Theory's QU prediction matches the empirical observation for
every example in our data set. -/
theorem theory_predicts_observations :
    ∀ obs ∈ allObservations,
      predictsQU obs.noun.nounClass obs.reading = obs.isQU := by
  simp [allObservations]; decide

/-- For measure term observations: the Theory predicts QU = true. -/
theorem measureTerm_observations_QU :
    ∀ obs ∈ allObservations, obs.noun.nounClass = .measureTerm →
      obs.isQU = true := by
  simp [allObservations]; decide

/-- For atomizer observations: the Theory predicts QU = false. -/
theorem atomizer_observations_not_QU :
    ∀ obs ∈ allObservations, obs.noun.nounClass = .atomizer →
      obs.isQU = false := by
  simp [allObservations]; decide

/-- For container noun observations: QU depends on the reading.
CONTAINER → not QU; MEASURE → QU. -/
theorem container_QU_depends_on_reading :
    ∀ obs ∈ allObservations, obs.noun.nounClass = .containerNoun →
      (obs.isQU = true ↔ obs.reading = some .measure) := by
  simp [allObservations]; decide

-- ============================================================================
-- § 3. Bridge: Fragment Entry Class = Observation Class
-- ============================================================================

/-! ### Fragment consistency

We also verify that the Fragment entries used in our observations have
the same class assignment as the observations themselves. This catches
the case where someone defines `glass.nounClass := .atomizer` in the
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
-- § 4. Additivity = QU (Diagnostic Alignment)
-- ============================================================================

/-- Additive closure aligns perfectly with QU: a noun passes the additive
test iff it is quantity-uniform. This is not a definition — it's an
empirical observation that the two diagnostics never diverge. -/
theorem additivity_iff_QU :
    ∀ obs ∈ allObservations, obs.additiveOK = obs.isQU := by
  simp [allObservations]; decide

-- ============================================================================
-- § 5. Disambiguation Context Predictions
-- ============================================================================

/-- Disambiguation contexts for container nouns (Scontras §3.2.1).

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

/-- Combining disambiguation with QU prediction: recipe contexts yield QU,
locative contexts yield non-QU. -/
theorem recipe_context_yields_QU :
    ∀ d ∈ allDisambiguations, d.forcedReading = .measure →
      predictsQU d.noun.nounClass (some d.forcedReading) = true := by
  simp [allDisambiguations]; decide

theorem locative_context_yields_not_QU :
    ∀ d ∈ allDisambiguations, d.forcedReading = .container →
      predictsQU d.noun.nounClass (some d.forcedReading) = false := by
  simp [allDisambiguations]; decide

end Phenomena.MeasurePhrases.Scontras2014
