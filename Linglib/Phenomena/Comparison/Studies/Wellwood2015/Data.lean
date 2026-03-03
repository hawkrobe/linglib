import Linglib.Theories.Semantics.Lexical.Measurement
import Linglib.Theories.Semantics.Events.ThematicRoles

/-!
# @cite{wellwood-2015}: Empirical Data

@cite{wellwood-2015}

Theory-neutral empirical data from @cite{wellwood-2015} on the distribution
of `much`/`many` and dimensional restrictions in comparatives across
nominal, verbal, and adjectival domains.

## Data Sources

- §2.1: Nominal comparatives (mass vs count nouns)
- §2.2: Verbal comparatives (atelic vs telic VPs)
- §3.1–3.2: Adjectival comparatives (gradable vs non-gradable adjectives)
- §3.3: Morphosyntactic evidence (`more` = `much` + `-er`, @cite{bresnan-1973})
- §3.4: Dimensional restriction patterns
- §5: Number morphology and measurement (grammar shifts measurement)

-/

namespace Phenomena.Comparison.Wellwood2015

-- ════════════════════════════════════════════════════
-- § 1. Lexical Category
-- ════════════════════════════════════════════════════

/-- Lexical categories relevant to Wellwood's cross-categorial analysis. -/
inductive LexCat where
  | massNoun       -- coffee, rock, gold
  | countNoun      -- cup, idea
  | atelicVP       -- ran, slept, ran in the park
  | telicVP        -- ran to the park, graduated high school
  | gradableAdj    -- hot, tall, heavy
  | nonGradableAdj -- wooden, triangular
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Felicity with `much`/`more` (§2.1, §2.2, §3.1–3.2)
-- ════════════════════════════════════════════════════

/-- Observed felicity of `much`/`more` with different lexical categories.

    Mass nouns and atelic VPs are felicitous with `much` and allow multiple
    measurement dimensions. Count nouns and telic VPs are anomalous.
    GAs are felicitous but lexically fix a single dimension.
    Non-GAs are anomalous (not comparable).

    Examples from the paper:
    - "Al bought more coffee than Bill did." ✓ (VOLUME or WEIGHT)
    - "? Al has more idea than Bill does." ✗
    - "Al ran more than Bill did." ✓ (DURATION or DISTANCE)
    - "? Al graduated high school more than Bill did." ✗
    - "Al's coffee is hotter than Bill's." ✓ (TEMPERATURE)
    - "? This table is more wooden than that one." ✗ -/
structure MuchFelicityDatum where
  category : LexCat
  /-- Is `much`/`more` felicitous with this category? -/
  felicitousWithMuch : Bool
  /-- Does this category allow multiple measurement dimensions? -/
  multipleDimensions : Bool
  deriving DecidableEq, BEq, Repr

def massNounDatum : MuchFelicityDatum :=
  { category := .massNoun, felicitousWithMuch := true, multipleDimensions := true }

def countNounDatum : MuchFelicityDatum :=
  { category := .countNoun, felicitousWithMuch := false, multipleDimensions := false }

def atelicVPDatum : MuchFelicityDatum :=
  { category := .atelicVP, felicitousWithMuch := true, multipleDimensions := true }

def telicVPDatum : MuchFelicityDatum :=
  { category := .telicVP, felicitousWithMuch := false, multipleDimensions := false }

def gradableAdjDatum : MuchFelicityDatum :=
  { category := .gradableAdj, felicitousWithMuch := true, multipleDimensions := false }

def nonGradableAdjDatum : MuchFelicityDatum :=
  { category := .nonGradableAdj, felicitousWithMuch := false, multipleDimensions := false }

-- ════════════════════════════════════════════════════
-- § 3. Grammar Shifts Measurement (§5)
-- ════════════════════════════════════════════════════

/-- Number morphology and telicity shifts affect available dimensions
    (Wellwood §5, p. 91–93).

    (104) a. "Al found more rock than Bill did." (WEIGHT, VOLUME, *NUMBER)
          b. "Al found more rocks than Bill did." (*WEIGHT, *VOLUME, NUMBER)

    (105) a. "Al ran in the park more than Bill did." (DIST, DUR, NUMBER)
          b. "Al ran to the park more than Bill did." (*DIST, *DUR, NUMBER)

    Shifting from mass → count (plural morpheme) or atelic → telic
    restricts measurement to NUMBER, blocking extensive dimensions. -/
structure GrammarShiftDatum where
  baseForm : String
  shiftedForm : String
  /-- Base form allows extensive dimensions (WEIGHT, VOLUME, DURATION, etc.)? -/
  baseExtensive : Bool
  /-- Shifted form allows extensive dimensions? -/
  shiftedExtensive : Bool
  deriving Repr

/-- Ex. 104: mass → count via plural morpheme. -/
def rockShift : GrammarShiftDatum :=
  { baseForm := "more rock"
  , shiftedForm := "more rocks"
  , baseExtensive := true
  , shiftedExtensive := false }

/-- Ex. 105: atelic → telic via directional PP. -/
def runShift : GrammarShiftDatum :=
  { baseForm := "ran in the park more"
  , shiftedForm := "ran to the park more"
  , baseExtensive := true
  , shiftedExtensive := false }

-- ════════════════════════════════════════════════════
-- § 4. Cross-Categorial Parallel (§2–3)
-- ════════════════════════════════════════════════════

/-- The three CUM-like categories form a natural class (all measurable
    by `much`), and the three QUA-like categories form a natural class
    (none measurable by `much`):

    CUM class: mass nouns, atelic VPs, gradable adjectives
    QUA class: count nouns, telic VPs, non-gradable adjectives

    This parallel is Wellwood's central empirical claim (§2–3). -/
structure CrossCategorialParallel where
  /-- Mass nouns and atelic VPs behave alike (both measurable) -/
  massNoun_atelicVP_parallel : Bool
  /-- Count nouns and telic VPs behave alike (both not measurable) -/
  countNoun_telicVP_parallel : Bool
  /-- Gradable adjectives pattern with the measurable class -/
  gradableAdj_patterns_with_measurable : Bool
  /-- Non-gradable adjectives pattern with the non-measurable class -/
  nonGradableAdj_patterns_with_nonmeasurable : Bool
  deriving DecidableEq, BEq, Repr

def crossCategorialData : CrossCategorialParallel :=
  { massNoun_atelicVP_parallel := true
  , countNoun_telicVP_parallel := true
  , gradableAdj_patterns_with_measurable := true
  , nonGradableAdj_patterns_with_nonmeasurable := true }

-- ════════════════════════════════════════════════════
-- § 5. `much`/`many` Distribution (§3.3)
-- ════════════════════════════════════════════════════

/-- @cite{bresnan-1973}: `more` = `much` + `-er` (§3.3, p. 82–84).

    (70) a. as much soup b. too much soup c. so much soup
         d. that much soup e. *more much soup

    `much` occurs with CUM-like predicates (mass nouns, atelic VPs).
    `many` is a suppletive variant of `much` for count/QUA domains
    (@cite{wellwood-2014}, fn. 11). -/
structure MuchManyDistribution where
  /-- `much` occurs with CUM-like predicates -/
  much_with_cum : Bool
  /-- `many` occurs with QUA-like predicates -/
  many_with_qua : Bool
  deriving DecidableEq, BEq, Repr

def muchManyData : MuchManyDistribution :=
  { much_with_cum := true
  , many_with_qua := true }

-- ════════════════════════════════════════════════════
-- § 6. Measured Domain (§3.4)
-- ════════════════════════════════════════════════════

/-- What is actually measured in a comparative — the ontological domain
    whose mereological structure determines available dimensions.

    Wellwood's key §3.4 insight: dimension type (intensive vs extensive)
    tracks the measured domain, not lexical category. GAs like `hot` and
    `hard` measure states (intensive), while GAs like `full` and `heavy`
    measure entities (extensive). Nouns like `heat` and `firmness` measure
    states (intensive), while `coffee` and `plastic` measure entities
    (extensive). -/
inductive MeasuredDomain where
  | entity  -- physical objects (coffee, plastic, glass)
  | event   -- events/processes (driving, singing)
  | state   -- states (heat, hardness, speed, loudness)
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 7. Dimension Reversal Data (§3.4)
-- ════════════════════════════════════════════════════

/-- Dimension reversal datum: a comparative form paired with its
    lexical category, available dimension, and what's actually measured.

    The key empirical claim (§3.4, p. 85–87): changing the expression
    changes the measured domain, and available dimensions follow from
    the measured domain, not from the syntactic category.

    - (82): GA `hotter`/`harder` — measures states → intensive
    - (83): Noun `more coffee`/`more plastic` — measures entities → extensive
    - (84): GA `fuller`/`heavier` — measures entities → extensive (reversal!)
    - (85): Noun `more heat`/`more firmness` — measures states → intensive (reversal!)
    - (86–89): Verbal/adverbal parallels -/
structure DimensionReversalDatum where
  form : String
  category : LexCat
  dimensionName : String
  measuredDomain : MeasuredDomain
  /-- Is the dimension intensive (state-measuring) rather than extensive? -/
  intensive : Bool
  deriving Repr

/-- (82a): "This coffee is hotter than that coffee is." — TEMPERATURE, *VOLUME.
    GA measuring states → intensive. -/
def hotterDatum : DimensionReversalDatum :=
  { form := "hotter", category := .gradableAdj, dimensionName := "temperature"
  , measuredDomain := .state, intensive := true }

/-- (82b): "This plastic is harder than that plastic is." — HARDNESS, *WEIGHT.
    GA measuring states → intensive. -/
def harderDatum : DimensionReversalDatum :=
  { form := "harder", category := .gradableAdj, dimensionName := "hardness"
  , measuredDomain := .state, intensive := true }

/-- (83a): "Al has more coffee than Bill does." — *TEMPERATURE, VOLUME.
    Mass noun measuring entities → extensive. -/
def moreCoffeeDatum : DimensionReversalDatum :=
  { form := "more coffee", category := .massNoun, dimensionName := "volume"
  , measuredDomain := .entity, intensive := false }

/-- (83b): "Al has more plastic than Bill does." — *HARDNESS, WEIGHT.
    Mass noun measuring entities → extensive. -/
def morePlasticDatum : DimensionReversalDatum :=
  { form := "more plastic", category := .massNoun, dimensionName := "weight"
  , measuredDomain := .entity, intensive := false }

/-- (84a): "This glass is fuller than that glass is." — *TEMPERATURE, VOLUME.
    GA measuring entities (via container contents) → extensive.
    **Reversal**: GA but extensive, because measured domain is entity. -/
def fullerDatum : DimensionReversalDatum :=
  { form := "fuller", category := .gradableAdj, dimensionName := "volume"
  , measuredDomain := .entity, intensive := false }

/-- (84b): "This plastic is heavier than that plastic is." — *HARDNESS, WEIGHT.
    GA measuring entities → extensive.
    **Reversal**: GA but extensive, because measured domain is entity. -/
def heavierDatum : DimensionReversalDatum :=
  { form := "heavier", category := .gradableAdj, dimensionName := "weight"
  , measuredDomain := .entity, intensive := false }

/-- (85a): "This rock has more heat than that one does." — TEMPERATURE, *VOLUME.
    Mass noun measuring states → intensive.
    **Reversal**: noun but intensive, because measured domain is state. -/
def moreHeatDatum : DimensionReversalDatum :=
  { form := "more heat", category := .massNoun, dimensionName := "temperature"
  , measuredDomain := .state, intensive := true }

/-- (85b): "This mattress has more firmness than that one does." — HARDNESS, *WEIGHT.
    Mass noun measuring states → intensive.
    **Reversal**: noun but intensive, because measured domain is state. -/
def moreFirmnessDatum : DimensionReversalDatum :=
  { form := "more firmness", category := .massNoun, dimensionName := "hardness"
  , measuredDomain := .state, intensive := true }

/-- (89a): "Al sped up more than Peter did." — SPEED, *DISTANCE.
    Atelic VP measuring states (speed) → intensive.
    **Reversal**: verb but intensive, because measured domain is state. -/
def spedUpMoreDatum : DimensionReversalDatum :=
  { form := "sped up more", category := .atelicVP, dimensionName := "speed"
  , measuredDomain := .state, intensive := true }

/-- (87a): "Al drove more than Peter did." — *SPEED, DISTANCE.
    Atelic VP measuring events → extensive. -/
def droveMoreDatum : DimensionReversalDatum :=
  { form := "drove more", category := .atelicVP, dimensionName := "distance"
  , measuredDomain := .event, intensive := false }

/-- All dimension reversal data from §3.4. -/
def dimensionReversalData : List DimensionReversalDatum :=
  [ hotterDatum, harderDatum, moreCoffeeDatum, morePlasticDatum
  , fullerDatum, heavierDatum, moreHeatDatum, moreFirmnessDatum
  , spedUpMoreDatum, droveMoreDatum ]

-- ════════════════════════════════════════════════════
-- § 8. State Modification Data (§3.2, §3.5)
-- ════════════════════════════════════════════════════

/-- State modification datum: an adjective with a modifier that applies to
    the state argument, illustrating that states (like events) support
    predicate modification via conjunction (§3.2, p. 81; §3.5, p. 88).

    "happy in the morning" = ∃s. happy(s) ∧ Holder(x, s) ∧ in-the-morning(s)

    This parallels Davidson's event modification: states are eventualities
    of sort `.state`, so `EventModifier` applies to them. -/
structure StateModificationDatum where
  adjective : String
  modifier : String
  /-- Full modified form -/
  form : String
  deriving Repr

/-- "happy in the morning" — temporal modifier on a state (§3.5). -/
def happyMorningDatum : StateModificationDatum :=
  { adjective := "happy", modifier := "in the morning"
  , form := "happy in the morning" }

/-- "patient with Mary on the playground" — multiple modifiers on a state (§3.5). -/
def patientPlaygroundDatum : StateModificationDatum :=
  { adjective := "patient", modifier := "with Mary on the playground"
  , form := "patient with Mary on the playground" }

-- ============================================================================
-- § Theory–Data Bridge
-- ============================================================================

open Semantics.Lexical.Measurement
open Semantics.Lexical.Verb.Aspect (AspectualProfile)

/-- Map `LexCat` to `MereologicalStatus` using the theory's bridges. -/
def lexCatToStatus : LexCat → MereologicalStatus
  | .massNoun       => numberToStatus .mass
  | .countNoun      => numberToStatus .sg
  | .atelicVP       => telicityToStatus .atelic
  | .telicVP        => telicityToStatus .telic
  | .gradableAdj    => gradableToStatus
  | .nonGradableAdj => nonGradableToStatus

/-- The theory predicts: cumulative → felicitous with `much`. -/
def statusPredictsFelicitous : MereologicalStatus → Bool
  | .cumulative => true
  | .quantized  => false

-- Per-datum felicity verification

theorem massNoun_felicity :
    statusPredictsFelicitous (lexCatToStatus .massNoun) =
      massNounDatum.felicitousWithMuch := rfl

theorem countNoun_felicity :
    statusPredictsFelicitous (lexCatToStatus .countNoun) =
      countNounDatum.felicitousWithMuch := rfl

theorem atelicVP_felicity :
    statusPredictsFelicitous (lexCatToStatus .atelicVP) =
      atelicVPDatum.felicitousWithMuch := rfl

theorem telicVP_felicity :
    statusPredictsFelicitous (lexCatToStatus .telicVP) =
      telicVPDatum.felicitousWithMuch := rfl

theorem gradableAdj_felicity :
    statusPredictsFelicitous (lexCatToStatus .gradableAdj) =
      gradableAdjDatum.felicitousWithMuch := rfl

theorem nonGradableAdj_felicity :
    statusPredictsFelicitous (lexCatToStatus .nonGradableAdj) =
      nonGradableAdjDatum.felicitousWithMuch := rfl

-- Cross-categorial parallel

theorem massNoun_atelicVP_same_status :
    lexCatToStatus .massNoun = lexCatToStatus .atelicVP := rfl

theorem countNoun_telicVP_same_status :
    lexCatToStatus .countNoun = lexCatToStatus .telicVP := rfl

theorem gradableAdj_patterns_with_cum :
    lexCatToStatus .gradableAdj = lexCatToStatus .massNoun := rfl

theorem nonGradableAdj_patterns_with_qua :
    lexCatToStatus .nonGradableAdj = lexCatToStatus .countNoun := rfl

-- Grammar shift bridges

theorem run_shift_via_telicize :
    let p : AspectualProfile := Semantics.Lexical.Verb.Aspect.activityProfile
    telicityToStatus p.telicity = .cumulative ∧
    telicityToStatus p.telicize.telicity = .quantized :=
  telicize_shifts_status _ rfl

theorem build_shift_via_atelicize :
    let p : AspectualProfile := Semantics.Lexical.Verb.Aspect.accomplishmentProfile
    telicityToStatus p.telicity = .quantized ∧
    telicityToStatus p.atelicize.telicity = .cumulative :=
  atelicize_shifts_status _ rfl

theorem rock_shift_status :
    lexCatToStatus .massNoun = .cumulative ∧
    lexCatToStatus .countNoun = .quantized := ⟨rfl, rfl⟩

-- Boundedness bridge

theorem massNoun_open_scale :
    (lexCatToStatus .massNoun).toBoundedness = .open_ := rfl

theorem countNoun_closed_scale :
    (lexCatToStatus .countNoun).toBoundedness = .closed := rfl

theorem atelicVP_open_scale :
    (lexCatToStatus .atelicVP).toBoundedness = .open_ := rfl

theorem telicVP_closed_scale :
    (lexCatToStatus .telicVP).toBoundedness = .closed := rfl

-- Dimension reversal bridges (§3.4)

def measuredDomainRestricted : MeasuredDomain → Bool
  | .state  => true
  | .entity => false
  | .event  => false

theorem hotter_restricted :
    measuredDomainRestricted hotterDatum.measuredDomain = hotterDatum.intensive := rfl

theorem harder_restricted :
    measuredDomainRestricted harderDatum.measuredDomain = harderDatum.intensive := rfl

theorem moreCoffee_not_restricted :
    measuredDomainRestricted moreCoffeeDatum.measuredDomain = moreCoffeeDatum.intensive := rfl

theorem morePlastic_not_restricted :
    measuredDomainRestricted morePlasticDatum.measuredDomain = morePlasticDatum.intensive := rfl

theorem fuller_not_restricted :
    measuredDomainRestricted fullerDatum.measuredDomain = fullerDatum.intensive := rfl

theorem heavier_not_restricted :
    measuredDomainRestricted heavierDatum.measuredDomain = heavierDatum.intensive := rfl

theorem moreHeat_restricted :
    measuredDomainRestricted moreHeatDatum.measuredDomain = moreHeatDatum.intensive := rfl

theorem moreFirmness_restricted :
    measuredDomainRestricted moreFirmnessDatum.measuredDomain = moreFirmnessDatum.intensive := rfl

theorem spedUpMore_restricted :
    measuredDomainRestricted spedUpMoreDatum.measuredDomain = spedUpMoreDatum.intensive := rfl

theorem droveMore_not_restricted :
    measuredDomainRestricted droveMoreDatum.measuredDomain = droveMoreDatum.intensive := rfl

-- State modification bridge (§3.5)

open Semantics.Events (Ev EvPred)
open Semantics.Events.ThematicRoles (ThematicFrame EventModifier
  modifiedStativeLogicalForm stativeLogicalForm modify modified_stative_is_pm)

theorem state_mod_pm_bridge {Entity Time : Type*} [LE Time]
    (P : EvPred Time) (frame : ThematicFrame Entity Time)
    (x : Entity) (M : EventModifier Time) :
    modifiedStativeLogicalForm P frame x M ↔
      stativeLogicalForm (modify P M) frame x :=
  modified_stative_is_pm P frame x M

end Phenomena.Comparison.Wellwood2015
