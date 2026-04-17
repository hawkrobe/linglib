import Linglib.Theories.Semantics.Noun.GradableNouns

/-!
# Morzycki (2009)

@cite{morzycki-2009}

Degree modification of gradable nouns: size adjectives and adnominal degree morphemes.
*Natural Language Semantics* 17:175–203.

## Key claims formalized

1. **Gradable nouns as measure functions** (§3.1, eq. 48b):
   ⟦idiot⟧ = λx . ιd[x is d-idiotic] = *idiot*

2. **MEAS_N operator** (§4.3, eq. 76): Size adjectives are introduced by a
   nominal counterpart of the adjectival MEAS morpheme. The combined denotation
   requires the individual's degree to exceed both the size adjective's minimum
   and the noun's contextual standard.

3. **Bigness Generalization** (§2.2, ex. 29): Adjectives that predicate bigness
   systematically license degree readings; adjectives of smallness do not.

4. **Position Generalization** (§2.1, ex. 18): Degree readings of size adjectives
   are possible only in attributive positions (prenominally in English).

5. **Adnominal degree morphemes** (§3.4, ex. 55): *real*, *true*, *complete*,
   *total*, *absolute* are DegN heads — the nominal counterpart of adjectival
   degree words like *very*.

6. **Scale structure compatibility** (p. 190, ex. 60): *complete* is restricted
   to nouns whose scales have maxima (*complete idiot* OK, *#complete smoker* not).

## Theory–data connection

The Bigness Generalization is *derived* from scale structure (§4.4, eqs. 81–85):
- **Positive (big)**: min{d : big(d)} = θ_big > 0 → substantive restriction
- **Negative (small)**: min{d : small(d)} = d₀ → vacuous; "small N" ≡ bare "N"

`small_idiot_vacuous` and `big_idiot_restrictive` from `GradableNouns.lean`
predict the acceptability pattern recorded in the data below.
-/

namespace Morzycki2009

open Semantics.Noun.GradableNouns
open Core.Scale (deg)

-- ═══════════════════════════════════════════════════════════════
-- Data: Bigness Generalization (§2.2)
-- ═══════════════════════════════════════════════════════════════

inductive SizePolarity where
  | positive  -- big, huge, enormous, tremendous
  | negative  -- small, tiny, little, slight
  deriving Repr, DecidableEq

structure BignessGeneralizationDatum where
  sizeAdj : String
  polarity : SizePolarity
  degreeReadingAvailable : Bool
  sentence : String
  source : String

-- Positive-polarity size adjectives: degree reading available (ex. 19)
def bigIdiotDatum : BignessGeneralizationDatum :=
  { sizeAdj := "big", polarity := .positive, degreeReadingAvailable := true
  , sentence := "George is a big idiot"
  , source := "Morzycki 2009 (ex. 19)" }

def hugeEnthusiastDatum : BignessGeneralizationDatum :=
  { sizeAdj := "huge", polarity := .positive, degreeReadingAvailable := true
  , sentence := "Three huge goat cheese enthusiasts were arguing in the corner"
  , source := "Morzycki 2009 (ex. 1c)" }

def enormousIdiotDatum : BignessGeneralizationDatum :=
  { sizeAdj := "enormous", polarity := .positive, degreeReadingAvailable := true
  , sentence := "George is an enormous idiot"
  , source := "Morzycki 2009 (ex. 1a)" }

-- Negative-polarity size adjectives: degree reading unavailable (ex. 20)
def smallIdiotDatum : BignessGeneralizationDatum :=
  { sizeAdj := "small", polarity := .negative, degreeReadingAvailable := false
  , sentence := "%George is a small idiot (degree reading unavailable)"
  , source := "Morzycki 2009 (ex. 20)" }

def tinyIdiotDatum : BignessGeneralizationDatum :=
  { sizeAdj := "tiny", polarity := .negative, degreeReadingAvailable := false
  , sentence := "%George is a tiny idiot (degree reading unavailable)"
  , source := "Morzycki 2009 (ex. 20)" }

def minuteIdiotDatum : BignessGeneralizationDatum :=
  { sizeAdj := "minute", polarity := .negative, degreeReadingAvailable := false
  , sentence := "%George is a minute idiot (degree reading unavailable)"
  , source := "Morzycki 2009 (ex. 20)" }

-- Morzycki (p. 179) explicitly says "slight" is NOT a size adjective
-- synchronically — it predicates slenderness, not generalized size.
-- This is outside the Bigness Generalization's scope, not an exception to it.
def slightExaggerationDatum : BignessGeneralizationDatum :=
  { sizeAdj := "slight", polarity := .negative
  , degreeReadingAvailable := true  -- not a true exception: "slight" is not a size adj.
  , sentence := "That's a slight exaggeration"
  , source := "Morzycki 2009 (ex. 21; argues slight is not a size adj.)" }

def bignessExamples : List BignessGeneralizationDatum :=
  [bigIdiotDatum, hugeEnthusiastDatum, enormousIdiotDatum,
   smallIdiotDatum, tinyIdiotDatum, minuteIdiotDatum, slightExaggerationDatum]

-- ═══════════════════════════════════════════════════════════════
-- Data: Position Generalization (§2.1)
-- ═══════════════════════════════════════════════════════════════

structure PositionGeneralizationDatum where
  noun : String
  sizeAdj : String
  position : String  -- "attributive" or "predicative"
  degreeReadingAvailable : Bool
  sentence : String
  source : String

def bigStampCollectorAttributive : PositionGeneralizationDatum :=
  { noun := "stamp-collector", sizeAdj := "big", position := "attributive"
  , degreeReadingAvailable := true
  , sentence := "that big stamp-collector"
  , source := "Morzycki 2009 (ex. 7a)" }

def bigStampCollectorPredicative : PositionGeneralizationDatum :=
  { noun := "stamp-collector", sizeAdj := "big", position := "predicative"
  , degreeReadingAvailable := false
  , sentence := "%That stamp-collector is big"
  , source := "Morzycki 2009 (ex. 7b)" }

def positionExamples : List PositionGeneralizationDatum :=
  [bigStampCollectorAttributive, bigStampCollectorPredicative]

-- ═══════════════════════════════════════════════════════════════
-- Data: Gradable noun examples (§1, §3.1)
-- ═══════════════════════════════════════════════════════════════

inductive NominalScaleType where
  | evaluative  -- idiot, genius (quality judgment)
  | enthusiasm  -- fan, lover, supporter (degree of devotion)
  | frequency   -- smoker, stamp-collector (how often/dedicated)
  | intensity   -- liar, cheat (how extremely)
  deriving Repr, DecidableEq

structure GradableNounExample where
  noun : String
  scaleType : NominalScaleType
  degreeAdjectives : List String
  sentence : String
  source : String

def idiotExample : GradableNounExample :=
  { noun := "idiot", scaleType := .evaluative
  , degreeAdjectives := ["big", "enormous", "huge", "colossal", "mammoth", "gargantuan"]
  , sentence := "George is a {big/enormous/huge/colossal/mammoth/gargantuan} idiot"
  , source := "Morzycki 2009 (ex. 19)" }

def enthusiastExample : GradableNounExample :=
  { noun := "goat cheese enthusiast", scaleType := .enthusiasm
  , degreeAdjectives := ["huge", "colossal"]
  , sentence := "Three huge goat cheese enthusiasts were arguing in the corner"
  , source := "Morzycki 2009 (ex. 1c-d)" }

def stampCollectorExample : GradableNounExample :=
  { noun := "stamp-collector", scaleType := .frequency
  , degreeAdjectives := ["big"]
  , sentence := "Gladys is a big stamp-collector"
  , source := "Morzycki 2009 (ex. 1b)" }

def bastardExample : GradableNounExample :=
  { noun := "bastard", scaleType := .intensity
  , degreeAdjectives := ["big"]
  , sentence := "The other driver was a really big bastard"
  , source := "Morzycki 2009 (ex. 32a)" }

def gradableNounExamples : List GradableNounExample :=
  [idiotExample, enthusiastExample, stampCollectorExample, bastardExample]

-- ═══════════════════════════════════════════════════════════════
-- Data: Nominal comparisons (§3.2)
-- ═══════════════════════════════════════════════════════════════

structure NominalComparisonDatum where
  noun : String
  comparativeForm : String
  sentence : String
  acceptable : Bool
  source : String

def moreOfAnIdiot : NominalComparisonDatum :=
  { noun := "idiot", comparativeForm := "more of an N"
  , sentence := "more of an idiot than Floyd is an idiot"
  , acceptable := true, source := "Morzycki 2009 (ex. 54)" }

def biggerIdiotComparison : NominalComparisonDatum :=
  { noun := "idiot", comparativeForm := "bigger N"
  , sentence := "Gladys is a bigger idiot than Floyd"
  , acceptable := true, source := "Morzycki 2009 (ex. 2a)" }

def nominalComparisonExamples : List NominalComparisonDatum :=
  [moreOfAnIdiot, biggerIdiotComparison]

-- ═══════════════════════════════════════════════════════════════
-- Data: Cross-linguistic (§1, §2)
-- ═══════════════════════════════════════════════════════════════

structure CrossLinguisticDatum where
  language : String
  sizeAdj : String
  polarity : SizePolarity
  degreeReadingAvailable : Bool
  translation : String
  source : String

def germanGrossIdiot : CrossLinguisticDatum :=
  { language := "German", sizeAdj := "groß", polarity := .positive
  , degreeReadingAvailable := true, translation := "ein großer Idiot"
  , source := "Morzycki 2009 (ex. 5)" }

def germanKleinIdiot : CrossLinguisticDatum :=
  { language := "German", sizeAdj := "klein", polarity := .negative
  , degreeReadingAvailable := false
  , translation := "%Floyd ist ein kleiner Idiot (degree reading unavailable)"
  , source := "Morzycki 2009 (ex. 27)" }

def crossLinguisticExamples : List CrossLinguisticDatum :=
  [germanGrossIdiot, germanKleinIdiot]

-- ═══════════════════════════════════════════════════════════════
-- Data: Adnominal degree morphemes (§3.4)
-- ═══════════════════════════════════════════════════════════════

structure AdnominalDegreeMorpheme where
  morpheme : String
  attributiveDegreeReading : Bool
  predicativeDegreeReading : Bool
  adjDegreeModCooccurrence : Bool
  source : String

-- Morzycki (2009, ex. 55–57)
def realDegN : AdnominalDegreeMorpheme :=
  { morpheme := "real", attributiveDegreeReading := true
  , predicativeDegreeReading := false, adjDegreeModCooccurrence := false
  , source := "Morzycki 2009 (ex. 55–57)" }

def trueDegN : AdnominalDegreeMorpheme :=
  { morpheme := "true", attributiveDegreeReading := true
  , predicativeDegreeReading := false, adjDegreeModCooccurrence := false
  , source := "Morzycki 2009 (ex. 55–57)" }

def totalDegN : AdnominalDegreeMorpheme :=
  { morpheme := "total", attributiveDegreeReading := true
  , predicativeDegreeReading := false, adjDegreeModCooccurrence := false
  , source := "Morzycki 2009 (ex. 55–57)" }

def completeDegN : AdnominalDegreeMorpheme :=
  { morpheme := "complete", attributiveDegreeReading := true
  , predicativeDegreeReading := false, adjDegreeModCooccurrence := false
  , source := "Morzycki 2009 (ex. 55–57)" }

def absoluteDegN : AdnominalDegreeMorpheme :=
  { morpheme := "absolute", attributiveDegreeReading := true
  , predicativeDegreeReading := false, adjDegreeModCooccurrence := false
  , source := "Morzycki 2009 (ex. 55–57)" }

def adnominalDegreeMorphemes : List AdnominalDegreeMorpheme :=
  [realDegN, trueDegN, totalDegN, completeDegN, absoluteDegN]

-- ═══════════════════════════════════════════════════════════════
-- Data: Scale structure compatibility (p. 190, ex. 60)
-- ═══════════════════════════════════════════════════════════════

structure ScaleMaximumDatum where
  noun : String
  hasScaleMaximum : Bool
  completeAcceptable : Bool
  source : String

def idiotScaleMax : ScaleMaximumDatum :=
  { noun := "idiot", hasScaleMaximum := true, completeAcceptable := true
  , source := "Morzycki 2009 (ex. 60a)" }

def dorkScaleMax : ScaleMaximumDatum :=
  { noun := "dork", hasScaleMaximum := true, completeAcceptable := true
  , source := "Morzycki 2009 (ex. 60a)" }

def fascistScaleMax : ScaleMaximumDatum :=
  { noun := "fascist", hasScaleMaximum := true, completeAcceptable := true
  , source := "Morzycki 2009 (ex. 60a)" }

def smokerScaleMax : ScaleMaximumDatum :=
  { noun := "smoker", hasScaleMaximum := false, completeAcceptable := false
  , source := "Morzycki 2009 (ex. 60b)" }

def enthusiastScaleMax : ScaleMaximumDatum :=
  { noun := "goat cheese enthusiast", hasScaleMaximum := false
  , completeAcceptable := false, source := "Morzycki 2009 (ex. 60b)" }

def curlingFanScaleMax : ScaleMaximumDatum :=
  { noun := "fan of curling", hasScaleMaximum := false
  , completeAcceptable := false, source := "Morzycki 2009 (ex. 60b)" }

def scaleMaximumExamples : List ScaleMaximumDatum :=
  [idiotScaleMax, dorkScaleMax, fascistScaleMax,
   smokerScaleMax, enthusiastScaleMax, curlingFanScaleMax]

-- ═══════════════════════════════════════════════════════════════
-- § 1: Theory predicts the Bigness Generalization
-- ═══════════════════════════════════════════════════════════════

/-- The theory predicts that negative-polarity size adjectives are vacuous:
    "small idiot" has the same truth conditions as bare "idiot".
    This is Morzycki's key result (§4.4, eqs. 81–85):
    min{d : d ∈ scale(idiot) ∧ standard(small) ≤ small(d)} = d₀,
    so the size adjective contributes nothing. -/
theorem negative_polarity_vacuous {E : Type} (noun : GradableNoun E) (x : E) :
    smallIdiot noun x = noun.pos x :=
  small_idiot_vacuous noun x

/-- The theory predicts that positive-polarity size adjectives are
    genuinely restrictive: "big idiot" entails "idiot". -/
theorem positive_polarity_restrictive {E : Type} (noun : GradableNoun E)
    (h : noun.standard < deg 5) (x : E) :
    bigIdiot noun x = true → noun.pos x = true :=
  big_idiot_restrictive noun h x

/-- There exist entities that are idiots but not big idiots —
    demonstrating bigIdiot is strictly stronger than bare pos.
    This matches Morzycki's entailment (§4.3, ex. 75):
    "#Clyde is a big idiot, but not an idiot." -/
theorem big_idiot_strictly_stronger :
    exampleIdiot.pos .sarah = true ∧
    bigIdiot exampleIdiot .sarah = false := by
  constructor <;> native_decide

-- ═══════════════════════════════════════════════════════════════
-- § 2: Verify data consistency with theory predictions
-- ═══════════════════════════════════════════════════════════════

/-- All positive-polarity examples in the data have degree readings. -/
theorem positive_examples_have_degree_readings :
    (bignessExamples.filter (·.polarity == .positive)).all
      (·.degreeReadingAvailable) = true := by
  native_decide

/-- All negative-polarity size adjectives in the data lack degree readings.
    "slight" is excluded because Morzycki (p. 179) argues it is not
    a size adjective. -/
theorem negative_size_adj_lack_degree_readings :
    (bignessExamples.filter (λ d =>
      d.polarity == .negative && d.sizeAdj != "slight")).all
      (! ·.degreeReadingAvailable) = true := by
  native_decide

/-- Position Generalization: attributive has degree reading,
    predicative does not. -/
theorem position_generalization_holds :
    (positionExamples.filter (·.position == "attributive")).all
      (·.degreeReadingAvailable) = true ∧
    (positionExamples.filter (·.position == "predicative")).all
      (! ·.degreeReadingAvailable) = true := by
  constructor <;> native_decide

-- ═══════════════════════════════════════════════════════════════
-- § 3: Adnominal degree morphemes (§3.4)
-- ═══════════════════════════════════════════════════════════════

/-- All adnominal degree morphemes have degree readings attributively
    but not predicatively — they obey the Position Generalization. -/
theorem degN_obey_position_generalization :
    adnominalDegreeMorphemes.all (·.attributiveDegreeReading) = true ∧
    adnominalDegreeMorphemes.all (! ·.predicativeDegreeReading) = true := by
  constructor <;> native_decide

/-- Adnominal degree morphemes cannot co-occur with adjectival degree
    modifiers — they occupy the same structural position (DegN). -/
theorem degN_no_adj_degree_mod_cooccurrence :
    adnominalDegreeMorphemes.all (! ·.adjDegreeModCooccurrence) = true := by
  native_decide

-- ═══════════════════════════════════════════════════════════════
-- § 4: Scale structure compatibility (p. 190, ex. 60)
-- ═══════════════════════════════════════════════════════════════

/-- "complete" is acceptable exactly when the noun's scale has a maximum. -/
theorem complete_iff_scale_maximum :
    scaleMaximumExamples.all
      (λ d => d.hasScaleMaximum == d.completeAcceptable) = true := by
  native_decide

-- ═══════════════════════════════════════════════════════════════
-- § 5: Concrete derivation — "big idiot" vs "small idiot"
-- ═══════════════════════════════════════════════════════════════

/-- The minimum degree satisfying POS(big) is d5 (substantive). -/
theorem min_big_substantive : minDegree posBig = some (deg 5) := min_big_is_d5

/-- The minimum degree satisfying POS(small) is d0 (vacuous). -/
theorem min_small_vacuous_d0 : minDegree posSmall = some (deg 0) := min_small_is_d0

/-- George (idiocy d8): big idiot ✓, small idiot = bare idiot ✓ -/
theorem george_big_idiot : bigIdiot exampleIdiot .george = true := by native_decide

theorem george_small_eq_bare :
    smallIdiot exampleIdiot .george = exampleIdiot.pos .george := by
  rw [small_idiot_vacuous]

/-- Floyd (idiocy d1): big idiot ✗, small idiot = bare idiot ✗ -/
theorem floyd_not_big_idiot : bigIdiot exampleIdiot .floyd = false := by native_decide

theorem floyd_small_eq_bare :
    smallIdiot exampleIdiot .floyd = exampleIdiot.pos .floyd := by
  rw [small_idiot_vacuous]

end Morzycki2009
