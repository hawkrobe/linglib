/-!
# Wellwood (2015): Empirical Data

@cite{wellwood-2015}

Theory-neutral empirical data from Wellwood (2015) on the distribution
of `much`/`many` and dimensional restrictions in comparatives across
nominal, verbal, and adjectival domains.

## Data Sources

- §2.1: Nominal comparatives (mass vs count nouns)
- §2.2: Verbal comparatives (atelic vs telic VPs)
- §3.1–3.2: Adjectival comparatives (gradable vs non-gradable adjectives)
- §3.3: Morphosyntactic evidence (`more` = `much` + `-er`, Bresnan 1973)
- §3.4: Dimensional restriction patterns
- §5: Number morphology and measurement (grammar shifts measurement)

## References

- Wellwood, A. (2015). On the semantics of comparison across categories.
  Linguistics and Philosophy 38(1): 67-101.
-/

namespace Phenomena.Gradability.Wellwood2015

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

/-- Bresnan (1973): `more` = `much` + `-er` (§3.3, p. 82–84).

    (70) a. as much soup    b. too much soup    c. so much soup
         d. that much soup  e. *more much soup

    `much` occurs with CUM-like predicates (mass nouns, atelic VPs).
    `many` is a suppletive variant of `much` for count/QUA domains
    (Wellwood 2014, fn. 11). -/
structure MuchManyDistribution where
  /-- `much` occurs with CUM-like predicates -/
  much_with_cum : Bool
  /-- `many` occurs with QUA-like predicates -/
  many_with_qua : Bool
  deriving DecidableEq, BEq, Repr

def muchManyData : MuchManyDistribution :=
  { much_with_cum := true
  , many_with_qua := true }

end Phenomena.Gradability.Wellwood2015
