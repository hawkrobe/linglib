import Linglib.Data.Examples.Schema

/-!
# `Kriz2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Kriz2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kriz2015.Examples`.
-/

namespace Kriz2015.Examples

open Data.Examples

def switches_pos_gap : LinguisticExample :=
  { id := "kriz2015_switches_pos_gap"
    source := ⟨"kriz-2015", "canonical switches homogeneity item"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The switches are on."
    discourseSegments := []
    glossedTokens := [("The", "DEF"), ("switches", "switch.PL"), ("are", "be.PRS.PL"), ("on", "on")]
    translation := "The switches are on."
    context := "Ten switches; 5 of the 10 switches are on."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "GAP"), ("gap_detected", "true")]
    comment := "Migrated from Phenomena/Plurals/Homogeneity.lean switchesExample (positiveInGap = neitherTrueNorFalse): homogeneity gap — neither clearly true nor clearly false when some but not all switches are on. The Lean source also cites kriz-chemla-2015 for this item. The ALL cell (all 10 on: positive clearly true, negative clearly false) and NONE cell (none on: positive clearly false, negative clearly true) are recorded in the same Lean datum."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def switches_neg_gap : LinguisticExample :=
  { id := "kriz2015_switches_neg_gap"
    source := ⟨"kriz-2015", "canonical switches homogeneity item, negated"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The switches are not on."
    discourseSegments := []
    glossedTokens := [("The", "DEF"), ("switches", "switch.PL"), ("are", "be.PRS.PL"), ("not", "NEG"), ("on", "on")]
    translation := "The switches are not on."
    context := "Ten switches; 5 of the 10 switches are on."
    judgment := .questionable
    alternatives := [("It's not the case that the switches are on.", .questionable)]
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "GAP"), ("gap_detected", "true")]
    comment := "Migrated from Phenomena/Plurals/Homogeneity.lean switchesExample (negativeInGap = neitherTrueNorFalse): the gap is symmetric under negation. The sentential-negation variant in alternatives is carried from the Lean source's inline comment on negativeSentence."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def switches_nonmax_existential : LinguisticExample :=
  { id := "kriz2015_switches_nonmax_existential"
    source := ⟨"kriz-2015", "(11) switches non-maximality"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Oh no, the switches are on!"
    discourseSegments := []
    glossedTokens := [("Oh", "oh"), ("no", "no"), ("the", "DEF"), ("switches", "switch.PL"), ("are", "be.PRS.PL"), ("on", "on")]
    translation := "Oh no, the switches are on!"
    context := "Fire risk if any switch is on; 2 of the 10 switches are on. Implicit question: Are any of the switches on?"
    judgment := .acceptable
    alternatives := [("Oh no, all the switches are on!", .unacceptable)]
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "GAP"), ("issue", "existential")]
    comment := "UNVERIFIED paperLabel: dissertation example number carried from prior Lean file (Phenomena/Plurals/NonMaximality.lean switchesNonMaximality, 'dissertation (11)'), not checked against PDF. Non-maximal reading acceptable when the all/some distinction is irrelevant to the issue (acceptableInNonMaximalContext = true). The 'all the switches' alternative is migrated from switchesAllBlocks ('dissertation (17)' per the prior Lean file, equally unverified): 'all' blocks non-maximality even in this permissive context (allAcceptable = false)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def switches_nonmax_universal : LinguisticExample :=
  { id := "kriz2015_switches_nonmax_universal"
    source := ⟨"kriz-2015", "(11) switches non-maximality"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Oh no, the switches are on!"
    discourseSegments := []
    glossedTokens := [("Oh", "oh"), ("no", "no"), ("the", "DEF"), ("switches", "switch.PL"), ("are", "be.PRS.PL"), ("on", "on")]
    translation := "Oh no, the switches are on!"
    context := "Fire risk only if all 10 switches are on; 2 of the 10 switches are on. Implicit question: Are all the switches on?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "GAP"), ("issue", "universal")]
    comment := "UNVERIFIED paperLabel: dissertation example number carried from prior Lean file (Phenomena/Plurals/NonMaximality.lean switchesNonMaximality), not checked against PDF. Same sentence and scenario as the existential-issue row, but with the all/some distinction relevant the non-maximal use is misleading (acceptableInMaximalContext = false, Lean inline comment 'misleading')."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [switches_pos_gap, switches_neg_gap, switches_nonmax_existential, switches_nonmax_universal]

end Kriz2015.Examples
