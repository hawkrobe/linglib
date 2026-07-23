import Linglib.Data.Examples.Schema

/-!
# `Kennedy1999` — typed example data

Auto-generated from `Linglib/Data/Examples/Kennedy1999.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kennedy1999.Examples`.
-/

namespace Kennedy1999.Examples

open Data.Examples

def cpa_long_short : LinguisticExample :=
  { id := "kennedy1999_cpa_long_short"
    source := ⟨"kennedy-1999", "(15), §3.1.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "#The Brothers Karamazov is longer than The Idiot is short"
    discourseSegments := []
    glossedTokens := []
    translation := "#The Brothers Karamazov is longer than The Idiot is short"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix_polarity", "positive"), ("standard_polarity", "negative"), ("shared_scale", "true")]
    comment := "Cross-polar anomaly: positive matrix adjective, negative subdeletion standard, same scale (length)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cpa_short_long : LinguisticExample :=
  { id := "kennedy1999_cpa_short_long"
    source := ⟨"kennedy-1999", "(16), §3.1.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "#The Idiot is shorter than The Brothers Karamazov is long"
    discourseSegments := []
    glossedTokens := []
    translation := "#The Idiot is shorter than The Brothers Karamazov is long"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix_polarity", "negative"), ("standard_polarity", "positive"), ("shared_scale", "true")]
    comment := "Cross-polar anomaly with the polarities reversed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def subdel_pos_pos : LinguisticExample :=
  { id := "kennedy1999_subdel_pos_pos"
    source := ⟨"kennedy-1999", "(19), §3.1.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Carmen's Cadillac is wider than Mike's Fiat is long"
    discourseSegments := []
    glossedTokens := []
    translation := "Carmen's Cadillac is wider than Mike's Fiat is long"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix_polarity", "positive"), ("standard_polarity", "positive"), ("shared_scale", "true")]
    comment := "Same-polarity subdeletion control: both adjectives positive on the shared scale of linear extent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def subdel_neg_neg : LinguisticExample :=
  { id := "kennedy1999_subdel_neg_neg"
    source := ⟨"kennedy-1999", "(20), §3.1.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fortunately, the ficus was shorter than the ceiling was low, so we were able to get it into the room"
    discourseSegments := []
    glossedTokens := []
    translation := "Fortunately, the ficus was shorter than the ceiling was low, so we were able to get it into the room"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix_polarity", "negative"), ("standard_polarity", "negative"), ("shared_scale", "true")]
    comment := "Same-polarity subdeletion control with two negative adjectives."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ficus_tall_high : LinguisticExample :=
  { id := "kennedy1999_ficus_tall_high"
    source := ⟨"kennedy-1999", "(61), §3.1.7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Unfortunately, the ficus turned out to be taller than the ceiling was high"
    discourseSegments := []
    glossedTokens := []
    translation := "Unfortunately, the ficus turned out to be taller than the ceiling was high"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix_polarity", "positive"), ("standard_polarity", "positive"), ("shared_scale", "true")]
    comment := "Minimal quadruple (61)-(64): cross-polar anomaly generalizes beyond antonym pairs to any polarity mismatch."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ficus_tall_low : LinguisticExample :=
  { id := "kennedy1999_ficus_tall_low"
    source := ⟨"kennedy-1999", "(62), §3.1.7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "#Unfortunately, the ficus turned out to be taller than the ceiling was low"
    discourseSegments := []
    glossedTokens := []
    translation := "#Unfortunately, the ficus turned out to be taller than the ceiling was low"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix_polarity", "positive"), ("standard_polarity", "negative"), ("shared_scale", "true")]
    comment := "tall and low are not antonyms, yet the polarity mismatch is anomalous."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ficus_short_low : LinguisticExample :=
  { id := "kennedy1999_ficus_short_low"
    source := ⟨"kennedy-1999", "(63), §3.1.7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Luckily, the ficus turned out to be shorter than the doorway was low"
    discourseSegments := []
    glossedTokens := []
    translation := "Luckily, the ficus turned out to be shorter than the doorway was low"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix_polarity", "negative"), ("standard_polarity", "negative"), ("shared_scale", "true")]
    comment := "Same-polarity (negative-negative) member of the quadruple."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ficus_short_high : LinguisticExample :=
  { id := "kennedy1999_ficus_short_high"
    source := ⟨"kennedy-1999", "(64), §3.1.7"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "#Luckily, the ficus turned out to be shorter than the doorway was high"
    discourseSegments := []
    glossedTokens := []
    translation := "#Luckily, the ficus turned out to be shorter than the doorway was high"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix_polarity", "negative"), ("standard_polarity", "positive"), ("shared_scale", "true")]
    comment := "Polarity-mismatch member of the quadruple with the negative adjective in the matrix."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def incomm_tall_clever : LinguisticExample :=
  { id := "kennedy1999_incomm_tall_clever"
    source := ⟨"kennedy-1999", "(25), §3.1.4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "#Mike is taller than Carmen is clever"
    discourseSegments := []
    glossedTokens := []
    translation := "#Mike is taller than Carmen is clever"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix_polarity", "positive"), ("standard_polarity", "positive"), ("shared_scale", "false")]
    comment := "Incommensurability: same polarity but distinct scales (height vs cleverness)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def incomm_tragic_heavy : LinguisticExample :=
  { id := "kennedy1999_incomm_tragic_heavy"
    source := ⟨"kennedy-1999", "(26), §3.1.4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "#The Idiot is more tragic than my copy of The Brothers Karamazov is heavy"
    discourseSegments := []
    glossedTokens := []
    translation := "#The Idiot is more tragic than my copy of The Brothers Karamazov is heavy"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("matrix_polarity", "positive"), ("standard_polarity", "positive"), ("shared_scale", "false")]
    comment := "Incommensurability with two positive adjectives on distinct scales."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mp_cadillac : LinguisticExample :=
  { id := "kennedy1999_mp_cadillac"
    source := ⟨"kennedy-1999", "(69), §3.1.8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My Cadillac is 8 feet long"
    discourseSegments := []
    glossedTokens := []
    translation := "My Cadillac is 8 feet long"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("construction", "absolute")]
    comment := "Measure phrase with a positive adjective: positive extents are bounded, so the ordering is defined."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mp_fiat : LinguisticExample :=
  { id := "kennedy1999_mp_fiat"
    source := ⟨"kennedy-1999", "(70), §3.1.8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "#My Fiat is 5 feet short"
    discourseSegments := []
    glossedTokens := []
    translation := "#My Fiat is 5 feet short"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("construction", "absolute")]
    comment := "Measure phrase with a negative adjective: negative extents are unbounded above, so the ordering is undefined."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mp_fiat_comparative : LinguisticExample :=
  { id := "kennedy1999_mp_fiat_comparative"
    source := ⟨"kennedy-1999", "(73), §3.1.8"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "My fiat is shorter than 8 feet"
    discourseSegments := []
    glossedTokens := []
    translation := "My fiat is shorter than 8 feet"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("construction", "comparative")]
    comment := "Phrasal comparative contrast to (70): the standard is derived by applying short to the measure phrase, not by the measure phrase directly."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mp_reich : LinguisticExample :=
  { id := "kennedy1999_mp_reich"
    source := ⟨"kennedy-1999", "(79), §3.1.9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "#Mr. Reich is 5 feet short"
    discourseSegments := []
    glossedTokens := []
    translation := "#Mr. Reich is 5 feet short"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("construction", "absolute")]
    comment := "Negative adjectives reject overt measure phrases; cited in the argument that sharp-flat pairs are both positive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mp_slow : LinguisticExample :=
  { id := "kennedy1999_mp_slow"
    source := ⟨"kennedy-1999", "(80), §3.1.9"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "#Maureen was driving 14 mph slow"
    discourseSegments := []
    glossedTokens := []
    translation := "#Maureen was driving 14 mph slow"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("construction", "absolute")]
    comment := "Adverbial counterpart of the measure-phrase restriction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [cpa_long_short, cpa_short_long, subdel_pos_pos, subdel_neg_neg, ficus_tall_high, ficus_tall_low, ficus_short_low, ficus_short_high, incomm_tall_clever, incomm_tragic_heavy, mp_cadillac, mp_fiat, mp_fiat_comparative, mp_reich, mp_slow]

end Kennedy1999.Examples
