import Linglib.Data.Examples.Schema

/-!
# `TieuEtAl2020` — typed example data

Auto-generated from `Linglib/Data/Examples/TieuEtAl2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TieuEtAl2020.Examples`.
-/

namespace TieuEtAl2020.Examples

open Data.Examples

def fed_giraffes_pos : LinguisticExample :=
  { id := "tieuetal2020_fed_giraffes_pos"
    source := ⟨"tieu-etal-2020", ""⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed giraffes"
    discourseSegments := []
    glossedTokens := []
    translation := "Emily fed giraffes"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("multiplicity (>1)", .acceptable)]
    paperFeatures := [("polarity", "positive"), ("multiplicity_inference", "present")]
    comment := "Core multiplicity datum, positive (upward-entailing) form: interpreted as 'Emily fed more than one giraffe'. Migrated from Phenomena/Plurals/Multiplicity.lean `fedGiraffes` (multiplicityInPositive = true); no example number asserted by the Lean source, so paperLabel is left empty."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def fed_giraffes_neg : LinguisticExample :=
  { id := "tieuetal2020_fed_giraffes_neg"
    source := ⟨"tieu-etal-2020", ""⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes"
    discourseSegments := []
    glossedTokens := []
    translation := "Emily didn't feed giraffes"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("multiplicity (>1)", .unacceptable)]
    paperFeatures := [("polarity", "negative"), ("multiplicity_inference", "absent")]
    comment := "Core multiplicity datum, negative (downward-entailing) form: interpreted as 'Emily didn't feed any giraffes', NOT 'Emily didn't feed more than one giraffe' — the multiplicity reading is unavailable under negation. Migrated from Phenomena/Plurals/Multiplicity.lean `fedGiraffes` (multiplicityInNegative = false); no example number asserted by the Lean source, so paperLabel is left empty."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_positive : LinguisticExample :=
  { id := "tieuetal2020_exp1_positive"
    source := ⟨"tieu-etal-2020", "Exp. 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily fed pigs"
    discourseSegments := []
    glossedTokens := []
    translation := "Emily fed pigs"
    context := "Emily has an apple. She feeds one pig. Only that pig was fed."
    judgment := .questionable
    alternatives := []
    readings := [("multiplicity (>1)", .acceptable), ("inclusive (one or more)", .marginal)]
    paperFeatures := [("experiment", "1"), ("polarity", "positive"), ("n_acted_on", "one"), ("acceptance_indicates_multiplicity", "false")]
    comment := "TVJ trial, upward-entailing condition. Rejecting = computing multiplicity (one pig is not 'more than one'). Sentence-level judgment 'questionable' encodes the group-split TVJ outcome recorded qualitatively in the Lean source (exp1Results): adults' multiplicity rate high (predominantly reject in this one-pig context), children's low (largely accept on the inclusive reading). Reading judgments encode availability for adults: multiplicity dominant, inclusive residual. Migrated from Studies/TieuEtAl2020.lean `exp1_positive`. UNVERIFIED paperLabel: 'Exp. 1' is asserted by the Lean docstring, not checked against the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_negative : LinguisticExample :=
  { id := "tieuetal2020_exp1_negative"
    source := ⟨"tieu-etal-2020", "Exp. 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emily didn't feed giraffes"
    discourseSegments := []
    glossedTokens := []
    translation := "Emily didn't feed giraffes"
    context := "Emily has food for one giraffe. She feeds that giraffe. The others go unfed."
    judgment := .questionable
    alternatives := []
    readings := [("multiplicity (>1) local under negation", .marginal)]
    paperFeatures := [("experiment", "1"), ("polarity", "negative"), ("n_acted_on", "one"), ("acceptance_indicates_multiplicity", "true")]
    comment := "TVJ trial, downward-entailing condition. Accepting = computing multiplicity locally under negation (interpreting as 'Emily didn't feed more than one giraffe'); on the inclusive reading the sentence is literally false (she fed one). Sentence-level judgment 'questionable' encodes the mixed TVJ outcome recorded qualitatively in the Lean source (exp1Results): adults' negative-condition multiplicity rate moderate, children's low. Reading judgment 'marginal' encodes that moderate adult availability. Migrated from Studies/TieuEtAl2020.lean `exp1_negative`. UNVERIFIED paperLabel: 'Exp. 1' is asserted by the Lean docstring, not checked against the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp3_positive_plural : LinguisticExample :=
  { id := "tieuetal2020_exp3_positive_plural"
    source := ⟨"tieu-etal-2020", "Exp. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Koala bought pears"
    discourseSegments := []
    glossedTokens := []
    translation := "Koala bought pears"
    context := "Koala only bought one pear."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("polarity", "positive"), ("n_acted_on", "one"), ("task", "ternary_reward"), ("preferred_reward", "intermediate")]
    comment := "Experiment 3 ternary judgment task (small/medium/large strawberry for false/neither/true), adults on Amazon Mechanical Turk, singular context. Literally true (bought one or more) but with a false multiplicity implicature — misleading. Adults' preferred reward: intermediate; judgment 'marginal' maps that intermediate ternary outcome onto the 5-level scale. Migrated from Studies/TieuEtAl2020.lean `exp3_positive_plural`. UNVERIFIED paperLabel: 'Exp. 3' is asserted by the Lean docstring, not checked against the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp3_negative_plural : LinguisticExample :=
  { id := "tieuetal2020_exp3_negative_plural"
    source := ⟨"tieu-etal-2020", "Exp. 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Koala didn't buy pears"
    discourseSegments := []
    glossedTokens := []
    translation := "Koala didn't buy pears"
    context := "Koala only bought one pear."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "3"), ("polarity", "negative"), ("n_acted_on", "one"), ("task", "ternary_reward"), ("preferred_reward", "minimal")]
    comment := "Experiment 3 ternary judgment task, singular context, negative sentence. Literally false (Koala did buy one or more pears); adults' preferred reward: minimal; judgment 'unacceptable' maps that minimal ternary outcome onto the 5-level scale. The positive/negative asymmetry with exp3_positive_plural confirms the implicature approach's singular-context prediction. Migrated from Studies/TieuEtAl2020.lean `exp3_negative_plural`. UNVERIFIED paperLabel: 'Exp. 3' is asserted by the Lean docstring, not checked against the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [fed_giraffes_pos, fed_giraffes_neg, exp1_positive, exp1_negative, exp3_positive_plural, exp3_negative_plural]

end TieuEtAl2020.Examples
