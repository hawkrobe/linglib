import Linglib.Data.Examples.Schema

/-!
# `AghaJeretic2022` — typed example data

Auto-generated from `Linglib/Data/Examples/AghaJeretic2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AghaJeretic2022.Examples`.
-/

namespace AghaJeretic2022.Examples

open Data.Examples

def should_pos_all : LinguisticExample :=
  { id := "aghajeretic2022_should_pos_all"
    source := ⟨"agha-jeretic-2022", "(8)-(9) modal homogeneity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you should go."
    discourseSegments := []
    glossedTokens := [("According", "according"), ("to", "to"), ("the", "DEF"), ("rules", "rule.PL"), ("you", "2SG"), ("should", "should"), ("go", "go")]
    translation := "According to the rules, you should go."
    context := "All best deontic worlds are go-worlds."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "ALL"), ("modal", "should")]
    comment := "UNVERIFIED paperLabel: example numbers carried from prior Lean file (Studies/AghaJeretic2022.lean shouldHomogeneity docstring), not checked against PDF. Migrated from shouldHomogeneity (positiveInAll = clearlyTrue): judged clearly true when all best worlds satisfy the prejacent."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def should_pos_none : LinguisticExample :=
  { id := "aghajeretic2022_should_pos_none"
    source := ⟨"agha-jeretic-2022", "(8)-(9) modal homogeneity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you should go."
    discourseSegments := []
    glossedTokens := [("According", "according"), ("to", "to"), ("the", "DEF"), ("rules", "rule.PL"), ("you", "2SG"), ("should", "should"), ("go", "go")]
    translation := "According to the rules, you should go."
    context := "No best deontic worlds are go-worlds."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "NONE"), ("modal", "should")]
    comment := "UNVERIFIED paperLabel: example numbers carried from prior Lean file, not checked against PDF. Migrated from shouldHomogeneity (positiveInNone = clearlyFalse): sentence is grammatical and felicitous but judged clearly FALSE when no best world satisfies the prejacent; the 5-level scale has no truth-value slot, so falsity is recorded here."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def should_pos_gap : LinguisticExample :=
  { id := "aghajeretic2022_should_pos_gap"
    source := ⟨"agha-jeretic-2022", "(8)-(9) modal homogeneity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you should go."
    discourseSegments := []
    glossedTokens := [("According", "according"), ("to", "to"), ("the", "DEF"), ("rules", "rule.PL"), ("you", "2SG"), ("should", "should"), ("go", "go")]
    translation := "According to the rules, you should go."
    context := "Some but not all best deontic worlds are go-worlds."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "GAP"), ("modal", "should"), ("gap_detected", "true")]
    comment := "UNVERIFIED paperLabel: example numbers carried from prior Lean file, not checked against PDF. Migrated from shouldHomogeneity (positiveInGap = neitherTrueNorFalse): modal homogeneity gap — weak necessity, like a plural definite over worlds, is neither clearly true nor clearly false in a mixed domain."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def should_neg_all : LinguisticExample :=
  { id := "aghajeretic2022_should_neg_all"
    source := ⟨"agha-jeretic-2022", "(8)-(9) modal homogeneity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you shouldn't go."
    discourseSegments := []
    glossedTokens := [("According", "according"), ("to", "to"), ("the", "DEF"), ("rules", "rule.PL"), ("you", "2SG"), ("shouldn't", "should.NEG"), ("go", "go")]
    translation := "According to the rules, you shouldn't go."
    context := "All best deontic worlds are go-worlds."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "ALL"), ("modal", "should")]
    comment := "UNVERIFIED paperLabel: example numbers carried from prior Lean file, not checked against PDF. Migrated from shouldHomogeneity (negativeInAll = clearlyFalse): grammatical and felicitous but judged clearly FALSE when all best worlds satisfy the prejacent."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def should_neg_none : LinguisticExample :=
  { id := "aghajeretic2022_should_neg_none"
    source := ⟨"agha-jeretic-2022", "(8)-(9) modal homogeneity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you shouldn't go."
    discourseSegments := []
    glossedTokens := [("According", "according"), ("to", "to"), ("the", "DEF"), ("rules", "rule.PL"), ("you", "2SG"), ("shouldn't", "should.NEG"), ("go", "go")]
    translation := "According to the rules, you shouldn't go."
    context := "No best deontic worlds are go-worlds."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "NONE"), ("modal", "should")]
    comment := "UNVERIFIED paperLabel: example numbers carried from prior Lean file, not checked against PDF. Migrated from shouldHomogeneity (negativeInNone = clearlyTrue): judged clearly true when no best world satisfies the prejacent."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def should_neg_gap : LinguisticExample :=
  { id := "aghajeretic2022_should_neg_gap"
    source := ⟨"agha-jeretic-2022", "(8)-(9) modal homogeneity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you shouldn't go."
    discourseSegments := []
    glossedTokens := [("According", "according"), ("to", "to"), ("the", "DEF"), ("rules", "rule.PL"), ("you", "2SG"), ("shouldn't", "should.NEG"), ("go", "go")]
    translation := "According to the rules, you shouldn't go."
    context := "Some but not all best deontic worlds are go-worlds."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "GAP"), ("modal", "should"), ("gap_detected", "true")]
    comment := "UNVERIFIED paperLabel: example numbers carried from prior Lean file, not checked against PDF. Migrated from shouldHomogeneity (negativeInGap = neitherTrueNorFalse): gap is symmetric under negation. Also carries the domain-restriction critique datum (Lean domainRestrictionFails): the existential followup 'but you are allowed to go' is empirically infelicitous (#) after negated should, contrary to what a bivalent not-all semantics predicts."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def haveTo_pos_gap : LinguisticExample :=
  { id := "aghajeretic2022_haveTo_pos_gap"
    source := ⟨"agha-jeretic-2022", "(9b) strong necessity, no homogeneity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you have to go."
    discourseSegments := []
    glossedTokens := [("According", "according"), ("to", "to"), ("the", "DEF"), ("rules", "rule.PL"), ("you", "2SG"), ("have", "have"), ("to", "to"), ("go", "go")]
    translation := "According to the rules, you have to go."
    context := "Some but not all best deontic worlds are go-worlds."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "GAP"), ("modal", "haveTo"), ("gap_detected", "false"), ("classical_value", "false")]
    comment := "UNVERIFIED paperLabel: example number carried from prior Lean file (haveToNoHomogeneity docstring), not checked against PDF. Migrated from haveToNoHomogeneity (positiveInGap = clearlyFalse): strong necessity is bivalent — grammatical and felicitous but judged clearly FALSE in the mixed domain, no truth-value gap. The ALL and NONE cells of haveToNoHomogeneity are identical to the should rows (clearlyTrue/clearlyFalse) and are not duplicated here."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def haveTo_neg_gap : LinguisticExample :=
  { id := "aghajeretic2022_haveTo_neg_gap"
    source := ⟨"agha-jeretic-2022", "(9b) strong necessity, no homogeneity"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you don't have to go."
    discourseSegments := []
    glossedTokens := [("According", "according"), ("to", "to"), ("the", "DEF"), ("rules", "rule.PL"), ("you", "2SG"), ("don't", "do.NEG"), ("have", "have"), ("to", "to"), ("go", "go")]
    translation := "According to the rules, you don't have to go."
    context := "Some but not all best deontic worlds are go-worlds."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "GAP"), ("modal", "haveTo"), ("gap_detected", "false"), ("classical_value", "true")]
    comment := "UNVERIFIED paperLabel: example number carried from prior Lean file, not checked against PDF. Migrated from haveToNoHomogeneity (negativeInGap = clearlyTrue): the dominant reading is narrow-scope negation (not-required), judged clearly true in the mixed domain — compatible with the followup 'but you are allowed to go', unlike negated should."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def necessarily_removes_gap : LinguisticExample :=
  { id := "aghajeretic2022_necessarily_removes_gap"
    source := ⟨"agha-jeretic-2022", "(14)-(15) homogeneity removal"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "According to the rules, you shouldn't necessarily go."
    discourseSegments := []
    glossedTokens := [("According", "according"), ("to", "to"), ("the", "DEF"), ("rules", "rule.PL"), ("you", "2SG"), ("shouldn't", "should.NEG"), ("necessarily", "necessarily"), ("go", "go")]
    translation := "According to the rules, you shouldn't necessarily go."
    context := "Some but not all best worlds are go-worlds."
    judgment := .acceptable
    alternatives := [("According to the rules, you shouldn't go.", .questionable)]
    readings := []
    paperFeatures := [("polarity", "negative"), ("condition", "GAP"), ("modal", "should"), ("remover", "necessarily")]
    comment := "UNVERIFIED paperLabel: example numbers carried from prior Lean file (necessarilyRemovesModalHomogeneity docstring), not checked against PDF. Migrated from necessarilyRemovesModalHomogeneity: 'necessarily' removes the gap, paralleling nominal 'all' — the bare variant (alternatives) is neither true nor false in the gap scenario, while the necessarily-variant gets a determinate truth value (Lean preciseJudgment = clearlyFalse; recorded as carried, the determinacy contrast is the migrated claim). Per the Lean section docstring, the necessarily-variant licenses the existential followup 'but you can go' that the bare variant blocks."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def should_exception_qud1 : LinguisticExample :=
  { id := "aghajeretic2022_should_exception_qud1"
    source := ⟨"agha-jeretic-2022", "(17) exception tolerance"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To get a perfect grade, you should do every exercise."
    discourseSegments := []
    glossedTokens := [("To", "to"), ("get", "get"), ("a", "INDEF"), ("perfect", "perfect"), ("grade", "grade"), ("you", "2SG"), ("should", "should"), ("do", "do"), ("every", "every"), ("exercise", "exercise")]
    translation := "To get a perfect grade, you should do every exercise."
    context := "One can get a perfect grade by doing most exercises; doing all gives extra credit. QUD: What is a way to get a perfect grade?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("modal", "should"), ("qud", "way_to_perfect_grade")]
    comment := "UNVERIFIED paperLabel: example number carried from prior Lean file (shouldExceptionTolerance docstring), not checked against PDF. Migrated from shouldExceptionTolerance (acceptableUnderQUD1 = true): weak necessity tolerates QUD-irrelevant exceptions."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def should_exception_qud2 : LinguisticExample :=
  { id := "aghajeretic2022_should_exception_qud2"
    source := ⟨"agha-jeretic-2022", "(17) exception tolerance"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To get a perfect grade, you should do every exercise."
    discourseSegments := []
    glossedTokens := [("To", "to"), ("get", "get"), ("a", "INDEF"), ("perfect", "perfect"), ("grade", "grade"), ("you", "2SG"), ("should", "should"), ("do", "do"), ("every", "every"), ("exercise", "exercise")]
    translation := "To get a perfect grade, you should do every exercise."
    context := "One can get a perfect grade by doing most exercises; doing all gives extra credit. QUD: What are the minimal requirements to get a perfect grade?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("modal", "should"), ("qud", "minimal_requirements")]
    comment := "UNVERIFIED paperLabel: example number carried from prior Lean file, not checked against PDF. Migrated from shouldExceptionTolerance (acceptableUnderQUD2 = false): when the QUD makes the exceptions relevant, the exception-tolerant use is infelicitous."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def haveTo_exception_qud1 : LinguisticExample :=
  { id := "aghajeretic2022_haveTo_exception_qud1"
    source := ⟨"agha-jeretic-2022", "(17) exception tolerance"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To get a perfect grade, you have to do every exercise."
    discourseSegments := []
    glossedTokens := [("To", "to"), ("get", "get"), ("a", "INDEF"), ("perfect", "perfect"), ("grade", "grade"), ("you", "2SG"), ("have", "have"), ("to", "to"), ("do", "do"), ("every", "every"), ("exercise", "exercise")]
    translation := "To get a perfect grade, you have to do every exercise."
    context := "One can get a perfect grade by doing most exercises; doing all gives extra credit. QUD: What is a way to get a perfect grade?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("modal", "haveTo"), ("qud", "way_to_perfect_grade")]
    comment := "UNVERIFIED paperLabel: example number carried from prior Lean file (haveToExceptionTolerance docstring), not checked against PDF. Migrated from haveToExceptionTolerance (acceptableUnderQUD1 = false): strong necessity does not tolerate exceptions even when QUD-irrelevant."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def haveTo_exception_qud2 : LinguisticExample :=
  { id := "aghajeretic2022_haveTo_exception_qud2"
    source := ⟨"agha-jeretic-2022", "(17) exception tolerance"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "To get a perfect grade, you have to do every exercise."
    discourseSegments := []
    glossedTokens := [("To", "to"), ("get", "get"), ("a", "INDEF"), ("perfect", "perfect"), ("grade", "grade"), ("you", "2SG"), ("have", "have"), ("to", "to"), ("do", "do"), ("every", "every"), ("exercise", "exercise")]
    translation := "To get a perfect grade, you have to do every exercise."
    context := "One can get a perfect grade by doing most exercises; doing all gives extra credit. QUD: What are the minimal requirements to get a perfect grade?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("modal", "haveTo"), ("qud", "minimal_requirements")]
    comment := "UNVERIFIED paperLabel: example number carried from prior Lean file, not checked against PDF. Migrated from haveToExceptionTolerance (acceptableUnderQUD2 = false)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def should_indet_response : LinguisticExample :=
  { id := "aghajeretic2022_should_indet_response"
    source := ⟨"agha-jeretic-2022", "(19) well-responses to indeterminate sentences"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You should take the right door to go to the living room."
    discourseSegments := []
    glossedTokens := [("You", "2SG"), ("should", "should"), ("take", "take"), ("the", "DEF"), ("right", "right"), ("door", "door"), ("to", "to"), ("go", "go"), ("to", "to"), ("the", "DEF"), ("living", "living"), ("room", "room")]
    translation := "You should take the right door to go to the living room."
    context := "Two doors lead to the living room; both are equally good options."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "GAP"), ("modal", "should")]
    comment := "UNVERIFIED paperLabel: example number carried from prior Lean file (shouldIndeterminateResponse docstring), not checked against PDF. Migrated from shouldIndeterminateResponse: borderline (indeterminate) weak-necessity sentence — outright 'No' denial is infelicitous (noResponseFelicitous = false), a 'Well, ...' response is preferred (wellResponseFelicitous = true), paralleling plural definites."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def must_indet_response : LinguisticExample :=
  { id := "aghajeretic2022_must_indet_response"
    source := ⟨"agha-jeretic-2022", "(19) well-responses to indeterminate sentences"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You must take the right door to go to the living room."
    discourseSegments := []
    glossedTokens := [("You", "2SG"), ("must", "must"), ("take", "take"), ("the", "DEF"), ("right", "right"), ("door", "door"), ("to", "to"), ("go", "go"), ("to", "to"), ("the", "DEF"), ("living", "living"), ("room", "room")]
    translation := "You must take the right door to go to the living room."
    context := "Two doors lead to the living room; both are equally good options."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "positive"), ("condition", "GAP"), ("modal", "must")]
    comment := "UNVERIFIED paperLabel: example number carried from prior Lean file, not checked against PDF. Migrated from mustIndeterminateResponse: strong necessity is bivalent — grammatical and felicitous but judged false in this scenario, so outright 'No' denial is felicitous (noResponseFelicitous = true) and a 'Well, ...' response is not (wellResponseFelicitous = false)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [should_pos_all, should_pos_none, should_pos_gap, should_neg_all, should_neg_none, should_neg_gap, haveTo_pos_gap, haveTo_neg_gap, necessarily_removes_gap, should_exception_qud1, should_exception_qud2, haveTo_exception_qud1, haveTo_exception_qud2, should_indet_response, must_indet_response]

end AghaJeretic2022.Examples
