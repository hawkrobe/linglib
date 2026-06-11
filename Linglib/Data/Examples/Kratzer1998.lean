import Linglib.Data.Examples.Schema

/-!
# `Kratzer1998` — typed example data

Auto-generated from `Linglib/Data/Examples/Kratzer1998.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kratzer1998.Examples`.
-/

namespace Kratzer1998.Examples

open Data.Examples

def ex01 : LinguisticExample :=
  { id := "kratzer1998_ex01"
    source := ⟨"abusch-1988", "WCCFL 7 SOT example"⟩
    reportedIn := some ⟨"kratzer-1998", "(1)"⟩
    language := "stan1293"
    primaryText := "John decided a week ago that in ten days he would say to his mother that they were having their last meal together."
    discourseSegments := []
    glossedTokens := []
    translation := "John decided a week ago that in ten days he would say to his mother that they were having their last meal together."
    context := "Showcases that the underlined past tense \"were\" need not be interpreted as semantically past — the meal time is in the future of utterance, not the past."
    judgment := .acceptable
    alternatives := []
    readings := [("uninterpreted-past (SOT)", .acceptable)]
    paperFeatures := []
    comment := "Kratzer's plot example (1). The point: a past tense morpheme can fail to make any semantic contribution beyond agreeing with a higher past. Section 1, p. 1."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex02 : LinguisticExample :=
  { id := "kratzer1998_ex02"
    source := ⟨"ogihara-1989", "dissertation SOT example"⟩
    reportedIn := some ⟨"kratzer-1998", "(2)"⟩
    language := "stan1293"
    primaryText := "John said he would buy a fish that was still alive."
    discourseSegments := []
    glossedTokens := []
    translation := "John said he would buy a fish that was still alive."
    context := "Past tense \"was\" inside the future-complement \"would buy\" — the alive-time is the future buying time, not the saying-time and not the utterance time."
    judgment := .acceptable
    alternatives := []
    readings := [("alive-at-buying (later-than-saying)", .acceptable), ("alive-at-saying", .acceptable)]
    paperFeatures := []
    comment := "Kratzer's plot example (2), reported from Ogihara 1989. Ambiguity highlights non-pronominal use of past. Section 1, p. 1."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex03 : LinguisticExample :=
  { id := "kratzer1998_ex03"
    source := ⟨"kratzer-1998", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary predicted that she would know that she was pregnant the minute she got pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary predicted that she would know that she was pregnant the minute she got pregnant."
    context := "Multi-embedded SOT with two underlined past forms (\"was\", \"got\") both referring to future-of-utterance times."
    judgment := .acceptable
    alternatives := []
    readings := [("pregnancy-at-knowing (future-of-utterance)", .acceptable)]
    paperFeatures := []
    comment := "Kratzer's plot example (3). The minute-clause shows even adjunct past morphology can be SOT'd. Section 1, p. 1."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex05 : LinguisticExample :=
  { id := "kratzer1998_ex05"
    source := ⟨"kratzer-1998", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He will marry a woman who went to Harvard."
    discourseSegments := []
    glossedTokens := []
    translation := "He will marry a woman who went to Harvard."
    context := "Out of the blue. The past tense \"went\" refers to a time before utterance, but unlike (1)-(3) it cannot be pronominal-bound — there is no higher past to agree with."
    judgment := .acceptable
    alternatives := []
    readings := [("going-to-Harvard at past-of-utterance", .acceptable)]
    paperFeatures := []
    comment := "Kratzer's \"major obstacle\" example (5), Section 1, p. 2: not all past tenses can be analyzed as pronouns. Motivates the perfect-aspect-as-operator move in Section 7."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex29 : LinguisticExample :=
  { id := "kratzer1998_ex29"
    source := ⟨"kratzer-1998", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thinks that it is 10 o'clock."
    discourseSegments := []
    glossedTokens := []
    translation := "John thinks that it is 10 o'clock."
    context := "Uttered at, say, 11 o'clock. John self-locates at 10 o'clock; his belief is not that the time of utterance is 10."
    judgment := .acceptable
    alternatives := []
    readings := [("de se (John self-locates at 10)", .acceptable), ("indexical (John thinks 11 is 10)", .marginal)]
    paperFeatures := []
    comment := "Kratzer's temporal de se example (29), Section 5, p. 11. Attributed to v. Stechow 1982."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex30 : LinguisticExample :=
  { id := "kratzer1998_ex30"
    source := ⟨"kratzer-1998", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thinks that he has a headache."
    discourseSegments := []
    glossedTokens := []
    translation := "John thinks that he has a headache."
    context := "Embedded present-under-present. John self-locates at a time when he has a headache."
    judgment := .acceptable
    alternatives := []
    readings := [("de se (headache at John's now)", .acceptable)]
    paperFeatures := []
    comment := "Kratzer's example (30), Section 5, p. 11: even non-dramatic embedded tense gets a de se interpretation."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex32a : LinguisticExample :=
  { id := "kratzer1998_ex32a"
    source := ⟨"kratzer-1998", "(32a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John bought a fish that was still alive."
    discourseSegments := []
    glossedTokens := []
    translation := "John bought a fish that was still alive."
    context := "Relative clause past tense under a matrix past. The relative-clause tense can be zero-bound (simultaneous with buying) or independently past."
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (alive-at-buying, zero tense in RC)", .acceptable), ("independent past (alive-before-buying, past in RC)", .acceptable)]
    paperFeatures := []
    comment := "Kratzer's example (32a), Section 5, p. 13. RC tense is structurally optional in a way SOT complement-tense is not."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex33a : LinguisticExample :=
  { id := "kratzer1998_ex33a"
    source := ⟨"kratzer-1998", "(33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said he would buy a fish that was still alive."
    discourseSegments := []
    glossedTokens := []
    translation := "John said he would buy a fish that was still alive."
    context := "Same surface form as (2)/ex02, re-analyzed in Section 5 with zero-tense in the RC. Kratzer's own multi-LF variant (not attributed to Ogihara below this ex number in the paper)."
    judgment := .acceptable
    alternatives := []
    readings := [("RC zero-tense (alive-at-buying)", .acceptable), ("RC past-tense (alive-at-saying)", .acceptable)]
    paperFeatures := []
    comment := "Kratzer's example (33a), Section 5, p. 13. Two LFs for the RC tense — zero-tense bound at the buying time, or genuine past bound at the saying time."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex34a : LinguisticExample :=
  { id := "kratzer1998_ex34a"
    source := ⟨"kratzer-1998", "(34a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought two days ago that you would be sick yesterday."
    discourseSegments := []
    glossedTokens := []
    translation := "John thought two days ago that you would be sick yesterday."
    context := "Sickness is at yesterday (between thought-time two-days-ago and utterance). \"Would\" makes the relative future-from-thought reachable."
    judgment := .acceptable
    alternatives := []
    readings := [("sickness-at-yesterday (de re past)", .acceptable)]
    paperFeatures := []
    comment := "Kratzer's example (34a), Section 5, p. 13. Contrasts minimally with (35a) below."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex35a : LinguisticExample :=
  { id := "kratzer1998_ex35a"
    source := ⟨"kratzer-1998", "(35a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John thought two days ago that you were sick yesterday."
    discourseSegments := []
    glossedTokens := []
    translation := "John thought two days ago that you were sick yesterday."
    context := "Without \"would\", the embedded past forces sickness at the thought-time (two days ago), which conflicts with the adverbial \"yesterday\"."
    judgment := .ungrammatical
    alternatives := []
    readings := [("sickness-at-thought-time", .ungrammatical)]
    paperFeatures := []
    comment := "Kratzer's example (35a), Section 5, p. 13. Star is Kratzer's. Illustrates the minimal de re vs SOT contrast."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex36a : LinguisticExample :=
  { id := "kratzer1998_ex36a"
    source := ⟨"kratzer-1998", "(36a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ultrasound picture indicated that Mary is pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "The ultrasound picture indicated that Mary is pregnant."
    context := "Past matrix with present embedded. Embedded present can be de re about a present state of Mary that the past ultrasound picture is about."
    judgment := .marginal
    alternatives := []
    readings := [("de re on present state", .marginal)]
    paperFeatures := []
    comment := "Kratzer's example (36a), Section 6, p. 14. \"Marginal for many speakers\" per Kratzer; some speakers accept readily."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex36b : LinguisticExample :=
  { id := "kratzer1998_ex36b"
    source := ⟨"kratzer-1998", "(36b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ultrasound picture indicated of a present state of Mary's that it is a pregnancy."
    discourseSegments := []
    glossedTokens := []
    translation := "The ultrasound picture indicated of a present state of Mary's that it is a pregnancy."
    context := "Ogihara-style paraphrase that makes the temporal de re explicit."
    judgment := .acceptable
    alternatives := []
    readings := [("de re on present state (explicit)", .acceptable)]
    paperFeatures := []
    comment := "Kratzer's example (36b), Section 6, p. 14."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex40a : LinguisticExample :=
  { id := "kratzer1998_ex40a"
    source := ⟨"kratzer-1998", "(40a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who built this Church? Borromini built this church."
    discourseSegments := ["Who built this Church?", "Borromini built this church."]
    glossedTokens := []
    translation := "Who built this Church? Borromini built this church."
    context := "Looking at churches in Italy, no previous discourse. English simple past acceptable out of the blue."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Kratzer's example (40a), Section 7, p. 16. Cornerstone of the deictic-vs-anaphoric contrast: English simple past does not require a contextually salient past time."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex40b : LinguisticExample :=
  { id := "kratzer1998_ex40b"
    source := ⟨"kratzer-1998", "(40b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wer baute diese Kirche? Borromini baute diese Kirche."
    discourseSegments := ["Wer baute diese Kirche?", "Borromini baute diese Kirche."]
    glossedTokens := [("Wer", "who"), ("baute", "build.PST.3SG"), ("diese", "DEM.ACC.SG.F"), ("Kirche", "church"), ("Borromini", "Borromini"), ("baute", "build.PST.3SG"), ("diese", "DEM.ACC.SG.F"), ("Kirche", "church")]
    translation := "Who built this church? Borromini built this church."
    context := "Looking at churches in Italy, no previous discourse. German simple past (Präteritum) infelicitous out of the blue."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Kratzer's example (40b), Section 7, p. 16. Star is Kratzer's. Per Kratzer: \"At best, it sounds like the hypercorrect utterance of a South German speaker.\" Cornerstone of the deictic-vs-anaphoric Preterit asymmetry."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex40c : LinguisticExample :=
  { id := "kratzer1998_ex40c"
    source := ⟨"kratzer-1998", "(40c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wer hat diese Kirche gebaut? Borromini hat diese Kirche gebaut."
    discourseSegments := ["Wer hat diese Kirche gebaut?", "Borromini hat diese Kirche gebaut."]
    glossedTokens := [("Wer", "who"), ("hat", "have.AUX.PRS.3SG"), ("diese", "DEM.ACC.SG.F"), ("Kirche", "church"), ("gebaut", "build.PTCP"), ("Borromini", "Borromini"), ("hat", "have.AUX.PRS.3SG"), ("diese", "DEM.ACC.SG.F"), ("Kirche", "church"), ("gebaut", "build.PTCP")]
    translation := "Who has this church built? Borromini has this church built."
    context := "Same out-of-the-blue Italy-church scenario. Standard German Perfekt is felicitous where simple past is not."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Kratzer's example (40c), Section 7, p. 16. The Perfekt fills the deictic-past slot that the Preterit cannot. Supports Kratzer's decomposition: English simple past = perfect-aspect + present-tense."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex41a : LinguisticExample :=
  { id := "kratzer1998_ex41a"
    source := ⟨"kratzer-1998", "(41a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We will answer every letter that we got."
    discourseSegments := []
    glossedTokens := []
    translation := "We will answer every letter that we got."
    context := "English simple past in a relative clause inside a future matrix. Felicitous even without a contextually salient past interval."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Kratzer's example (41a), Section 7, p. 16. English simple past = perfect tolerated in embedded sentences."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex41b : LinguisticExample :=
  { id := "kratzer1998_ex41b"
    source := ⟨"kratzer-1998", "(41b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wir werden jeden Brief beantworten, den wir bekamen."
    discourseSegments := []
    glossedTokens := [("Wir", "we"), ("werden", "will.AUX.PRS.1PL"), ("jeden", "every.ACC.SG.M"), ("Brief", "letter"), ("beantworten", "answer.INF"), ("den", "REL.ACC.SG.M"), ("wir", "we"), ("bekamen", "receive.PST.1PL")]
    translation := "We will answer every letter that we received."
    context := "Same content as (41a) in Standard German Präteritum. Needs a contextually salient past time to be acceptable."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Kratzer's example (41b), Section 7, p. 16. Per Kratzer: \"needs a contextually salient past time to be acceptable\" — directly diagnoses the anaphoric requirement."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex41c : LinguisticExample :=
  { id := "kratzer1998_ex41c"
    source := ⟨"kratzer-1998", "(41c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Wir werden jeden Brief beantworten, den wir bekommen haben."
    discourseSegments := []
    glossedTokens := [("Wir", "we"), ("werden", "will.AUX.PRS.1PL"), ("jeden", "every.ACC.SG.M"), ("Brief", "letter"), ("beantworten", "answer.INF"), ("den", "REL.ACC.SG.M"), ("wir", "we"), ("bekommen", "receive.PTCP"), ("haben", "have.AUX.PRS.1PL")]
    translation := "We will answer every letter that we have received."
    context := "Same content as (41a/b) but with German Perfekt in the RC. Felicitous without a salient past time."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Kratzer's example (41c), Section 7, p. 16. The Perfekt slot again fills in for the missing deictic Preterit."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex42a : LinguisticExample :=
  { id := "kratzer1998_ex42a"
    source := ⟨"kratzer-1998", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John dreamed about eating a fish that he caught himself."
    discourseSegments := []
    glossedTokens := []
    translation := "John dreamed about eating a fish that he caught himself."
    context := "RC past \"caught\" can have either an anaphoric reading (relative to the dream-time) or an independent backward-shifted reading."
    judgment := .acceptable
    alternatives := []
    readings := [("anaphoric (caught-before-dreaming)", .acceptable), ("backward-shifted (caught-before-eating)", .acceptable)]
    paperFeatures := []
    comment := "Kratzer's example (42a), Section 7, p. 16-17. Per Kratzer: \"Underlined past tense does not have to be anaphoric.\""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex42b : LinguisticExample :=
  { id := "kratzer1998_ex42b"
    source := ⟨"kratzer-1998", "(42b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hans träumte davon, einen Fisch zu essen, den er selber fing."
    discourseSegments := []
    glossedTokens := [("Hans", "Hans"), ("träumte", "dream.PST.3SG"), ("davon", "R.of"), ("einen", "INDEF.ACC.SG.M"), ("Fisch", "fish"), ("zu", "INF.PRT"), ("essen", "eat.INF"), ("den", "REL.ACC.SG.M"), ("er", "he"), ("selber", "INTENS"), ("fing", "catch.PST.3SG")]
    translation := "Hans dreamed about eating a fish that he himself caught."
    context := "Same content as (42a) with German Präteritum in the RC. Per Kratzer, the past tense must be anaphoric (no backward-shifted reading)."
    judgment := .acceptable
    alternatives := []
    readings := [("anaphoric (caught-at-dreaming-time)", .acceptable), ("backward-shifted (caught-before-eating)", .unacceptable)]
    paperFeatures := []
    comment := "Kratzer's example (42b), Section 7, p. 16-17. Per Kratzer: \"Underlined past tense must be anaphoric.\" The backward-shifted reading is an interpretation gap (unavailable LF), not a string ill-formedness — hence `unacceptable` rather than `ungrammatical`."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex42c : LinguisticExample :=
  { id := "kratzer1998_ex42c"
    source := ⟨"kratzer-1998", "(42c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Hans träumte davon, einen Fisch zu essen, den er selber gefangen hatte."
    discourseSegments := []
    glossedTokens := [("Hans", "Hans"), ("träumte", "dream.PST.3SG"), ("davon", "R.of"), ("einen", "INDEF.ACC.SG.M"), ("Fisch", "fish"), ("zu", "INF.PRT"), ("essen", "eat.INF"), ("den", "REL.ACC.SG.M"), ("er", "he"), ("selber", "INTENS"), ("gefangen", "catch.PTCP"), ("hatte", "have.AUX.PST.3SG")]
    translation := "Hans dreamed about eating a fish that he had caught himself."
    context := "To recover the backward-shifted reading in German, the past perfect (Plusquamperfekt) is required."
    judgment := .acceptable
    alternatives := []
    readings := [("backward-shifted (caught-before-eating)", .acceptable)]
    paperFeatures := []
    comment := "Kratzer's example (42c), Section 7, p. 17. Past perfect fills the backward-shifted slot that the bare Preterit cannot. NB: Kratzer's free English translation in the PDF reads \"catching\" (typo for \"eating\"); the German `einen Fisch zu essen` is unambiguously \"to eat a fish\", with the catching in the RC `den er selber gefangen hatte`. Translation here reflects the German."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex01, ex02, ex03, ex05, ex29, ex30, ex32a, ex33a, ex34a, ex35a, ex36a, ex36b, ex40a, ex40b, ex40c, ex41a, ex41b, ex41c, ex42a, ex42b, ex42c]

end Kratzer1998.Examples
