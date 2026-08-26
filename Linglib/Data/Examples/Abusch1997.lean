import Linglib.Data.Examples.Schema

/-!
# `Abusch1997` — typed example data

Auto-generated from `Linglib/Data/Examples/Abusch1997.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Abusch1997.Examples`.
-/

namespace Abusch1997.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "abusch1997_ex1"
    source := ⟨"abusch-1997", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The defendant was actually watching the Simpsons at the time of the crime. According to the testimony of the first eye-witness, the jurors clearly believed that he was in the laboratory building."
    discourseSegments := ["The defendant was actually watching the Simpsons at the time of the crime.", "According to the testimony of the first eye-witness, the jurors clearly believed that he was in the laboratory building."]
    glossedTokens := []
    translation := "The defendant was actually watching the Simpsons at the time of the crime. According to the testimony of the first eye-witness, the jurors clearly believed that he was in the laboratory building."
    context := "Past-shifted (backward-shifted) reading: the embedded `was` (in 'he was in the laboratory') is anaphoric to the time of the crime introduced in the first sentence. Time of the defendant being in the laboratory precedes the jurors' believing time. Abusch's diagnostic for the Independent Theory's anaphoric account of embedded past tense."
    judgment := .acceptable
    alternatives := []
    readings := [("past-shifted (defendant in lab before jurors' believing)", .acceptable)]
    paperFeatures := []
    comment := "Abusch 1997 ex (1), Linguistics and Philosophy 20 p. 2. Two-sentence discourse establishing the time-of-the-crime antecedent; the second sentence's embedded past picks up that antecedent rather than the matrix `believed` event. Cornerstone of the anaphoric (vs. SOT-deletion) account of past-under-past."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2 : LinguisticExample :=
  { id := "abusch1997_ex2"
    source := ⟨"abusch-1997", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary believed it was raining."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary believed it was raining."
    context := "Simultaneous reading. The embedded `was raining` is anaphoric to the matrix `believed`, yielding a reading where the raining is co-temporal with the believing. Abusch's contrast with (1): both readings derived by the Independent Theory via anaphora to different antecedents."
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (raining at believing time)", .acceptable), ("past-shifted (raining before believing)", .acceptable)]
    paperFeatures := []
    comment := "Abusch 1997 ex (2), p. 3. Footnote 2 attributes the simultaneous-reading shape to Enç 1987 (cited as 'Eng 1987'). Standard past-under-past minimal example."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex3_ULC : LinguisticExample :=
  { id := "abusch1997_ex3_ULC"
    source := ⟨"abusch-1997", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John found an ostrich in his apartment yesterday. Just before he opened the door, he thought that a burglar attacked him."
    discourseSegments := ["John found an ostrich in his apartment yesterday.", "Just before he opened the door, he thought that a burglar attacked him."]
    glossedTokens := []
    translation := "John found an ostrich in his apartment yesterday. Just before he opened the door, he thought that a burglar attacked him."
    context := "Upper Limit Constraint (ULC) foil. The Independent Theory would predict a forward-shifted reading (the attack co-temporal with the later opening, hence after the thinking) via anaphora to the previous sentence's time of opening, paraphrasable as 'When I open the door, a burglar will attack me'. This reading is UNAVAILABLE: embedded past cannot denote a time later than the matrix event. Motivates the §7 ULC."
    judgment := .acceptable
    alternatives := []
    readings := [("past-shifted (attack before thinking)", .acceptable), ("forward-shifted (attack co-temporal with later opening, after thinking)", .ungrammatical)]
    paperFeatures := []
    comment := "Abusch 1997 ex (3), p. 4. The decisive counterexample to the pure Independent Theory: the predicted forward-shifted reading (paraphrased by ex (4) 'When I open the door, a burglar will attack me') is unavailable. Motivates the Upper Limit Constraint: embedded R cannot exceed matrix E."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex8_doubleAccess : LinguisticExample :=
  { id := "abusch1997_ex8_doubleAccess"
    source := ⟨"abusch-1997", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed that Mary is pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "John believed that Mary is pregnant."
    context := "Double-access (present-under-past). The pregnancy must include BOTH the utterance time and John's believing time. The embedded present cannot have a purely future-shifted reading (despite the future-orientation usually available to present tense). Motivates Abusch's §3 de re analysis of the embedded present."
    judgment := .acceptable
    alternatives := []
    readings := [("double-access (pregnancy includes utterance + believing)", .acceptable), ("future-shifted (pregnancy only at believing, not utterance)", .ungrammatical)]
    paperFeatures := []
    comment := "Abusch 1997 ex (8), p. 5. Cornerstone present-under-past example. Sharvit 2003 ex (3) descends from this. The double-access constraint is one of two phenomena (alongside the ULC of ex 3) that the pure Independent Theory cannot derive; Abusch addresses both via de re belief + acquaintance relations."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex6 : LinguisticExample :=
  { id := "abusch1997_ex6"
    source := ⟨"abusch-1997", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John found an ostrich in his apartment yesterday. Just before he opened the door he thought that a burglar would attack him."
    discourseSegments := ["John found an ostrich in his apartment yesterday.", "Just before he opened the door he thought that a burglar would attack him."]
    glossedTokens := []
    translation := "John found an ostrich in his apartment yesterday. Just before he opened the door he thought that a burglar would attack him."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("forward-shifted (attack after thinking, co-temporal with the opening)", .acceptable)]
    paperFeatures := [("configuration", "would under past"), ("reading", "forward-shifted")]
    comment := "The forward-shifted reading (3) lacks is available with would: the past on would is anaphoric to the past on thought and woll orders the attack after it."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex27 : LinguisticExample :=
  { id := "abusch1997_ex27"
    source := ⟨"abusch-1997", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last Monday John believed that he was in Paris on Tuesday."
    discourseSegments := []
    glossedTokens := []
    translation := "Last Monday John believed that he was in Paris on Tuesday."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("backward-shifted (a previous Tuesday)", .acceptable), ("forward-shifted (the Tuesday after last Monday)", .unacceptable)]
    paperFeatures := [("phenomenon", "upper limit"), ("anaphora", "internal to the attitude")]
    comment := "Temporal anaphora internal to the belief context, beyond the reach of acquaintance relations; an upper limit phenomenon."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex29 : LinguisticExample :=
  { id := "abusch1997_ex29"
    source := ⟨"abusch-1997", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed he was in Paris at some time."
    discourseSegments := []
    glossedTokens := []
    translation := "John believed he was in Paris at some time."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("backward-shifted, narrow scope (some time before the believing)", .acceptable), ("forward-shifted, narrow scope", .unacceptable)]
    paperFeatures := [("phenomenon", "upper limit"), ("anaphora", "internal to the attitude")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex30 : LinguisticExample :=
  { id := "abusch1997_ex30"
    source := ⟨"abusch-1997", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue believed that she would marry a man who loved her."
    discourseSegments := []
    glossedTokens := []
    translation := "Sue believed that she would marry a man who loved her."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (loving at the marrying, after the believing)", .acceptable)]
    paperFeatures := [("phenomenon", "sequence of tense"), ("morphology", "past without precedence")]
    comment := "Past morphology on loved with no precedence relative to the utterance time: anaphora internal to the attitude, so not de re."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex34 : LinguisticExample :=
  { id := "abusch1997_ex34"
    source := ⟨"abusch-1997", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John decided a week ago that in ten days at breakfast he would say to his mother that they were having their last meal together."
    discourseSegments := []
    glossedTokens := []
    translation := "John decided a week ago that in ten days at breakfast he would say to his mother that they were having their last meal together."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous (meal at the saying, three days after the utterance)", .acceptable)]
    paperFeatures := [("phenomenon", "sequence of tense"), ("morphology", "past without precedence")]
    comment := "The meal time precedes no time mentioned in the sentence; a sequence-of-tense past licensed non-locally."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46a : LinguisticExample :=
  { id := "abusch1997_ex46a"
    source := ⟨"abusch-1997", "(46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary believed that John was afraid during the last thunderstorm."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary believed that John was afraid during the last thunderstorm."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "upper limit"), ("reading", "backward-shifted")]
    comment := "The past is determinate from an epistemic alternative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46b : LinguisticExample :=
  { id := "abusch1997_ex46b"
    source := ⟨"abusch-1997", "(46b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary believed that John was afraid during the next thunderstorm."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary believed that John was afraid during the next thunderstorm."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("forward-shifted (the thunderstorm after the believing)", .unacceptable)]
    paperFeatures := [("phenomenon", "upper limit"), ("reading", "forward-shifted")]
    comment := "The future branches across epistemic alternatives; the now of an alternative is an upper limit for tense denotation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex47 : LinguisticExample :=
  { id := "abusch1997_ex47"
    source := ⟨"abusch-1997", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leo will go to Rome on the day of Lea's dissertation defence. Lia believes that she will go with him then."
    discourseSegments := ["Leo will go to Rome on the day of Lea's dissertation defence.", "Lia believes that she will go with him then."]
    glossedTokens := []
    translation := "Leo will go to Rome on the day of Lea's dissertation defence. Lia believes that she will go with him then."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "future-directed acquaintance"), ("source", "Bonomi")]
    comment := "Anaphoric then under believes refers to a future time de re, refuting a constraint on acquaintance relations as the source of upper limit effects."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex53 : LinguisticExample :=
  { id := "abusch1997_ex53"
    source := ⟨"abusch-1997", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Five days ago, John promised to talk two weeks later about the topic that the participants were most interested in."
    discourseSegments := []
    glossedTokens := []
    translation := "Five days ago, John promised to talk two weeks later about the topic that the participants were most interested in."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow scope (interest at the seminar, after the utterance)", .acceptable), ("wide scope (a specific topic; interest before the utterance)", .acceptable)]
    paperFeatures := [("phenomenon", "sequence of tense"), ("sensitivity", "logical scope")]
    comment := "Non-local licensing of the relative-clause past is available only when the noun phrase scopes under the attitude."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex60 : LinguisticExample :=
  { id := "abusch1997_ex60"
    source := ⟨"abusch-1997", "(60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue expects to marry a man she met recently."
    discourseSegments := []
    glossedTokens := []
    translation := "Sue expects to marry a man she met recently."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("meeting before the marrying (locally licensed)", .acceptable)]
    paperFeatures := [("phenomenon", "local licensing"), ("matrix", "present")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex63 : LinguisticExample :=
  { id := "abusch1997_ex63"
    source := ⟨"abusch-1997", "(63)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue expects to marry a man she loved."
    discourseSegments := []
    glossedTokens := []
    translation := "Sue expects to marry a man she loved."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("loving before the marrying", .acceptable), ("simultaneous (loving at the marrying)", .unacceptable)]
    paperFeatures := [("phenomenon", "local licensing"), ("matrix", "present")]
    comment := "Under a present matrix neither relation can license a past coindexed with the marrying time."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex64 : LinguisticExample :=
  { id := "abusch1997_ex64"
    source := ⟨"abusch-1997", "(64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue will marry a man she met recently."
    discourseSegments := []
    glossedTokens := []
    translation := "Sue will marry a man she met recently."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("meeting before the marrying, possibly after the utterance", .acceptable)]
    paperFeatures := [("phenomenon", "local licensing"), ("operator", "will as evaluation-time shifter")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex69 : LinguisticExample :=
  { id := "abusch1997_ex69"
    source := ⟨"abusch-1997", "(69)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John said two weeks ago that Mary is pregnant but actually she has just been overeating for the last three months."
    discourseSegments := []
    glossedTokens := []
    translation := "John said two weeks ago that Mary is pregnant but actually she has just been overeating for the last three months."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "double access"), ("complement", "not true at either time")]
    comment := "The double access reading does not require the complement to hold at the believing time or the utterance time."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex81 : LinguisticExample :=
  { id := "abusch1997_ex81"
    source := ⟨"abusch-1997", "(81)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John believed that Mary was pregnant."
    discourseSegments := []
    glossedTokens := []
    translation := "John believed that Mary was pregnant."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("simultaneous", .acceptable)]
    paperFeatures := [("phenomenon", "double access"), ("alternative", "simultaneous past")]
    comment := "The pragmatically neutral report when Mary's symptom no longer persists at the utterance time."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex1, ex2, ex3_ULC, ex8_doubleAccess, ex6, ex27, ex29, ex30, ex34, ex46a, ex46b, ex47, ex53, ex60, ex63, ex64, ex69, ex81]

end Abusch1997.Examples
