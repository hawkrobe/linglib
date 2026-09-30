module

public import Linglib.Data.Examples.Schema

/-!
# `ZwickyPullum1983` — typed example data

Auto-generated from `Linglib/Data/Examples/ZwickyPullum1983.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ZwickyPullum1983.Examples`.
-/

@[expose] public section

namespace ZwickyPullum1983.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "zwickypullum1983_1a"
    source := ⟨"zwicky-pullum-1983", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She's gone"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clitic", "'s")]
    comment := "She is or has gone." }

def ex_1b : LinguisticExample :=
  { id := "zwickypullum1983_1b"
    source := ⟨"zwicky-pullum-1983", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They've all seen this movie before"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clitic", "'ve")]
    comment := "" }

def ex_2a : LinguisticExample :=
  { id := "zwickypullum1983_2a"
    source := ⟨"zwicky-pullum-1983", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The person I was talking to's going to be angry with me"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "A"), ("host", "preposition")]
    comment := "" }

def ex_2b : LinguisticExample :=
  { id := "zwickypullum1983_2b"
    source := ⟨"zwicky-pullum-1983", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The ball you hit's just broken my dining room window"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "A"), ("host", "verb")]
    comment := "" }

def ex_2c : LinguisticExample :=
  { id := "zwickypullum1983_2c"
    source := ⟨"zwicky-pullum-1983", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Any answer not entirely right's going to be marked as an error"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "A"), ("host", "adjective")]
    comment := "" }

def ex_2d : LinguisticExample :=
  { id := "zwickypullum1983_2d"
    source := ⟨"zwicky-pullum-1983", "(2d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The drive home tonight's been really easy"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "A"), ("host", "adverb")]
    comment := "" }

def ex_3 : LinguisticExample :=
  { id := "zwickypullum1983_3"
    source := ⟨"zwicky-pullum-1983", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'd've done it if you'd asked me"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "F")]
    comment := "The clitic 've attaches to material already containing the clitic 'd." }

def ex_4a : LinguisticExample :=
  { id := "zwickypullum1983_4a"
    source := ⟨"zwicky-pullum-1983", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You haven't been here"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("morpheme", "-n't")]
    comment := "" }

def ex_4b : LinguisticExample :=
  { id := "zwickypullum1983_4b"
    source := ⟨"zwicky-pullum-1983", "(4b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Haven't you been there?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "E")]
    comment := "Subject-auxiliary inversion carries the contracted negator with the auxiliary." }

def ex_5 : LinguisticExample :=
  { id := "zwickypullum1983_5"
    source := ⟨"zwicky-pullum-1983", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You have not been there"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def ex_6 : LinguisticExample :=
  { id := "zwickypullum1983_6"
    source := ⟨"zwicky-pullum-1983", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have not you been there?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "E")]
    comment := "The uncontracted counterpart of (4b) is out." }

def ex_7a : LinguisticExample :=
  { id := "zwickypullum1983_7a"
    source := ⟨"zwicky-pullum-1983", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you been there?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def ex_7b : LinguisticExample :=
  { id := "zwickypullum1983_7b"
    source := ⟨"zwicky-pullum-1983", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Have you not been there?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def ex_8a : LinguisticExample :=
  { id := "zwickypullum1983_8a"
    source := ⟨"zwicky-pullum-1983", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You could've been there"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clitic", "'ve")]
    comment := "" }

def ex_8b : LinguisticExample :=
  { id := "zwickypullum1983_8b"
    source := ⟨"zwicky-pullum-1983", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Could've you been there?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "E")]
    comment := "Inversion cannot carry the clitic 've with the auxiliary." }

def ex_9 : LinguisticExample :=
  { id := "zwickypullum1983_9"
    source := ⟨"zwicky-pullum-1983", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'dn't be doing this unless I had to"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "F")]
    comment := "-n't cannot attach to material containing the clitic 'd." }

def ex_10a : LinguisticExample :=
  { id := "zwickypullum1983_10a"
    source := ⟨"zwicky-pullum-1983", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wouldn't be doing this unless I had to"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def ex_10b : LinguisticExample :=
  { id := "zwickypullum1983_10b"
    source := ⟨"zwicky-pullum-1983", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'd not be doing this unless I had to"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def ex_12a : LinguisticExample :=
  { id := "zwickypullum1983_12a"
    source := ⟨"zwicky-pullum-1983", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It would be a shame to have not ever had a chance to see it"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "A")]
    comment := "" }

def ex_12b : LinguisticExample :=
  { id := "zwickypullum1983_12b"
    source := ⟨"zwicky-pullum-1983", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It would be a shame to haven't ever had a chance to see it"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "A")]
    comment := "-n't attaches only to finite auxiliaries." }

def ex_13a : LinguisticExample :=
  { id := "zwickypullum1983_13a"
    source := ⟨"zwicky-pullum-1983", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The police have not been informed"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def ex_13b : LinguisticExample :=
  { id := "zwickypullum1983_13b"
    source := ⟨"zwicky-pullum-1983", "(13b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The police haven't been informed"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def ex_14a : LinguisticExample :=
  { id := "zwickypullum1983_14a"
    source := ⟨"zwicky-pullum-1983", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Would the police have not been informed?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "" }

def ex_14b : LinguisticExample :=
  { id := "zwickypullum1983_14b"
    source := ⟨"zwicky-pullum-1983", "(14b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Would the police haven't been informed?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "A")]
    comment := "" }

def ex_15a : LinguisticExample :=
  { id := "zwickypullum1983_15a"
    source := ⟨"zwicky-pullum-1983", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A good Christian can not attend church and still be saved"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "D"), ("reading", "CAN(NOT(P))")]
    comment := "With stressed, separated not: non-attendance can be forgiven." }

def ex_15b : LinguisticExample :=
  { id := "zwickypullum1983_15b"
    source := ⟨"zwicky-pullum-1983", "(15b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A good Christian can't attend church and still be saved"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "D"), ("reading", "NOT(CAN(P))")]
    comment := "The contracted form denies the possibility." }

def ex_16a : LinguisticExample :=
  { id := "zwickypullum1983_16a"
    source := ⟨"zwicky-pullum-1983", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Well, I just would not not sunbathe on such a beautiful day"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "D")]
    comment := "" }

def ex_16b : LinguisticExample :=
  { id := "zwickypullum1983_16b"
    source := ⟨"zwicky-pullum-1983", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "When he's nervous, he can't not smoke"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "D")]
    comment := "" }

def ex_17 : LinguisticExample :=
  { id := "zwickypullum1983_17"
    source := ⟨"zwicky-pullum-1983", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Could this group of sixteen energetic youngsters not travel down the Colorado in a bark canoe?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("criterion", "D")]
    comment := "Ambiguous between denying the possibility of the trip and asking whether they can avoid it." }

def all : List LinguisticExample := [ex_1a, ex_1b, ex_2a, ex_2b, ex_2c, ex_2d, ex_3, ex_4a, ex_4b, ex_5, ex_6, ex_7a, ex_7b, ex_8a, ex_8b, ex_9, ex_10a, ex_10b, ex_12a, ex_12b, ex_13a, ex_13b, ex_14a, ex_14b, ex_15a, ex_15b, ex_16a, ex_16b, ex_17]

end ZwickyPullum1983.Examples
