module

public import Linglib.Data.Examples.Schema

/-!
# `VanDerSandtMaier2003` — typed example data

Auto-generated from `Linglib/Data/Examples/VanDerSandtMaier2003.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanDerSandtMaier2003.Examples`.
-/

@[expose] public section

namespace VanDerSandtMaier2003.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "vandersandtmaier2003_1"
    source := ⟨"van-der-sandt-maier-2003", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The King of France walks in the park. No, he doesn't, France doesn't have a king."
    discourseSegments := ["The King of France walks in the park.", "No, he doesn't,", "France doesn't have a king."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial", "presupposition"), ("sequence", "assertion-denial-correction")]
    comment := "Reverse anaphora moves the contribution of the first utterance under the negation of the denial; the result is that France has no king, (2)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "vandersandtmaier2003_3"
    source := ⟨"van-der-sandt-maier-2003", "(3)"⟩
    reportedIn := some ⟨"strawson-1952", ""⟩
    language := "stan1293"
    primaryText := "A man jumped off the bridge. He didn't jump, he was pushed."
    discourseSegments := ["A man jumped off the bridge.", "He didn't jump, he was pushed."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial", "proposition"), ("problem", "referent must survive")]
    comment := "The discourse referent of the first utterance must be retained to bind the pronoun, so the whole contribution cannot be removed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "vandersandtmaier2003_4"
    source := ⟨"van-der-sandt-maier-2003", "(4)"⟩
    reportedIn := some ⟨"geurts-1998", ""⟩
    language := "stan1293"
    primaryText := "The King of France knows I quit smoking. No he doesn't, France doesn't have a king."
    discourseSegments := ["The King of France knows I quit smoking.", "No he doesn't, France doesn't have a king."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial", "presupposition"), ("problem", "one of two presuppositions")]
    comment := "Only the presupposition that France has a king is objected to; that I quit smoking should pass unharmed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "vandersandtmaier2003_5"
    source := ⟨"van-der-sandt-maier-2003", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Now, THAT's a nice lady. Yes, she is, but she's not a LAdy, she's my WIfe."
    discourseSegments := ["Now, THAT's a nice lady.", "Yes, she is, but she's not a LAdy, she's my WIfe."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial", "implicature"), ("problem", "part acknowledged, part denied")]
    comment := "The second speaker confirms that the person is nice and denies the implicature of 'a lady' that she is a stranger."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9a : LinguisticExample :=
  { id := "vandersandtmaier2003_9a"
    source := ⟨"van-der-sandt-maier-2003", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible the Pope is right."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("layers", "pr: the Pope; fr: possibly right; imp: not necessarily right")]
    comment := "The preliminary layered representation (9b): the three layers share one reference marker."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20 : LinguisticExample :=
  { id := "vandersandtmaier2003_20"
    source := ⟨"van-der-sandt-maier-2003", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is possible the Pope is right. No, it's not POssible, it's NEcessary that he's right."
    discourseSegments := ["It is possible the Pope is right.", "No, it's not POssible,", "it's NEcessary that he's right."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial", "implicature"), ("off", "imp1")]
    comment := "Off(ψ, fr3) = {imp1}: the correction clashes only with the implicature that he is not necessarily right, which moves under the negation of the denial."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21 : LinguisticExample :=
  { id := "vandersandtmaier2003_21"
    source := ⟨"van-der-sandt-maier-2003", "(21)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Now, THAT's a nice lady. Yes, she is, but she's not a LAdy, she's my WIfe."
    discourseSegments := ["Now, THAT's a nice lady.", "Yes, she is,", "but she's not a LAdy,", "she's my WIfe."]
    glossedTokens := []
    translation := ""
    context := "Someone points at a woman."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial", "implicature"), ("off", "imp1"), ("sequence", "assertion-affirmation-denial-correction")]
    comment := "Off(ψ, fr4) = {imp1}: the stranger implicature moves under the negation; the acknowledged content that she is nice and the literal predication that she is a lady survive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def fn12 : LinguisticExample :=
  { id := "vandersandtmaier2003_fn12"
    source := ⟨"van-der-sandt-maier-2003", "footnote 12 (i)"⟩
    reportedIn := some ⟨"horn-1989", ""⟩
    language := "stan1293"
    primaryText := "They didn't call the POlice — they called the poLIce."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("denial", "register")]
    comment := "A style or register denial, which a layer for intonational and other surface features would accommodate."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_3, ex_4, ex_5, ex_9a, ex_20, ex_21, fn12]

end VanDerSandtMaier2003.Examples
