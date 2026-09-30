module

public import Linglib.Data.Examples.Schema

/-!
# `Kubota2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Kubota2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kubota2026.Examples`.
-/

@[expose] public section

namespace Kubota2026.Examples

open Data.Examples

def ex10_nanka_noncancelable : LinguisticExample :=
  { id := "kubota2026_ex10_nanka_noncancelable"
    source := ⟨"kubota-2026", "(10)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Satō-iri-no ryokucha-wa jitsu-ni mooshi-bun-nai mono-da-ga, watashi-wa satō-iri-no ryokucha nanka kesshite nomanai."
    glossedTokens := [("Satō-iri-no", "sugar-put.in-GEN"), ("ryokucha-wa", "green.tea-TOP"), ("jitsu-ni", "real-ADV"), ("mooshi-bun-nai", "complaint-NEG"), ("mono-da-ga", "thing-COP-but"), ("watashi-wa", "I-TOP"), ("satō-iri-no", "sugar-put.in-GEN"), ("ryokucha", "green.tea"), ("nanka", "NANKA"), ("kesshite", "never"), ("nomanai", "drink-NEG")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "noncancelability"), ("contextStance", "positive")] }

def ex11_mushiro_unexpected : LinguisticExample :=
  { id := "kubota2026_ex11_mushiro_unexpected"
    source := ⟨"kubota-2026", "(11)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Igai-na koto-ni, sunao-ni misu-o mitome-ta hō-ga mushiro yoi kekka-ni tsunagaru."
    glossedTokens := [("Igai-na", "unexpected-ADN"), ("koto-ni", "thing-DAT"), ("sunao-ni", "honest-ADV"), ("misu-o", "mistake-ACC"), ("mitome-ta", "admit-PAST"), ("hō-ga", "way-NOM"), ("mushiro", "rather"), ("yoi", "good"), ("kekka-ni", "result-DAT"), ("tsunagaru", "lead.to")]
    context := ""
    judgment := .acceptable
    alternatives := [("Igai-na koto-ni, sunao-ni misu-o mitome-ta hō-ga yahari yoi kekka-ni tsunagaru.", .unacceptable)]
    readings := []
    paperFeatures := [("marker", "mushiro"), ("phenomenon", "noncancelability"), ("contextExpectation", "unexpected")] }

def ex12_yahari_expected : LinguisticExample :=
  { id := "kubota2026_ex12_yahari_expected"
    source := ⟨"kubota-2026", "(12)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Igai-na koto-wa nani-mo na-ku, sunao-ni misu-o mitome-ta hō-ga yahari yoi kekka-ni tsunagaru."
    glossedTokens := [("Igai-na", "unexpected"), ("koto-wa", "thing-TOP"), ("nani-mo", "nothing"), ("na-ku", "exist-NEG"), ("sunao-ni", "honestly"), ("misu-o", "mistake-ACC"), ("mitome-ta", "admit-PAST"), ("hō-ga", "way-NOM"), ("yahari", "after.all"), ("yoi", "good"), ("kekka-ni", "result-DAT"), ("tsunagaru", "lead")]
    context := ""
    judgment := .acceptable
    alternatives := [("Igai-na koto-wa nani-mo na-ku, sunao-ni misu-o mitome-ta hō-ga mushiro yoi kekka-ni tsunagaru.", .unacceptable)]
    readings := []
    paperFeatures := [("marker", "yahari"), ("phenomenon", "noncancelability"), ("contextExpectation", "expected")] }

def ex37_nanka_counterstance : LinguisticExample :=
  { id := "kubota2026_ex37_nanka_counterstance"
    source := ⟨"kubota-2026", "(37)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "A: Satō-iri-no ryokucha-tte, oishii yo ne. B: Ge, amai mono-wa suki-da kedo, satō-iri-no ryokucha nanka zettai oishiku nai yo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "counterstance"), ("priorMove", "evaluativeAssertion")] }

def ex38_nanka_no_counterstance : LinguisticExample :=
  { id := "kubota2026_ex38_nanka_no_counterstance"
    source := ⟨"kubota-2026", "(38)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "A: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na? B: Satō-iri-no ryokucha-nanka oishiku-nai-yo."
    glossedTokens := []
    context := ""
    judgment := .questionable
    alternatives := [("A: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na? B: Satō-iri-no ryokucha-wa oishiku-nai-yo.", .acceptable)]
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "counterstance"), ("priorMove", "whQuestion")] }

def ex39_dose_q1 : LinguisticExample :=
  { id := "kubota2026_ex39_dose_q1"
    source := ⟨"kubota-2026", "(39), response to Q1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Q1: Satō-iri-no ryokucha-wa oishii-ka-na? A: Satō-iri-no ryokucha-wa dōse mazui yo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "counterstance"), ("priorMove", "polarQuestion")] }

def ex39_dose_q2 : LinguisticExample :=
  { id := "kubota2026_ex39_dose_q2"
    source := ⟨"kubota-2026", "(39), response to Q2"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Q2: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na? A: Satō-iri-no ryokucha-wa dōse mazui yo."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "counterstance"), ("priorMove", "whQuestion")] }

def ex40_nanka_denial : LinguisticExample :=
  { id := "kubota2026_ex40_nanka_denial"
    source := ⟨"kubota-2026", "(40)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "A: Satō-iri-no ryokucha nanka watashi-wa noma-nai. B: Iya, sonna hazu-wa nai yo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "denial"), ("denialTarget", "prejacent")] }

def ex41_dose_denial : LinguisticExample :=
  { id := "kubota2026_ex41_dose_denial"
    source := ⟨"kubota-2026", "(41)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "A: Watashi-ni-wa dōse kinmedaru-wa tor-e-nai. B: Iya, sonna hazu-wa nai yo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "denial"), ("denialTarget", "prejacent")] }

def ex42_perspective_shift : LinguisticExample :=
  { id := "kubota2026_ex42_perspective_shift"
    source := ⟨"kubota-2026", "(42)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Sensei-wa boku-ga (dōse) SALT-ni(-nanka) tōra-nai-to omot-te-ta rashii."
    glossedTokens := [("Sensei-wa", "advisor-TOP"), ("boku-ga", "I-NOM"), ("(dōse)", "DŌSE"), ("SALT-ni(-nanka)", "SALT-DAT-NANKA"), ("tōra-nai-to", "pass-NEG-C"), ("omot-te-ta", "think-PST"), ("rashii", "seem")]
    context := "The speaker was confident their paper would be accepted; the advisor held a pessimistic view."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse+nanka"), ("phenomenon", "perspectiveShift"), ("perspectiveHolder", "attitudeHolder")] }

def ex45a_nanka_epistemic : LinguisticExample :=
  { id := "kubota2026_ex45a_nanka_epistemic"
    source := ⟨"kubota-2026", "(45a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Konna tokoro ni nihonjin-nanka inai hazu da."
    glossedTokens := [("Konna", "such"), ("tokoro", "place"), ("ni", "LOC"), ("nihonjin-nanka", "Japanese-NANKA"), ("inai", "exist-NEG"), ("hazu", "supposed"), ("da", "COP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "hazu"), ("modalFlavor", "epistemic"), ("evaluation", "neutral")] }

def ex45b_nanka_ability : LinguisticExample :=
  { id := "kubota2026_ex45b_nanka_ability"
    source := ⟨"kubota-2026", "(45b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Watashi ni-wa kin medaru-nanka torenai."
    glossedTokens := [("Watashi", "I"), ("ni-wa", "DAT-TOP"), ("kin medaru-nanka", "gold.medal-NANKA"), ("torenai", "get-POT-NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "-eru"), ("modalFlavor", "circumstantial"), ("evaluation", "neutral")] }

def ex45c_nanka_deontic : LinguisticExample :=
  { id := "kubota2026_ex45c_nanka_deontic"
    source := ⟨"kubota-2026", "(45c)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tookyoo-ni-nanka ika-nai hō-ga yokat-ta."
    glossedTokens := [("Tookyoo-ni-nanka", "Tokyo-DAT-NANKA"), ("ika-nai", "go-NEG"), ("hō-ga", "way-NOM"), ("yokat-ta", "good-PST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "hō-ga yokat-ta"), ("modalFlavor", "deontic"), ("evaluation", "pejorative")] }

def ex45d_nanka_bouletic : LinguisticExample :=
  { id := "kubota2026_ex45d_nanka_bouletic"
    source := ⟨"kubota-2026", "(45d)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Aisu kuriimu-nanka iranai."
    glossedTokens := [("Aisu kuriimu-nanka", "Ice.cream-NANKA"), ("iranai", "need-NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "iranai"), ("modalFlavor", "bouletic"), ("evaluation", "pejorative")] }

def ex46a_semete_epistemic : LinguisticExample :=
  { id := "kubota2026_ex46a_semete_epistemic"
    source := ⟨"kubota-2026", "(46a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kono-yoona tokoro-ni-wa semete Nihonjin-wa iru hazu-da."
    glossedTokens := [("Kono-yoona", "this-like"), ("tokoro-ni-wa", "place-LOC-TOP"), ("semete", "at.least"), ("Nihonjin-wa", "Japanese.top"), ("iru", "exist"), ("hazu-da", "should-COP")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "hazu"), ("modalFlavor", "epistemic")] }

def ex46b_semete_ability : LinguisticExample :=
  { id := "kubota2026_ex46b_semete_ability"
    source := ⟨"kubota-2026", "(46b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Watashi-ni-wa semete dō-medaru-wa toreru."
    glossedTokens := [("Watashi-ni-wa", "I-DAT-TOP"), ("semete", "at.least"), ("dō-medaru-wa", "bronze-medal-TOP"), ("toreru", "obtain.can")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-eru"), ("modalFlavor", "circumstantial")] }

def ex46c_semete_desiderative : LinguisticExample :=
  { id := "kubota2026_ex46c_semete_desiderative"
    source := ⟨"kubota-2026", "(46c)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Semete yobō-sesshu-wa uke-tai."
    glossedTokens := [("Semete", "at.least"), ("yobō-sesshu-wa", "vaccination-TOP"), ("uke-tai", "receive-want")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-tai"), ("modalFlavor", "bouletic")] }

def ex46d_semete_deontic : LinguisticExample :=
  { id := "kubota2026_ex46d_semete_deontic"
    source := ⟨"kubota-2026", "(46d)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Semete ryohi-wa harau-beki-da."
    glossedTokens := [("Semete", "at.least"), ("ryohi-wa", "travel.expenses-top"), ("harau-beki-da", "pay-should-COP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-beki"), ("modalFlavor", "deontic")] }

def all : List LinguisticExample := [ex10_nanka_noncancelable, ex11_mushiro_unexpected, ex12_yahari_expected, ex37_nanka_counterstance, ex38_nanka_no_counterstance, ex39_dose_q1, ex39_dose_q2, ex40_nanka_denial, ex41_dose_denial, ex42_perspective_shift, ex45a_nanka_epistemic, ex45b_nanka_ability, ex45c_nanka_deontic, ex45d_nanka_bouletic, ex46a_semete_epistemic, ex46b_semete_ability, ex46c_semete_desiderative, ex46d_semete_deontic]

end Kubota2026.Examples
