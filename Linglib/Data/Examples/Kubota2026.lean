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
    discourseSegments := []
    glossedTokens := [("Satō-iri-no", "sugar-put.in-GEN"), ("ryokucha-wa", "green.tea-TOP"), ("jitsu-ni", "real-ADV"), ("mooshi-bun-nai", "complaint-NEG"), ("mono-da-ga", "thing-COP-but"), ("watashi-wa", "I-TOP"), ("satō-iri-no", "sugar-put.in-GEN"), ("ryokucha", "green.tea"), ("nanka", "NANKA"), ("kesshite", "never"), ("nomanai", "drink-NEG")]
    translation := "Green tea with sugar is indeed impeccable, but I never drink such a thing."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "noncancelability"), ("contextStance", "positive")]
    comment := "The positive evaluation in the preceding clause contradicts the negative stance of nanka, and the stance cannot be cancelled: the evaluative meaning is conventional, not a Gricean inference." }

def ex11_mushiro_unexpected : LinguisticExample :=
  { id := "kubota2026_ex11_mushiro_unexpected"
    source := ⟨"kubota-2026", "(11)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Igai-na koto-ni, sunao-ni misu-o mitome-ta hō-ga mushiro yoi kekka-ni tsunagaru."
    discourseSegments := []
    glossedTokens := [("Igai-na", "unexpected-ADN"), ("koto-ni", "thing-DAT"), ("sunao-ni", "honest-ADV"), ("misu-o", "mistake-ACC"), ("mitome-ta", "admit-PAST"), ("hō-ga", "way-NOM"), ("mushiro", "rather"), ("yoi", "good"), ("kekka-ni", "result-DAT"), ("tsunagaru", "lead.to")]
    translation := "Unexpectedly, honestly admitting one's mistake leads (rather/#as expected) to a better outcome."
    context := ""
    judgment := .acceptable
    alternatives := [("Igai-na koto-ni, sunao-ni misu-o mitome-ta hō-ga yahari yoi kekka-ni tsunagaru.", .unacceptable)]
    readings := []
    paperFeatures := [("marker", "mushiro"), ("phenomenon", "noncancelability"), ("contextExpectation", "unexpected")]
    comment := "The contrary marker mushiro 'rather' is fine under 'unexpectedly'; yahari 'as expected' is not. The paper prints {mushiro/#yahari} 'rather/as.expected'." }

def ex12_yahari_expected : LinguisticExample :=
  { id := "kubota2026_ex12_yahari_expected"
    source := ⟨"kubota-2026", "(12)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Igai-na koto-wa nani-mo na-ku, sunao-ni misu-o mitome-ta hō-ga yahari yoi kekka-ni tsunagaru."
    discourseSegments := []
    glossedTokens := [("Igai-na", "unexpected"), ("koto-wa", "thing-TOP"), ("nani-mo", "nothing"), ("na-ku", "exist-NEG"), ("sunao-ni", "honestly"), ("misu-o", "mistake-ACC"), ("mitome-ta", "admit-PAST"), ("hō-ga", "way-NOM"), ("yahari", "after.all"), ("yoi", "good"), ("kekka-ni", "result-DAT"), ("tsunagaru", "lead")]
    translation := "Nothing surprising; frankly admitting your mistake leads (#rather/as expected) to better results."
    context := ""
    judgment := .acceptable
    alternatives := [("Igai-na koto-wa nani-mo na-ku, sunao-ni misu-o mitome-ta hō-ga mushiro yoi kekka-ni tsunagaru.", .unacceptable)]
    readings := []
    paperFeatures := [("marker", "yahari"), ("phenomenon", "noncancelability"), ("contextExpectation", "expected")]
    comment := "yahari 'as expected' is fine under 'nothing surprising'; the contrary marker mushiro is not. The paper prints {#mushiro/yahari} 'rather/after.all'." }

def ex37_nanka_counterstance : LinguisticExample :=
  { id := "kubota2026_ex37_nanka_counterstance"
    source := ⟨"kubota-2026", "(37)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "A: Satō-iri-no ryokucha-tte, oishii yo ne. B: Ge, amai mono-wa suki-da kedo, satō-iri-no ryokucha nanka zettai oishiku nai yo."
    discourseSegments := ["A: Satō-iri-no ryokucha-tte, oishii yo ne.", "B: Ge, amai mono-wa suki-da kedo, satō-iri-no ryokucha nanka zettai oishiku nai yo."]
    glossedTokens := []
    translation := "Sweetened green tea is tasty, isn't it? — Ugh, I do like sweets, but sweetened green tea is absolutely not tasty."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "counterstance"), ("priorMove", "evaluativeAssertion")]
    comment := "A's positive evaluation of sweetened green tea is the salient counterstance that licenses nanka." }

def ex38_nanka_no_counterstance : LinguisticExample :=
  { id := "kubota2026_ex38_nanka_no_counterstance"
    source := ⟨"kubota-2026", "(38)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "A: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na? B: Satō-iri-no ryokucha-nanka oishiku-nai-yo."
    discourseSegments := ["A: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na?", "B: Satō-iri-no ryokucha-nanka oishiku-nai-yo."]
    glossedTokens := []
    translation := "I wonder what kind of drink tastes good with sugar in it. — Sweetened green tea is not tasty (at all)."
    context := ""
    judgment := .questionable
    alternatives := [("A: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na? B: Satō-iri-no ryokucha-wa oishiku-nai-yo.", .acceptable)]
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "counterstance"), ("priorMove", "whQuestion")]
    comment := "The paper marks nanka with ?? here ({wa/??nanka}); the plain wa variant is fine. No counterstance is salient after a general wh-question. The paper prints ryokucha-{wa/??nanka} 'green.tea-TOP/NANKA'." }

def ex39_dose_q1 : LinguisticExample :=
  { id := "kubota2026_ex39_dose_q1"
    source := ⟨"kubota-2026", "(39), response to Q1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Q1: Satō-iri-no ryokucha-wa oishii-ka-na? A: Satō-iri-no ryokucha-wa dōse mazui yo."
    discourseSegments := ["Q1: Satō-iri-no ryokucha-wa oishii-ka-na?", "A: Satō-iri-no ryokucha-wa dōse mazui yo."]
    glossedTokens := []
    translation := "I wonder if sweetened green tea is tasty. — Sweetened green tea is untasty anyway."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "counterstance"), ("priorMove", "polarQuestion")]
    comment := "The polar question raises the issue whether sweetened green tea is tasty, which licenses dōse." }

def ex39_dose_q2 : LinguisticExample :=
  { id := "kubota2026_ex39_dose_q2"
    source := ⟨"kubota-2026", "(39), response to Q2"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Q2: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na? A: Satō-iri-no ryokucha-wa dōse mazui yo."
    discourseSegments := ["Q2: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na?", "A: Satō-iri-no ryokucha-wa dōse mazui yo."]
    glossedTokens := []
    translation := "I wonder what kind of drink tastes good with sugar in it. — Sweetened green tea is untasty anyway."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "counterstance"), ("priorMove", "whQuestion")]
    comment := "Same sentence as the response to Q1; infelicitous because no salient issue directly responded to by the prejacent is raised." }

def ex40_nanka_denial : LinguisticExample :=
  { id := "kubota2026_ex40_nanka_denial"
    source := ⟨"kubota-2026", "(40)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "A: Satō-iri-no ryokucha nanka watashi-wa noma-nai. B: Iya, sonna hazu-wa nai yo."
    discourseSegments := ["A: Satō-iri-no ryokucha nanka watashi-wa noma-nai.", "B: Iya, sonna hazu-wa nai yo."]
    glossedTokens := []
    translation := "I won't drink green tea with sugar or anything like that. — No, that can't be true."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "denial"), ("denialTarget", "prejacent")]
    comment := "B's denial means 'You'll drink it for sure', not 'You are not negative about green tea with sugar': the stance layer cannot be the target of a yes/no response." }

def ex41_dose_denial : LinguisticExample :=
  { id := "kubota2026_ex41_dose_denial"
    source := ⟨"kubota-2026", "(41)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "A: Watashi-ni-wa dōse kinmedaru-wa tor-e-nai. B: Iya, sonna hazu-wa nai yo."
    discourseSegments := ["A: Watashi-ni-wa dōse kinmedaru-wa tor-e-nai.", "B: Iya, sonna hazu-wa nai yo."]
    glossedTokens := []
    translation := "I can't win a gold medal anyway. — No, that can't be true."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "denial"), ("denialTarget", "prejacent")]
    comment := "B's denial means 'You have plenty of chances', not 'You aren't really so pessimistic'." }

def ex42_perspective_shift : LinguisticExample :=
  { id := "kubota2026_ex42_perspective_shift"
    source := ⟨"kubota-2026", "(42)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Sensei-wa boku-ga (dōse) SALT-ni(-nanka) tōra-nai-to omot-te-ta rashii."
    discourseSegments := []
    glossedTokens := [("Sensei-wa", "advisor-TOP"), ("boku-ga", "I-NOM"), ("(dōse)", "DŌSE"), ("SALT-ni(-nanka)", "SALT-DAT-NANKA"), ("tōra-nai-to", "pass-NEG-C"), ("omot-te-ta", "think-PST"), ("rashii", "seem")]
    translation := "My advisor seems to have thought I wouldn't possibly get accepted at SALT."
    context := "The speaker was confident their paper would be accepted; the advisor held a pessimistic view."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse+nanka"), ("phenomenon", "perspectiveShift"), ("perspectiveHolder", "attitudeHolder")]
    comment := "Under the attitude verb the pessimistic outlook can only be read as the advisor's, not the speaker's: outlook markers shift under embedding, unlike typical expressives. The paper brackets the embedded clause, [boku-ga … tōra-nai]-to, and adds 'The advisor had a negative/pessimistic outlook.'" }

def ex45a_nanka_epistemic : LinguisticExample :=
  { id := "kubota2026_ex45a_nanka_epistemic"
    source := ⟨"kubota-2026", "(45a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Konna tokoro ni nihonjin-nanka inai hazu da."
    discourseSegments := []
    glossedTokens := [("Konna", "such"), ("tokoro", "place"), ("ni", "LOC"), ("nihonjin-nanka", "Japanese-NANKA"), ("inai", "exist-NEG"), ("hazu", "supposed"), ("da", "COP")]
    translation := "There shouldn't be any Japanese people in a place like this."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "hazu"), ("modalFlavor", "epistemic"), ("evaluation", "neutral")]
    comment := "With the epistemic modal hazu the negative implication is comparatively neutral." }

def ex45b_nanka_ability : LinguisticExample :=
  { id := "kubota2026_ex45b_nanka_ability"
    source := ⟨"kubota-2026", "(45b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Watashi ni-wa kin medaru-nanka torenai."
    discourseSegments := []
    glossedTokens := [("Watashi", "I"), ("ni-wa", "DAT-TOP"), ("kin medaru-nanka", "gold.medal-NANKA"), ("torenai", "get-POT-NEG")]
    translation := "There's no way I can win a gold medal."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "-eru"), ("modalFlavor", "circumstantial"), ("evaluation", "neutral")]
    comment := "With the ability modal the negative implication is comparatively neutral, as with the epistemic case." }

def ex45c_nanka_deontic : LinguisticExample :=
  { id := "kubota2026_ex45c_nanka_deontic"
    source := ⟨"kubota-2026", "(45c)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tookyoo-ni-nanka ika-nai hō-ga yokat-ta."
    discourseSegments := []
    glossedTokens := [("Tookyoo-ni-nanka", "Tokyo-DAT-NANKA"), ("ika-nai", "go-NEG"), ("hō-ga", "way-NOM"), ("yokat-ta", "good-PST")]
    translation := "It would have been better not to go to Tokyo (of all places)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "hō-ga yokat-ta"), ("modalFlavor", "deontic"), ("evaluation", "pejorative")]
    comment := "With a priority modal the negative implication is clearly pejorative." }

def ex45d_nanka_bouletic : LinguisticExample :=
  { id := "kubota2026_ex45d_nanka_bouletic"
    source := ⟨"kubota-2026", "(45d)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Aisu kuriimu-nanka iranai."
    discourseSegments := []
    glossedTokens := [("Aisu kuriimu-nanka", "Ice.cream-NANKA"), ("iranai", "need-NEG")]
    translation := "I don't want such a thing as ice cream."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "iranai"), ("modalFlavor", "bouletic"), ("evaluation", "pejorative")]
    comment := "With a bouletic modal the negative implication is clearly pejorative." }

def ex46a_semete_epistemic : LinguisticExample :=
  { id := "kubota2026_ex46a_semete_epistemic"
    source := ⟨"kubota-2026", "(46a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kono-yoona tokoro-ni-wa semete Nihonjin-wa iru hazu-da."
    discourseSegments := []
    glossedTokens := [("Kono-yoona", "this-like"), ("tokoro-ni-wa", "place-LOC-TOP"), ("semete", "at.least"), ("Nihonjin-wa", "Japanese.top"), ("iru", "exist"), ("hazu-da", "should-COP")]
    translation := "In a place like this, there should at least be some Japanese people."
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "hazu"), ("modalFlavor", "epistemic")]
    comment := "The paper marks the sentence ??: semete is incompatible with the epistemic modal hazu." }

def ex46b_semete_ability : LinguisticExample :=
  { id := "kubota2026_ex46b_semete_ability"
    source := ⟨"kubota-2026", "(46b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Watashi-ni-wa semete dō-medaru-wa toreru."
    discourseSegments := []
    glossedTokens := [("Watashi-ni-wa", "I-DAT-TOP"), ("semete", "at.least"), ("dō-medaru-wa", "bronze-medal-TOP"), ("toreru", "obtain.can")]
    translation := "As for me, I can at least win a bronze medal."
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-eru"), ("modalFlavor", "circumstantial")]
    comment := "The paper marks the sentence ??: semete is incompatible with the ability modal -eru." }

def ex46c_semete_desiderative : LinguisticExample :=
  { id := "kubota2026_ex46c_semete_desiderative"
    source := ⟨"kubota-2026", "(46c)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Semete yobō-sesshu-wa uke-tai."
    discourseSegments := []
    glossedTokens := [("Semete", "at.least"), ("yobō-sesshu-wa", "vaccination-TOP"), ("uke-tai", "receive-want")]
    translation := "One should at least get vaccinated."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-tai"), ("modalFlavor", "bouletic")]
    comment := "semete with the desiderative -tai." }

def ex46d_semete_deontic : LinguisticExample :=
  { id := "kubota2026_ex46d_semete_deontic"
    source := ⟨"kubota-2026", "(46d)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Semete ryohi-wa harau-beki-da."
    discourseSegments := []
    glossedTokens := [("Semete", "at.least"), ("ryohi-wa", "travel.expenses-top"), ("harau-beki-da", "pay-should-COP")]
    translation := "At least we should cover the travel expenses."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-beki"), ("modalFlavor", "deontic")]
    comment := "semete with the deontic -beki." }

def all : List LinguisticExample := [ex10_nanka_noncancelable, ex11_mushiro_unexpected, ex12_yahari_expected, ex37_nanka_counterstance, ex38_nanka_no_counterstance, ex39_dose_q1, ex39_dose_q2, ex40_nanka_denial, ex41_dose_denial, ex42_perspective_shift, ex45a_nanka_epistemic, ex45b_nanka_ability, ex45c_nanka_deontic, ex45d_nanka_bouletic, ex46a_semete_epistemic, ex46b_semete_ability, ex46c_semete_desiderative, ex46d_semete_deontic]

end Kubota2026.Examples
