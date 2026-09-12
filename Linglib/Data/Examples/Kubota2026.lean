import Linglib.Data.Examples.Schema

/-!
# `Kubota2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Kubota2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Kubota2026.Examples`.
-/

namespace Kubota2026.Examples

open Data.Examples

def ex10_nanka_noncancelable : LinguisticExample :=
  { id := "kubota2026_ex10_nanka_noncancelable"
    source := ⟨"kubota-2026", "(10)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Satō-iri-no ryokucha-wa jitsu-ni mooshi-bun-nai mono-da-ga, watashi-wa satō-iri-no ryokucha nanka kesshite nomanai."
    discourseSegments := []
    glossedTokens := []
    translation := "Green tea with sugar is indeed impeccable, but I never drink such a thing."
    context := "The preceding clause of the same sentence praises green tea with sugar."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "noncancelability"), ("contextStance", "positive")]
    comment := "The positive evaluation in the preceding clause contradicts the negative stance of nanka, and the stance cannot be cancelled: the evaluative meaning is conventional, not a Gricean inference."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11_mushiro_unexpected : LinguisticExample :=
  { id := "kubota2026_ex11_mushiro_unexpected"
    source := ⟨"kubota-2026", "(11)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Igai-na koto-ni, sunao-ni misu-o mitome-ta hō-ga mushiro yoi kekka-ni tsunagaru."
    discourseSegments := []
    glossedTokens := []
    translation := "Unexpectedly, honestly admitting one's mistake leads (rather) to a better outcome."
    context := "The sentence-initial adverbial marks the outcome as unexpected."
    judgment := .acceptable
    alternatives := [("Igai-na koto-ni, sunao-ni misu-o mitome-ta hō-ga yahari yoi kekka-ni tsunagaru.", .unacceptable)]
    readings := []
    paperFeatures := [("marker", "mushiro"), ("phenomenon", "noncancelability"), ("contextExpectation", "unexpected")]
    comment := "The contrary marker mushiro 'rather' is fine under 'unexpectedly'; yahari 'as expected' is not."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex12_yahari_expected : LinguisticExample :=
  { id := "kubota2026_ex12_yahari_expected"
    source := ⟨"kubota-2026", "(12)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Igai-na koto-wa nani-mo na-ku, sunao-ni misu-o mitome-ta hō-ga yahari yoi kekka-ni tsunagaru."
    discourseSegments := []
    glossedTokens := []
    translation := "Nothing surprising; frankly admitting your mistake leads (as expected) to better results."
    context := "The sentence-initial adverbial marks the outcome as expected."
    judgment := .acceptable
    alternatives := [("Igai-na koto-wa nani-mo na-ku, sunao-ni misu-o mitome-ta hō-ga mushiro yoi kekka-ni tsunagaru.", .unacceptable)]
    readings := []
    paperFeatures := [("marker", "yahari"), ("phenomenon", "noncancelability"), ("contextExpectation", "expected")]
    comment := "yahari 'as expected' is fine under 'nothing surprising'; the contrary marker mushiro is not."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex37_nanka_counterstance : LinguisticExample :=
  { id := "kubota2026_ex37_nanka_counterstance"
    source := ⟨"kubota-2026", "(37)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ge, amai mono-wa suki-da kedo, satō-iri-no ryokucha nanka zettai oishiku nai yo."
    discourseSegments := ["A: Satō-iri-no ryokucha-tte, oishii yo ne.", "B: Ge, amai mono-wa suki-da kedo, satō-iri-no ryokucha nanka zettai oishiku nai yo."]
    glossedTokens := []
    translation := "Ugh, I do like sweets, but sweetened green tea is absolutely not tasty."
    context := "A has just asserted a positive evaluation: 'Sweetened green tea is tasty, isn't it?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "counterstance"), ("priorMove", "evaluativeAssertion")]
    comment := "A's positive evaluation of sweetened green tea is the salient counterstance that licenses nanka."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex38_nanka_no_counterstance : LinguisticExample :=
  { id := "kubota2026_ex38_nanka_no_counterstance"
    source := ⟨"kubota-2026", "(38)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Satō-iri-no ryokucha nanka oishiku-nai-yo."
    discourseSegments := ["A: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na?", "B: Satō-iri-no ryokucha nanka oishiku-nai-yo."]
    glossedTokens := []
    translation := "Sweetened green tea is not tasty (at all)."
    context := "A has asked a general wh-question, 'I wonder what kind of drink tastes good with sugar in it': whether sweetened green tea is tasty is not at issue."
    judgment := .questionable
    alternatives := [("Satō-iri-no ryokucha-wa oishiku-nai-yo.", .acceptable)]
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "counterstance"), ("priorMove", "whQuestion")]
    comment := "The paper marks nanka with ?? here ({wa/??nanka}); the plain wa variant is fine. No counterstance is salient after a general wh-question."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex39_dose_q1 : LinguisticExample :=
  { id := "kubota2026_ex39_dose_q1"
    source := ⟨"kubota-2026", "(39), response to Q1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Satō-iri-no ryokucha-wa dōse mazui yo."
    discourseSegments := ["Q1: Satō-iri-no ryokucha-wa oishii-ka-na?", "A: Satō-iri-no ryokucha-wa dōse mazui yo."]
    glossedTokens := []
    translation := "Sweetened green tea is untasty anyway."
    context := "Q1, 'I wonder if sweetened green tea is tasty', makes the issue the prejacent responds to salient."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "counterstance"), ("priorMove", "polarQuestion")]
    comment := "The polar question raises the issue whether sweetened green tea is tasty, which licenses dōse."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex39_dose_q2 : LinguisticExample :=
  { id := "kubota2026_ex39_dose_q2"
    source := ⟨"kubota-2026", "(39), response to Q2"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Satō-iri-no ryokucha-wa dōse mazui yo."
    discourseSegments := ["Q2: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na?", "A: Satō-iri-no ryokucha-wa dōse mazui yo."]
    glossedTokens := []
    translation := "Sweetened green tea is untasty anyway."
    context := "Q2, 'I wonder what kind of drink tastes good with sugar in it', is a general wh-question that leaves the specific issue unraised."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "counterstance"), ("priorMove", "whQuestion")]
    comment := "Same sentence as the response to Q1; infelicitous because no salient issue directly responded to by the prejacent is raised."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40_nanka_denial : LinguisticExample :=
  { id := "kubota2026_ex40_nanka_denial"
    source := ⟨"kubota-2026", "(40)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Satō-iri-no ryokucha nanka watashi-wa noma-nai. — Iya, sonna hazu-wa nai yo."
    discourseSegments := ["A: Satō-iri-no ryokucha nanka watashi-wa noma-nai.", "B: Iya, sonna hazu-wa nai yo."]
    glossedTokens := []
    translation := "I won't drink green tea with sugar or anything like that. — No, that can't be true."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "denial"), ("denialTarget", "prejacent")]
    comment := "B's denial means 'You'll drink it for sure', not 'You are not negative about green tea with sugar': the stance layer cannot be the target of a yes/no response."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex41_dose_denial : LinguisticExample :=
  { id := "kubota2026_ex41_dose_denial"
    source := ⟨"kubota-2026", "(41)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Watashi-ni-wa dōse kinmedaru-wa tor-e-nai. — Iya, sonna hazu-wa nai yo."
    discourseSegments := ["A: Watashi-ni-wa dōse kinmedaru-wa tor-e-nai.", "B: Iya, sonna hazu-wa nai yo."]
    glossedTokens := []
    translation := "I can't win a gold medal anyway. — No, that can't be true."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "denial"), ("denialTarget", "prejacent")]
    comment := "B's denial means 'You have plenty of chances', not 'You aren't really so pessimistic'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex42_perspective_shift : LinguisticExample :=
  { id := "kubota2026_ex42_perspective_shift"
    source := ⟨"kubota-2026", "(42)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Sensei-wa [boku-ga (dōse) SALT-ni(-nanka) tōra-nai]-to omot-te-ta rashii."
    discourseSegments := []
    glossedTokens := []
    translation := "My advisor seems to have thought I wouldn't possibly get accepted at SALT."
    context := "The speaker was confident their paper would be accepted; the advisor held a pessimistic view."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse+nanka"), ("phenomenon", "perspectiveShift"), ("perspectiveHolder", "attitudeHolder")]
    comment := "Under the attitude verb the pessimistic outlook can only be read as the advisor's, not the speaker's: outlook markers shift under embedding, unlike typical expressives."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex45a_nanka_epistemic : LinguisticExample :=
  { id := "kubota2026_ex45a_nanka_epistemic"
    source := ⟨"kubota-2026", "(45a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Konna tokoro ni nihonjin-nanka inai hazu da."
    discourseSegments := []
    glossedTokens := []
    translation := "There shouldn't be any Japanese people in a place like this."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "hazu"), ("modalFlavor", "epistemic"), ("evaluation", "neutral")]
    comment := "With the epistemic modal hazu the negative implication is comparatively neutral."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex45b_nanka_ability : LinguisticExample :=
  { id := "kubota2026_ex45b_nanka_ability"
    source := ⟨"kubota-2026", "(45b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Watashi ni-wa kin medaru-nanka torenai."
    discourseSegments := []
    glossedTokens := []
    translation := "There's no way I can win a gold medal."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "-eru"), ("modalFlavor", "circumstantial"), ("evaluation", "neutral")]
    comment := "With the ability modal the negative implication is comparatively neutral, as with the epistemic case."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex45c_nanka_deontic : LinguisticExample :=
  { id := "kubota2026_ex45c_nanka_deontic"
    source := ⟨"kubota-2026", "(45c)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Tookyoo-ni-nanka ika-nai hō-ga yokat-ta."
    discourseSegments := []
    glossedTokens := []
    translation := "It would have been better not to go to Tokyo (of all places)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "hō-ga yokat-ta"), ("modalFlavor", "deontic"), ("evaluation", "pejorative")]
    comment := "With a priority modal the negative implication is clearly pejorative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex45d_nanka_bouletic : LinguisticExample :=
  { id := "kubota2026_ex45d_nanka_bouletic"
    source := ⟨"kubota-2026", "(45d)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Aisu kuriimu-nanka iranai."
    discourseSegments := []
    glossedTokens := []
    translation := "I don't want such a thing as ice cream."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "iranai"), ("modalFlavor", "bouletic"), ("evaluation", "pejorative")]
    comment := "With a bouletic modal the negative implication is clearly pejorative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46a_semete_epistemic : LinguisticExample :=
  { id := "kubota2026_ex46a_semete_epistemic"
    source := ⟨"kubota-2026", "(46a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kono-yoona tokoro-ni-wa semete Nihonjin-wa iru hazu-da."
    discourseSegments := []
    glossedTokens := []
    translation := "In a place like this, there should at least be some Japanese people."
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "hazu"), ("modalFlavor", "epistemic")]
    comment := "The paper marks the sentence ??: semete is incompatible with the epistemic modal hazu."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46b_semete_ability : LinguisticExample :=
  { id := "kubota2026_ex46b_semete_ability"
    source := ⟨"kubota-2026", "(46b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Watashi-ni-wa semete dō-medaru-wa toreru."
    discourseSegments := []
    glossedTokens := []
    translation := "As for me, I can at least win a bronze medal."
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-eru"), ("modalFlavor", "circumstantial")]
    comment := "The paper marks the sentence ??: semete is incompatible with the ability modal -eru."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46c_semete_desiderative : LinguisticExample :=
  { id := "kubota2026_ex46c_semete_desiderative"
    source := ⟨"kubota-2026", "(46c)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Semete yobō-sesshu-wa uke-tai."
    discourseSegments := []
    glossedTokens := []
    translation := "One should at least get vaccinated."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-tai"), ("modalFlavor", "bouletic")]
    comment := "semete with the desiderative -tai."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46d_semete_deontic : LinguisticExample :=
  { id := "kubota2026_ex46d_semete_deontic"
    source := ⟨"kubota-2026", "(46d)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Semete ryohi-wa harau-beki-da."
    discourseSegments := []
    glossedTokens := []
    translation := "At least we should cover the travel expenses."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-beki"), ("modalFlavor", "deontic")]
    comment := "semete with the deontic -beki."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex10_nanka_noncancelable, ex11_mushiro_unexpected, ex12_yahari_expected, ex37_nanka_counterstance, ex38_nanka_no_counterstance, ex39_dose_q1, ex39_dose_q2, ex40_nanka_denial, ex41_dose_denial, ex42_perspective_shift, ex45a_nanka_epistemic, ex45b_nanka_ability, ex45c_nanka_deontic, ex45d_nanka_bouletic, ex46a_semete_epistemic, ex46b_semete_ability, ex46c_semete_desiderative, ex46d_semete_deontic]

end Kubota2026.Examples
