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

def ex37_nanka_counterstance : LinguisticExample :=
  { id := "kubota2026_ex37_nanka_counterstance"
    source := ⟨"kubota-2026", "(37)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Ge, amai mono-wa suki-da kedo, satō-iri-no ryokucha nanka zettai oishiku nai yo."
    discourseSegments := ["A: Satō-iri-no ryokucha-tte oishii yo ne.", "B: Ge, amai mono-wa suki-da kedo, satō-iri-no ryokucha nanka zettai oishiku nai yo."]
    glossedTokens := []
    translation := "Ugh, I do like sweets, but sweetened green tea (nanka) is absolutely not tasty."
    context := "A has just asserted a positive evaluation: 'Sweetened green tea is tasty, isn't it?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "counterstance"), ("counterstanceSalient", "true")]
    comment := "Counterstance salient: A's positive evaluation of sweetened green tea licenses nanka. Example number verified against the Kubota 2026 PDF (2026-06-08 audit)."
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
    translation := "Sweetened green tea (nanka) is not tasty."
    context := "A has asked a neutral question: 'What kind of drink tastes good with sugar in it?' — no evaluation is salient."
    judgment := .unacceptable
    alternatives := [("Satō-iri-no ryokucha-wa oishiku-nai-yo.", .acceptable)]
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "counterstance"), ("counterstanceSalient", "false")]
    comment := "No counterstance salient: A's question is neutral, not evaluative; the paper marks nanka with ?? here ({wa/??nanka}), the plain wa variant is fine. Example number verified against the Kubota 2026 PDF (2026-06-08 audit)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex39_dose_q1 : LinguisticExample :=
  { id := "kubota2026_ex39_dose_q1"
    source := ⟨"kubota-2026", "(39), response to Q1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Satō-iri-no ryokucha-wa dōse mazui yo."
    discourseSegments := ["Q1: Satō-iri-no ryokucha-wa oishii-ka-na?", "Satō-iri-no ryokucha-wa dōse mazui yo."]
    glossedTokens := []
    translation := "Sweetened green tea is (dōse) bad-tasting anyway."
    context := "Q1 'I wonder if sweetened green tea is tasty' makes 'sweetened green tea is tasty' a salient counterstance."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "counterstance"), ("counterstanceSalient", "true")]
    comment := "Q1 makes the positive evaluation salient as a counterstance, licensing dōse. Example number verified against the Kubota 2026 PDF (2026-06-08 audit)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex39_dose_q2 : LinguisticExample :=
  { id := "kubota2026_ex39_dose_q2"
    source := ⟨"kubota-2026", "(39), response to Q2"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Satō-iri-no ryokucha-wa dōse mazui yo."
    discourseSegments := ["Q2: Donna nomimono-ni satō-o ireru-no-ga oishii-ka-na?", "Satō-iri-no ryokucha-wa dōse mazui yo."]
    glossedTokens := []
    translation := "Sweetened green tea is (dōse) bad-tasting anyway."
    context := "Q2 'What drink tastes good with sugar?' is neutral: no specific evaluation is salient as a counterstance."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse"), ("phenomenon", "counterstance"), ("counterstanceSalient", "false")]
    comment := "Same sentence as the Q1 response; infelicitous because Q2 makes no evaluation salient as a counterstance. Example number verified against the Kubota 2026 PDF (2026-06-08 audit)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex10_nanka_noncancelable : LinguisticExample :=
  { id := "kubota2026_ex10_nanka_noncancelable"
    source := ⟨"kubota-2026", "(10)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Satō-iri-no ryokucha-wa jitsu-ni mooshi-bun-nai mono-da-ga, watashi-wa satō-iri-no ryokucha nanka kesshite nomanai."
    discourseSegments := []
    glossedTokens := []
    translation := "Green tea with sugar is indeed impeccable, but I will never drink green tea with sugar (nanka)."
    context := "The preceding clause of the same sentence praises green tea with sugar."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "noncancelability")]
    comment := "Non-cancelability: the positive evaluation in the preceding clause contradicts nanka's negative stance, and the stance cannot be cancelled. Example number verified against the Kubota 2026 PDF (2026-06-08 audit)."
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
    comment := "B's denial means 'You'll drink it for sure', not 'You are not negative about green tea with sugar': denial targets the propositional content, not the evaluative stance (descriptive ineffability). Example number verified against the Kubota 2026 PDF (2026-06-08 audit)."
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
    comment := "B's denial means 'You have plenty of chances', not 'You aren't really so pessimistic': denial targets the proposition, not the pessimistic stance. Example number verified against the Kubota 2026 PDF (2026-06-08 audit)."
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
    translation := "Apparently my advisor thought I wouldn't get into SALT (dōse/nanka)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "dōse+nanka"), ("phenomenon", "perspectiveShift"), ("perspectiveHolder", "attitudeHolder")]
    comment := "Under the attitude verb 'think' the negative/pessimistic outlook is attributed to the advisor, not the speaker: outlook markers perspective-shift under embedding, unlike pure expressives. Example number verified against the Kubota 2026 PDF (2026-06-08 audit)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex45a_nanka_epistemic : LinguisticExample :=
  { id := "kubota2026_ex45a_nanka_epistemic"
    source := ⟨"kubota-2026", "(45a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "nanka … hazu"
    discourseSegments := []
    glossedTokens := []
    translation := "There shouldn't be any Japanese people in a place like this."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "hazu"), ("modalFlavor", "epistemic")]
    comment := "nanka with the epistemic modal hazu 'supposed': acceptable, with a neutral (non-pejorative) interpretation. Schematic marker–modal combination; the source row recorded only the combination and its interpretation. Example number verified against the Kubota 2026 PDF (2026-06-08 audit)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex45c_nanka_bouletic : LinguisticExample :=
  { id := "kubota2026_ex45c_nanka_bouletic"
    source := ⟨"kubota-2026", "(45c)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "nanka … ika-nai hō-ga yokat-ta"
    discourseSegments := []
    glossedTokens := []
    translation := "It would have been better not to go to Tokyo (of all places)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "nanka"), ("phenomenon", "modalInteraction"), ("modalForm", "hō-ga yokat-ta"), ("modalFlavor", "bouletic")]
    comment := "nanka with a deontic/bouletic modal 'it would have been better not to go': acceptable, with a pejorative interpretation. Schematic marker–modal combination; the source row recorded only the combination and its interpretation. Example number verified against the Kubota 2026 PDF (2026-06-08 audit)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46a_semete_epistemic : LinguisticExample :=
  { id := "kubota2026_ex46a_semete_epistemic"
    source := ⟨"kubota-2026", "(46a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "semete … hazu"
    discourseSegments := []
    glossedTokens := []
    translation := "??In a place like this, there should at least be some Japanese people."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "hazu"), ("modalFlavor", "epistemic")]
    comment := "semete with the epistemic modal hazu 'supposed' is degraded (?? in the paper): semete rejects epistemic modal flavor. Schematic marker–modal combination; the source row recorded only the combination and its interpretation. Example number verified against the Kubota 2026 PDF (2026-06-08 audit)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46c_semete_desiderative : LinguisticExample :=
  { id := "kubota2026_ex46c_semete_desiderative"
    source := ⟨"kubota-2026", "(46c)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "semete … -tai"
    discourseSegments := []
    glossedTokens := []
    translation := "One should at least get vaccinated."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-tai"), ("modalFlavor", "bouletic")]
    comment := "semete with the desiderative modal -tai 'want': acceptable. Schematic marker–modal combination; the source row recorded only the combination and its interpretation. Example number verified against the Kubota 2026 PDF (2026-06-08 audit)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46d_semete_deontic : LinguisticExample :=
  { id := "kubota2026_ex46d_semete_deontic"
    source := ⟨"kubota-2026", "(46d)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "semete … -beki"
    discourseSegments := []
    glossedTokens := []
    translation := "At least we should cover the travel expenses."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "semete"), ("phenomenon", "modalInteraction"), ("modalForm", "-beki"), ("modalFlavor", "deontic")]
    comment := "semete with the deontic modal -beki 'should': acceptable. Schematic marker–modal combination; the source row recorded only the combination and its interpretation. Example number verified against the Kubota 2026 PDF (2026-06-08 audit)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex37_nanka_counterstance, ex38_nanka_no_counterstance, ex39_dose_q1, ex39_dose_q2, ex10_nanka_noncancelable, ex40_nanka_denial, ex41_dose_denial, ex42_perspective_shift, ex45a_nanka_epistemic, ex45c_nanka_bouletic, ex46a_semete_epistemic, ex46c_semete_desiderative, ex46d_semete_deontic]

end Kubota2026.Examples
