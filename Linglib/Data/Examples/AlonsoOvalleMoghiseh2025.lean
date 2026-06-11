import Linglib.Data.Examples.Schema

/-!
# `AlonsoOvalleMoghiseh2025` — typed example data

Auto-generated from `Linglib/Data/Examples/AlonsoOvalleMoghiseh2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AlonsoOvalleMoghiseh2025.Examples`.
-/

namespace AlonsoOvalleMoghiseh2025.Examples

open Data.Examples

def aom2025_rootUniqueness : LinguisticExample :=
  { id := "aom2025_rootUniqueness"
    source := ⟨"alonso-ovalle-moghiseh-2025", "root uniqueness, §2.4.2"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "yek-i az dānešju-hā umæd."
    discourseSegments := []
    glossedTokens := [("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā", "student-PL"), ("umæd", "came")]
    translation := "One of the students came."
    context := "root context (no modal embedding)"
    judgment := .acceptable
    alternatives := []
    readings := [("uniqueness (exactly one student)", .acceptable)]
    paperFeatures := [("contextType", "root"), ("modalFlavor", ""), ("uniqueness", "true"), ("freeChoice", "false"), ("modalVariation", "false")]
    comment := "Supplementary illustration of yek-i's root uniqueness reading. Migrated from the legacy `FreeChoiceFarsi.lean` data file; the example is not a direct transcription from the paper but reflects the paper's central claim about yek-i in root contexts."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_deonticFreeChoice : LinguisticExample :=
  { id := "aom2025_deonticFreeChoice"
    source := ⟨"alonso-ovalle-moghiseh-2025", "deontic FC, §2.3.1"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "mituni yek-i az in sib-ā-ro bardāri."
    discourseSegments := []
    glossedTokens := [("mituni", "can.2SG"), ("yek-i", "one-INDF"), ("az", "of"), ("in", "this"), ("sib-ā-ro", "apple-PL-RA"), ("bardāri", "pick.2SG")]
    translation := "You can pick one of these apples."
    context := "deontic possibility modal scopes over yek-i"
    judgment := .acceptable
    alternatives := []
    readings := [("free choice (each apple is a permitted option)", .acceptable), ("embedded uniqueness (only one apple permitted total)", .acceptable)]
    paperFeatures := [("contextType", "deontic modal"), ("modalFlavor", "permission"), ("uniqueness", "true"), ("freeChoice", "true"), ("modalVariation", "false")]
    comment := "Supplementary illustration. Migrated from `FreeChoiceFarsi.lean`. The paper's canonical deontic FC examples are (20a), (25), (26)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_deonticBooks : LinguisticExample :=
  { id := "aom2025_deonticBooks"
    source := ⟨"alonso-ovalle-moghiseh-2025", "deontic FC, books variant"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "mituni yek-i az in ketāb-hā-ro bekhuni."
    discourseSegments := []
    glossedTokens := [("mituni", "can.2SG"), ("yek-i", "one-INDF"), ("az", "of"), ("in", "this"), ("ketāb-hā-ro", "book-PL-RA"), ("bekhuni", "read.2SG")]
    translation := "You can read one of these books."
    context := "deontic possibility modal scopes over yek-i"
    judgment := .acceptable
    alternatives := []
    readings := [("free choice (each book is a permitted option)", .acceptable), ("embedded uniqueness (only one book permitted total)", .acceptable)]
    paperFeatures := [("contextType", "deontic modal"), ("modalFlavor", "permission"), ("uniqueness", "true"), ("freeChoice", "true")]
    comment := "Books variant of the deontic FC example. Migrated from `FreeChoiceFarsi.lean`."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_epistemicModalVariation : LinguisticExample :=
  { id := "aom2025_epistemicModalVariation"
    source := ⟨"alonso-ovalle-moghiseh-2025", "epistemic modal variation, §2.3.2"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "yek-i az dānešju-hā ketāb-o dozid-e."
    discourseSegments := []
    glossedTokens := [("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā", "student-PL"), ("ketāb-o", "book-RA"), ("dozid-e", "stole-3SG")]
    translation := "One of the students (might have) stolen the book."
    context := "epistemic possibility (covert or pragmatic) over yek-i"
    judgment := .acceptable
    alternatives := []
    readings := [("modal variation (at least two students are possible)", .acceptable), ("embedded uniqueness (exactly one stole it)", .acceptable)]
    paperFeatures := [("contextType", "epistemic modal"), ("modalFlavor", "epistemic"), ("modalVariation", "true"), ("uniqueness", "true"), ("freeChoice", "false")]
    comment := "Supplementary illustration of yek-i's modal variation reading under epistemic possibility. Migrated from `FreeChoiceFarsi.lean`. Paper's canonical epistemic example is (32)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_epistemicExplicit : LinguisticExample :=
  { id := "aom2025_epistemicExplicit"
    source := ⟨"alonso-ovalle-moghiseh-2025", "explicit epistemic modal"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "momken-e yek-i az dānešju-hā biyād."
    discourseSegments := []
    glossedTokens := [("momken-e", "possible-is"), ("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā", "student-PL"), ("biyād", "come.3SG")]
    translation := "It's possible that one of the students will come."
    context := "explicit epistemic possibility modal over yek-i"
    judgment := .acceptable
    alternatives := []
    readings := [("modal variation (multiple students are possible)", .acceptable)]
    paperFeatures := [("contextType", "epistemic modal"), ("modalFlavor", "epistemic"), ("modalVariation", "true"), ("uniqueness", "true")]
    comment := "Supplementary example with overt epistemic possibility modal `momken`. Migrated from `FreeChoiceFarsi.lean`."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_deNegation : LinguisticExample :=
  { id := "aom2025_deNegation"
    source := ⟨"alonso-ovalle-moghiseh-2025", "negation context"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "yek-i az dānešju-hā-ro nadid-æm."
    discourseSegments := []
    glossedTokens := [("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā-ro", "student-PL-RA"), ("nadid-æm", "NEG.see-1SG")]
    translation := "I didn't see any of the students."
    context := "downward-entailing: sentential negation, partitive structure"
    judgment := .acceptable
    alternatives := []
    readings := [("narrow-scope existential (no student seen)", .acceptable)]
    paperFeatures := [("contextType", "DE (negation)"), ("modalFlavor", ""), ("uniqueness", "false")]
    comment := "yek-i in DE contexts contributes plain existential force. The paper (17) shows that bare yek-i cannot scope under sentential negation; this partitive variant (`yek-i az NP`) appears compatible with the polarity-item reading. Migrated from `FreeChoiceFarsi.lean`."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_deConditional : LinguisticExample :=
  { id := "aom2025_deConditional"
    source := ⟨"alonso-ovalle-moghiseh-2025", "conditional antecedent"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "ægær yek-i az dānešju-hā biyād, xošhāl mišæm."
    discourseSegments := []
    glossedTokens := [("ægær", "if"), ("yek-i", "one-INDF"), ("az", "of"), ("dānešju-hā", "student-PL"), ("biyād", "come.3SG"), ("xošhāl", "happy"), ("mišæm", "become.1SG")]
    translation := "If any of the students comes, I'll be happy."
    context := "downward-entailing: conditional antecedent"
    judgment := .acceptable
    alternatives := []
    readings := [("narrow-scope existential (some student coming suffices)", .acceptable)]
    paperFeatures := [("contextType", "DE (conditional)"), ("modalFlavor", ""), ("uniqueness", "false")]
    comment := "Conditional antecedent is the canonical DE context where yek-i contributes plain existential force (paper §2.2; cf. eq. 16). Migrated from `FreeChoiceFarsi.lean`."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_embeddedUniqueness : LinguisticExample :=
  { id := "aom2025_embeddedUniqueness"
    source := ⟨"alonso-ovalle-moghiseh-2025", "embedded uniqueness contrast"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "mituni yek-i az in sib-ā-ro bardāri, #væli do-tā nemituni."
    discourseSegments := []
    glossedTokens := [("mituni", "can.2SG"), ("yek-i", "one-INDF"), ("az", "of"), ("in", "this"), ("sib-ā-ro", "apple-PL-RA"), ("bardāri", "pick.2SG"), ("væli", "but"), ("do-tā", "two-CL"), ("nemituni", "NEG.can.2SG")]
    translation := "You can pick one of these apples, #but not two."
    context := "deontic possibility, with continuation testing uniqueness"
    judgment := .marginal
    alternatives := [("mituni yek-i az in sib-ā-ro bardāri.", .acceptable)]
    readings := [("FC + embedded uniqueness (continuation redundant/contradictory)", .marginal)]
    paperFeatures := [("contextType", "deontic modal"), ("modalFlavor", "permission"), ("uniqueness", "true"), ("freeChoice", "true")]
    comment := "Continuation `but not two` is infelicitous (marked `#`) because the embedded uniqueness component already entails that only one apple may be picked. Migrated from `FreeChoiceFarsi.lean` (the original recorded `do-tā væli næ` which appears garbled; corrected here to `do-tā nemituni` 'cannot two')."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_contrast_irgendein : LinguisticExample :=
  { id := "aom2025_contrast_irgendein"
    source := ⟨"kratzer-shimoyama-2002", "irgendein root"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025", "(1), Table 1"⟩
    language := "stan1295"
    primaryText := "Irgendjemand hat angerufen."
    discourseSegments := []
    glossedTokens := [("Irgendjemand", "IRGEND.somebody"), ("hat", "AUX.3SG"), ("angerufen", "called.PTCP")]
    translation := "Somebody (the speaker doesn't know/care who) called."
    context := "root context (no modal); contrast with yek-i in (8)"
    judgment := .acceptable
    alternatives := []
    readings := [("epistemic ignorance/indifference (modal insertion)", .acceptable)]
    paperFeatures := [("item", "irgendein"), ("language", "German"), ("rescueMechanism", "modalInsertion"), ("hasModalInRoot", "true"), ("efciType", "irgendein")]
    comment := "Cross-linguistic EFCI contrast: irgendein has a modal component in root contexts (covert epistemic insertion), unlike yek-i."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def aom2025_contrast_yeki : LinguisticExample :=
  { id := "aom2025_contrast_yeki"
    source := ⟨"alonso-ovalle-moghiseh-2025", "yek-i root contrast, §2.4"⟩
    reportedIn := none
    language := "west2369"
    primaryText := "Yek-i zæng zæd."
    discourseSegments := []
    glossedTokens := [("Yek-i", "one-INDF"), ("zæng", "ring"), ("zæd", "hit.3SG")]
    translation := "Exactly one person called."
    context := "root context (no modal); contrast with irgendein"
    judgment := .acceptable
    alternatives := []
    readings := [("uniqueness (no modal component)", .acceptable)]
    paperFeatures := [("item", "yek-i"), ("language", "Farsi"), ("rescueMechanism", "partialExhaustification"), ("hasModalInRoot", "false"), ("efciType", "yeki")]
    comment := "Cross-linguistic EFCI contrast row: yek-i in root yields uniqueness with no modal component, the paper's central novel claim."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def aom2025_contrast_vreun : LinguisticExample :=
  { id := "aom2025_contrast_vreun"
    source := ⟨"falaus-2014", "p. 122 (cited at AOM 2025 ex. 4)"⟩
    reportedIn := some ⟨"alonso-ovalle-moghiseh-2025", "(4), Table 1"⟩
    language := "roma1327"
    primaryText := "*Monica s-a întâlnit cu vreun prieten."
    discourseSegments := []
    glossedTokens := [("Monica", "Monica"), ("s-a", "REFL-have.3SG"), ("întâlnit", "met"), ("cu", "with"), ("vreun", "VREUN"), ("prieten", "friend.MASC")]
    translation := "(intended) Monica met a friend."
    context := "root context (no modal); contrast with irgendein and yek-i"
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("item", "vreun"), ("language", "Romanian"), ("rescueMechanism", "none"), ("hasModalInRoot", "false"), ("efciType", "vreun")]
    comment := "Cross-linguistic EFCI contrast: vreun has no rescue mechanism and is ungrammatical in unembedded contexts (Fălăuș 2014: 122, cited at AOM 2025 ex. 4 / Table 1)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [aom2025_rootUniqueness, aom2025_deonticFreeChoice, aom2025_deonticBooks, aom2025_epistemicModalVariation, aom2025_epistemicExplicit, aom2025_deNegation, aom2025_deConditional, aom2025_embeddedUniqueness, aom2025_contrast_irgendein, aom2025_contrast_yeki, aom2025_contrast_vreun]

end AlonsoOvalleMoghiseh2025.Examples
