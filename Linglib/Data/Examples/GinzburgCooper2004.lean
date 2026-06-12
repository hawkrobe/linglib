import Linglib.Data.Examples.Schema

/-!
# `GinzburgCooper2004` — typed example data

Auto-generated from `Linglib/Data/Examples/GinzburgCooper2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GinzburgCooper2004.Examples`.
-/

namespace GinzburgCooper2004.Examples

open Data.Examples

def ex_4a_bo : LinguisticExample :=
  { id := "ginzburgcooper2004_4a_bo"
    source := ⟨"ginzburg-cooper-2004", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did Bo finagle a raise? B: Bo?"
    discourseSegments := ["A: Did Bo finagle a raise?", "B: Bo?"]
    glossedTokens := []
    translation := "A: Did Bo finagle a raise? B: Bo?"
    context := "Clarification ellipsis of a proper name: the paradigm case. Clausal reading: 'Are you asking if BO finagled a raise?'; constituent reading: 'Who is Bo?'"
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("phonIdentical", "true"), ("category", "NP")]
    comment := "UNVERIFIED paperLabel: ex. (4a) carried from Phenomena/Ellipsis/ClarificationEllipsis.lean ceProperName, not checked against the published paper. RECONCILE: Studies/GinzburgCooper2004.lean uses 'Did Bo leave?' as its running example (paper ex. 28/32 per that file); whether (4a)'s antecedent is 'Did Bo finagle a raise?' or 'Did Bo leave?' needs checking against the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4a_finagle : LinguisticExample :=
  { id := "ginzburgcooper2004_4a_finagle"
    source := ⟨"ginzburg-cooper-2004", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did Bo finagle a raise? B: Finagle?"
    discourseSegments := ["A: Did Bo finagle a raise?", "B: Finagle?"]
    glossedTokens := []
    translation := "A: Did Bo finagle a raise? B: Finagle?"
    context := "Clarification ellipsis of a rare word: the constituent reading requests lexical clarification ('What does finagle mean?'), not referent identification."
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("phonIdentical", "true"), ("category", "V")]
    comment := "UNVERIFIED paperLabel: ex. (4a) carried from Phenomena/Ellipsis/ClarificationEllipsis.lean ceRareWord, not checked against the published paper (the Lean file labels both the Bo and finagle fragments as 4a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8a : LinguisticExample :=
  { id := "ginzburgcooper2004_8a"
    source := ⟨"ginzburg-cooper-2004", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did Bo leave? B: My cousin?"
    discourseSegments := ["A: Did Bo leave?", "B: My cousin?"]
    glossedTokens := []
    translation := "A: Did Bo leave? B: My cousin?"
    context := "Non-identical clarification ellipsis: the fragment 'My cousin?' is not phonologically identical to the antecedent sub-utterance 'Bo'. Neither reading requires phonological identity."
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("phonIdentical", "false"), ("category", "NP")]
    comment := "UNVERIFIED paperLabel: ex. (8a) carried from Phenomena/Ellipsis/ClarificationEllipsis.lean ceNonIdentical, not checked against the published paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8c : LinguisticExample :=
  { id := "ginzburgcooper2004_8c"
    source := ⟨"ginzburg-cooper-2004", "(8c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did you bike to work yesterday? B: Cycle?"
    discourseSegments := ["A: Did you bike to work yesterday?", "B: Cycle?"]
    glossedTokens := []
    translation := "A: Did you bike to work yesterday? B: Cycle?"
    context := "Non-identical clarification ellipsis of a verb. Clausal reading: 'Are you asking if I cycled to work yesterday?'; constituent reading: 'When you say bike, are you referring to cycling?'"
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("phonIdentical", "false"), ("category", "V")]
    comment := "UNVERIFIED paperLabel: ex. (8c) carried from Phenomena/Ellipsis/ClarificationEllipsis.lean ceNonIdenticalVerb, not checked against the published paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10a : LinguisticExample :=
  { id := "ginzburgcooper2004_10a"
    source := ⟨"ginzburg-cooper-2004", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: I phoned him. B: Him?"
    discourseSegments := ["A: I phoned him.", "B: Him?"]
    glossedTokens := []
    translation := "A: I phoned him. B: Him?"
    context := "Syntactic parallelism: the CE fragment must categorially match the antecedent sub-utterance. Accusative 'Him?' matches accusative 'him'; nominative 'he?' does not."
    judgment := .acceptable
    alternatives := [("He?", .unacceptable)]
    readings := []
    paperFeatures := [("phonIdentical", "true"), ("category", "NP")]
    comment := "UNVERIFIED paperLabel: ex. (10a) carried from Phenomena/Ellipsis/ClarificationEllipsis.lean accMatchOK/nomMismatchBad, not checked against the published paper. The nominative variant in alternatives is the Lean file's '#he?' (infelicitous), merged here as a within-example contrast."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "ginzburgcooper2004_11"
    source := ⟨"ginzburg-cooper-2004", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Let's hold the conference here. B: Here?"
    discourseSegments := ["A: Let's hold the conference here.", "B: Here?"]
    glossedTokens := []
    translation := "A: Let's hold the conference here. B: Here?"
    context := "A is in Gothenburg, B is in Hyderabad (no shared belief about the content of 'here'). The content of 'here' differs across participants, so the clausal reading, which presupposes shared belief about content, is unavailable; only the constituent reading survives."
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .unacceptable), ("constituent", .acceptable)]
    paperFeatures := [("phonIdentical", "true"), ("category", "AdvP"), ("sharedBelief", "false")]
    comment := "UNVERIFIED paperLabel: ex. (11) carried from Phenomena/Ellipsis/ClarificationEllipsis.lean ceDistinctLocations and differentLocations (the same example encoded twice in the Lean file, merged here), not checked against the published paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "ginzburgcooper2004_12"
    source := ⟨"ginzburg-cooper-2004", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Let's hold the conference here. B: Here?"
    discourseSegments := ["A: Let's hold the conference here.", "B: Here?"]
    glossedTokens := []
    translation := "A: Let's hold the conference here. B: Here?"
    context := "Both A and B are in Gothenburg (shared belief about the content of 'here'). Both readings available; clausal: 'Are you asking if we should hold the conference in Gothenburg of all places?'"
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("phonIdentical", "true"), ("category", "AdvP"), ("sharedBelief", "true")]
    comment := "UNVERIFIED paperLabel: ex. (12) carried from Phenomena/Ellipsis/ClarificationEllipsis.lean sameLocation, not checked against the published paper. Minimal pair with ex. (11): the shared-belief condition distinguishes the clausal from the constituent reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_13a : LinguisticExample :=
  { id := "ginzburgcooper2004_13a"
    source := ⟨"ginzburg-cooper-2004", "(13a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Can I come in? B: I?"
    discourseSegments := ["A: Can I come in?", "B: I?"]
    glossedTokens := []
    translation := "A: Can I come in? B: I?"
    context := "Clarification ellipsis of an indexical pronoun across speakers: 'I' refers to A when A says it, but would refer to B if B said it. Since the reference changes across speakers, the clausal reading (which requires shared belief about content) is blocked."
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .unacceptable), ("constituent", .acceptable)]
    paperFeatures := [("phonIdentical", "true"), ("category", "NP"), ("sharedBelief", "false")]
    comment := "UNVERIFIED paperLabel: ex. (13a) carried from Phenomena/Ellipsis/ClarificationEllipsis.lean ceIndexicalI, not checked against the published paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6a : LinguisticExample :=
  { id := "ginzburgcooper2004_6a"
    source := ⟨"ginzburg-cooper-2004", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: you always had er er say every foot he had with a piece of spunyarn in the wire B: Spunyarn?"
    discourseSegments := ["A: you always had er er say every foot he had with a piece of spunyarn in the wire", "B: Spunyarn?"]
    glossedTokens := []
    translation := "A: you always had er er say every foot he had with a piece of spunyarn in the wire B: Spunyarn?"
    context := "British National Corpus attestation (file H5G): clarification ellipsis of an unknown word. Constituent reading dominant: 'What's spunyarn?'"
    judgment := .acceptable
    alternatives := []
    readings := [("clausal", .acceptable), ("constituent", .acceptable)]
    paperFeatures := [("phonIdentical", "true"), ("category", "N")]
    comment := "UNVERIFIED paperLabel: ex. (6a) carried from Phenomena/Ellipsis/ClarificationEllipsis.lean ceSpunyarn, not checked against the published paper. Originating source is the BNC (file H5G per the Lean notes), reported in Ginzburg & Cooper 2004; no separate BNC bib entry, so source carries the paper's bibkey."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_4a_bo, ex_4a_finagle, ex_8a, ex_8c, ex_10a, ex_11, ex_12, ex_13a, ex_6a]

end GinzburgCooper2004.Examples
