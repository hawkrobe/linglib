import Linglib.Data.Examples.Schema

/-!
# `Giannakidou2002` — typed example data

Auto-generated from `Linglib/Data/Examples/Giannakidou2002.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Giannakidou2002.Examples`.
-/

namespace Giannakidou2002.Examples

open Data.Examples

def prin : LinguisticExample :=
  { id := "giannakidou2002_prin"
    source := ⟨"giannakidou-2002", "UNVERIFIED"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Efije prin na erthi o Janis."
    discourseSegments := []
    glossedTokens := []
    translation := "She left before Janis came."
    context := "Greek *prin* (πριν, 'before'): before-type connective. Requires subjunctive, needs no DE licensor, non-veridical complement, licenses NPIs, no durative restriction on the main clause, and carries no actualization inference — compatible with the complement event never occurring (§6)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "prin"), ("semantic_type", "before"), ("mood", "subjunctive"), ("requires_de", "false"), ("complement_veridical", "false"), ("requires_durative_main", "false"), ("licenses_npis", "true"), ("actualization", "none")]
    comment := "Giannakidou 2002 Greek before-type datum; sentence and diagnostic profile not verified verbatim against the paper (cited in prior formalization as §§2-4, ex. (72) for the no-actualization point)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mexri : LinguisticExample :=
  { id := "giannakidou2002_mexri"
    source := ⟨"giannakidou-2002", "UNVERIFIED"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I Maria perimine mexri irthi o Janis."
    discourseSegments := []
    glossedTokens := []
    translation := "Maria waited until Janis came."
    context := "Greek *mexri* (μέχρι, 'until'): endpoint-type (durative) connective. Requires indicative, veridical complement, requires an imperfective/stative (durative) main clause, does not license NPIs; actualization of the boundary event is a cancellable Q-implicature (cf. ex. (7): 'Sure, the princess slept until midnight. In fact she only woke up at 2am.')."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "mexri"), ("semantic_type", "endpoint"), ("mood", "indicative"), ("requires_de", "false"), ("complement_veridical", "true"), ("requires_durative_main", "true"), ("licenses_npis", "false"), ("actualization", "implicature")]
    comment := "Giannakidou 2002 Greek endpoint-type datum; sentence and diagnostic profile not verified verbatim against the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def para_monon : LinguisticExample :=
  { id := "giannakidou2002_para_monon"
    source := ⟨"giannakidou-2002", "UNVERIFIED ex. (37)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "I prigipisa dhen (apo)kimithike para monon ta mesanixta."
    discourseSegments := []
    glossedTokens := []
    translation := "The princess didn't fall asleep until midnight."
    context := "Greek *para monon* (παρά μονον, lit. 'but only'): eventive-type connective — the Greek lexicalization of NPI-*until*. Requires an anti-veridical trigger (negation, 'without'), no durative restriction, does not itself license NPIs; actualization of the main-clause event at the boundary time is an entailment — cancellation yields contradiction (ex. (38))."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "para monon"), ("semantic_type", "eventive"), ("requires_de", "true"), ("complement_veridical", "false"), ("requires_durative_main", "false"), ("licenses_npis", "false"), ("actualization", "entailment")]
    comment := "Giannakidou 2002 §3.2 eventive-type datum; example number and profile inherited from prior formalization, not verified against the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def english_npi_until : LinguisticExample :=
  { id := "giannakidou2002_english_npi_until"
    source := ⟨"giannakidou-2002", "UNVERIFIED"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The princess didn't wake up until the prince kissed her."
    discourseSegments := []
    glossedTokens := []
    translation := "The princess didn't wake up until the prince kissed her."
    context := "English NPI-*until*: eventive-type. English collapses eventive and durative *until* under one lexeme, disambiguated by the negation context. Patterns with Greek *para monon* on every diagnostic: requires a DE trigger, no durative restriction, actualization is an entailment."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "until (NPI)"), ("semantic_type", "eventive"), ("requires_de", "true"), ("complement_veridical", "false"), ("requires_durative_main", "false"), ("licenses_npis", "true"), ("actualization", "entailment")]
    comment := "Giannakidou 2002 English eventive-type datum; sentence and profile not verified verbatim against the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def english_durative_until : LinguisticExample :=
  { id := "giannakidou2002_english_durative_until"
    source := ⟨"giannakidou-2002", "UNVERIFIED"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John slept until 3pm."
    discourseSegments := []
    glossedTokens := []
    translation := "John slept until 3pm."
    context := "English durative *until*: endpoint-type. No DE requirement, veridical complement, durative main clause required, no NPI licensing; actualization of the boundary event is a cancellable implicature."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("form", "until (durative)"), ("semantic_type", "endpoint"), ("requires_de", "false"), ("complement_veridical", "true"), ("requires_durative_main", "true"), ("licenses_npis", "false"), ("actualization", "implicature")]
    comment := "Giannakidou 2002 English endpoint-type datum; sentence and profile not verified verbatim against the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [prin, mexri, para_monon, english_npi_until, english_durative_until]

end Giannakidou2002.Examples
