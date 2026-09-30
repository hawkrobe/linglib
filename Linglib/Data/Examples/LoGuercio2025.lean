module

public import Linglib.Data.Examples.Schema

/-!
# `LoGuercio2025` — typed example data

Auto-generated from `Linglib/Data/Examples/LoGuercio2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace LoGuercio2025.Examples`.
-/

@[expose] public section

namespace LoGuercio2025.Examples

def outOfBlue_epithet : Datum :=
  { id := "loguercio2025_outOfBlue_epithet"
    source := ⟨"lo-guercio-2025", "(epithet OOTB)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John arrived late."
    glossedTokens := []
    context := "Out of the blue, no prior mention of any epithet construction."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "epithet"), ("licensingMechanism", "outOfBlue")] }

def priorMention_epithet : Datum :=
  { id := "loguercio2025_priorMention_epithet"
    source := ⟨"lo-guercio-2025", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John arrived first, then that bastard Pedro arrived."
    glossedTokens := []
    context := "Single conjoined utterance; the ACI target is the first conjunct's bare `John`."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "John (first conjunct)"), ("expressionType", "epithet"), ("licensingMechanism", "priorMention")] }

def subconstituent_epithet : Datum :=
  { id := "loguercio2025_subconstituent_epithet"
    source := ⟨"lo-guercio-2025", "(epithet subconstituent)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday, John met with that bastard Pedro."
    glossedTokens := []
    context := "Single sentence; the epithet construction occurs as a subconstituent making the alternative for the matrix `John` available."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "John (matrix subject)"), ("expressionType", "epithet"), ("licensingMechanism", "subconstituent")] }

def outOfBlue_honorific : Datum :=
  { id := "loguercio2025_outOfBlue_honorific"
    source := ⟨"lo-guercio-2025", "(Spanish honorific OOTB)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Diego entró."
    glossedTokens := [("Diego", "Diego"), ("entró", "enter.PST.3SG")]
    context := "Out-of-the-blue Spanish utterance; no prior contextual relevance of *don/doña*."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "honorific"), ("licensingMechanism", "outOfBlue"), ("language", "Spanish")] }

def contrastive_honorific : Datum :=
  { id := "loguercio2025_contrastive_honorific"
    source := ⟨"lo-guercio-2025", "(22a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Primero entró Donato. Después entró Don Pedro."
    glossedTokens := [("Primero", "first"), ("entró", "enter.PST.3SG"), ("Donato", "Donato"), ("Después", "afterwards"), ("entró", "enter.PST.3SG"), ("Don", "HON.M"), ("Pedro", "Pedro")]
    context := "Two-segment discourse; the second segment uses honorific *Don* while the first uses bare name *Donato*."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Donato (first segment)"), ("expressionType", "honorific"), ("licensingMechanism", "priorMention"), ("language", "Spanish")] }

def outOfBlue_appositive : Datum :=
  { id := "loguercio2025_outOfBlue_appositive"
    source := ⟨"lo-guercio-2025", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Diego recommended an aspirin."
    glossedTokens := []
    context := "Out-of-the-blue; no prior appositive construction in discourse."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "appositive"), ("licensingMechanism", "outOfBlue")] }

def priorMention_appositive : Datum :=
  { id := "loguercio2025_priorMention_appositive"
    source := ⟨"lo-guercio-2025", "(31b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Diego recommended an aspirin. Laura, a doctor, recommended an antibiotic."
    glossedTokens := []
    context := "Two-segment discourse; the second segment's `, a doctor,` appositive makes the same-shape appositive a contextually-relevant alternative for `Diego`."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Diego (first segment)"), ("expressionType", "appositive"), ("licensingMechanism", "priorMention")] }

def outOfBlue_suppAdverb : Datum :=
  { id := "loguercio2025_outOfBlue_suppAdverb"
    source := ⟨"lo-guercio-2025", "(33a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan signed up for the tournament."
    glossedTokens := []
    context := "Out-of-the-blue assertion with no supplementary-adverb construction in discourse."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "supplementaryAdverb"), ("licensingMechanism", "outOfBlue")] }

def priorMention_suppAdverb : Datum :=
  { id := "loguercio2025_priorMention_suppAdverb"
    source := ⟨"lo-guercio-2025", "(supp-adv prior mention)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan signed up for the tournament and luckily, Pedro signed up for the tournament."
    glossedTokens := []
    context := "Conjoined utterance; the second conjunct's `luckily,` makes the parallel adverb-modified variant available for the first conjunct."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Juan-signup proposition (first conjunct)"), ("expressionType", "supplementaryAdverb"), ("licensingMechanism", "priorMention")] }

def priorMention_emotiveMarker : Datum :=
  { id := "loguercio2025_priorMention_emotiveMarker"
    source := ⟨"lo-guercio-2025", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan signed up for the tournament, and Alas, Pedro signed up too."
    glossedTokens := []
    context := "Conjoined utterance; second conjunct's emotive marker `Alas,` parallels the first conjunct."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Juan-signup proposition (first conjunct)"), ("expressionType", "emotiveMarker"), ("licensingMechanism", "priorMention")] }

def registerBlocking : Datum :=
  { id := "loguercio2025_registerBlocking"
    source := ⟨"lo-guercio-2025", "(28a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "That bastard John is late."
    glossedTokens := []
    context := "Both *bastard* and *motherfucker* are lexical items in the substitution source, with *motherfucker* CI-stronger; the prediction would be an ACI ¬(speaker believes John is a motherfucker)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "doesNotArise"), ("expressionType", "epithet"), ("licensingMechanism", "register"), ("registerContrast", "bastard~motherfucker")] }

def disjunction_independent_of_assertion : Datum :=
  { id := "loguercio2025_disjunction_independent_of_assertion"
    source := ⟨"lo-guercio-2025", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan called María or that bastard Pedro."
    glossedTokens := []
    context := "Test of independence-of-assertion: the CI-stronger conjunctive variant has different at-issue content from the disjunctive utterance, yet the ACI still arises."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "María"), ("expressionType", "epithet"), ("aciProperty", "independentOfAssertion")] }

def DE_aci_survives : Datum :=
  { id := "loguercio2025_DE_aci_survives"
    source := ⟨"lo-guercio-2025", "(DE-embedding)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I doubt that Juan or that bastard Pedro passed the exam."
    glossedTokens := []
    context := "Downward-entailing embedding under `doubt`; tests whether DE blocks ACI computation."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciTarget", "Juan"), ("expressionType", "epithet"), ("aciProperty", "unaffectedByDE")] }

def cancellation : Datum :=
  { id := "loguercio2025_cancellation"
    source := ⟨"lo-guercio-2025", "(ACI cancellation)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan arrived first. Then that bastard Pedro arrived. By the way, Juan is also a bastard."
    glossedTokens := []
    context := "Tests cancellability of the ACI ¬(speaker believes John is a bastard) triggered by the prior-mention configuration."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "cancelled"), ("aciProperty", "cancellable")] }

def reinforcement : Datum :=
  { id := "loguercio2025_reinforcement"
    source := ⟨"lo-guercio-2025", "(ACI reinforcement)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Juan arrived first. That bastard Pedro arrived second. By the way, Juan is not a bastard."
    glossedTokens := []
    context := "Tests reinforceability of the ACI ¬(speaker believes Juan is a bastard)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aciStatus", "arises"), ("aciProperty", "reinforceable")] }

def all : List Datum := [outOfBlue_epithet, priorMention_epithet, subconstituent_epithet, outOfBlue_honorific, contrastive_honorific, outOfBlue_appositive, priorMention_appositive, outOfBlue_suppAdverb, priorMention_suppAdverb, priorMention_emotiveMarker, registerBlocking, disjunction_independent_of_assertion, DE_aci_survives, cancellation, reinforcement]

end LoGuercio2025.Examples
