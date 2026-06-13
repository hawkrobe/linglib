import Linglib.Data.Examples.Schema

/-!
# `Thomas2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Thomas2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Thomas2026.Examples`.
-/

namespace Thomas2026.Examples

open Data.Examples

def canonical_too : LinguisticExample :=
  { id := "thomas2026_canonical_too"
    source := ⟨"thomas-2026", "(2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Avery invited Bailey. She invited Cameron, too."
    discourseSegments := ["Avery invited Bailey.", "She invited Cameron, too."]
    glossedTokens := []
    translation := "Avery invited Bailey. She invited Cameron, too."
    context := "Q: Who did Avery invite?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")]
    comment := "Canonical additive use: two independent answers to a contextually salient question (the Beaver & Clark 2008 / Zeevat & Jasinskaja 2007 configuration). Replaces the constructed row johnCameMaryToo from Phenomena/Focus/AdditiveParticles/Data.lean, which did not occur in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def rullmann_too : LinguisticExample :=
  { id := "thomas2026_rullmann_too"
    source := ⟨"rullmann-2003", "UNVERIFIED focus-alternative too"⟩
    reportedIn := some ⟨"thomas-2026", "(5a)"⟩
    language := "stan1293"
    primaryText := "I like [pizza]F, and I like [spaghetti]F, too."
    discourseSegments := []
    glossedTokens := []
    translation := "I like pizza, and I like spaghetti, too."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "satisfied")]
    comment := "The antecedent 'I like [pizza]F' is a focus alternative of the host 'I like [spaghetti]F' (Rooth 1985, 1992). Replaces the constructed row johnSingsJohnDancesToo from Phenomena/Focus/AdditiveParticles/Data.lean, which did not occur in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def rullmann_either : LinguisticExample :=
  { id := "thomas2026_rullmann_either"
    source := ⟨"rullmann-2003", "UNVERIFIED negative additive either"⟩
    reportedIn := some ⟨"thomas-2026", "(5b)"⟩
    language := "stan1293"
    primaryText := "I don't like [pizza]F, and I don't like [spaghetti]F, either."
    discourseSegments := []
    glossedTokens := []
    translation := "I don't like pizza, and I don't like spaghetti, either."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "either"), ("use_type", "standard")]
    comment := "Negative-context additive either. Thomas 2026 fn. 9 leaves either's precise felicity conditions to future work (awkwardness of 'too' under negation attributed to competition with 'either', following Rullmann 2003), so no def64_status feature is recorded. Replaces the constructed row eitherNegative from Phenomena/Focus/AdditiveParticles/Data.lean, which did not occur in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kripke_dinner : LinguisticExample :=
  { id := "thomas2026_kripke_dinner"
    source := ⟨"kripke-2009", "UNVERIFIED out-of-the-blue too"⟩
    reportedIn := some ⟨"thomas-2026", "(3)"⟩
    language := "stan1293"
    primaryText := "Tonight [Sam]F is having dinner in New York, too."
    discourseSegments := []
    glossedTokens := []
    translation := "Tonight Sam is having dinner in New York, too."
    context := "Uttered out of the blue, with no salient antecedent in the discourse."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "antecedent_violation")]
    comment := "Kripke's classic: felicitous only if some other salient person is having dinner in New York tonight; counterevidence to a purely existential presupposition (Karttunen 1974). Under Thomas 2026 Def (64) there is no antecedent proposition embodying a fact about the context, so the Antecedent Condition fails. Replaces the constructed rows missingAntecedent and contextMismatch from Phenomena/Focus/AdditiveParticles/Data.lean, which did not occur in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def dogs_mammals : LinguisticExample :=
  { id := "thomas2026_dogs_mammals"
    source := ⟨"thomas-2026", "(72)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She invited Bailey and Cameron. Dogs are mammals, too."
    discourseSegments := ["A: She invited Bailey and Cameron.", "B: Dogs are mammals, too."]
    glossedTokens := []
    translation := "She invited Bailey and Cameron. Dogs are mammals, too."
    context := "Q: Who are some people Avery invited?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "conjunction_violation")]
    comment := "The prejacent contributes no information about who Avery invited, so ANT ∩ ⟦π⟧ evidences the resolution no more strongly than ANT alone: the Conjunction Condition fails for every contextually relevant question (§5.5). Replaces the constructed row irrelevantAntecedent from Phenomena/Focus/AdditiveParticles/Data.lean, which did not occur in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ecstatic : LinguisticExample :=
  { id := "thomas2026_ecstatic"
    source := ⟨"beaver-clark-2008", "UNVERIFIED pp. 93-94"⟩
    reportedIn := some ⟨"thomas-2026", "(11)"⟩
    language := "stan1293"
    primaryText := "Sam is happy. He's ecstatic, too."
    discourseSegments := ["Sam is happy.", "He's ecstatic, too."]
    glossedTokens := []
    translation := "Sam is happy. He's ecstatic, too."
    context := "Q: What is Sam's emotional state?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "prejacent_violation_i")]
    comment := "Beaver & Clark 2008's observation; the host entails the antecedent. Under Thomas 2026 the Antecedent and Conjunction Conditions are satisfied with RQ = the question shown, but the resolution |Sam is ecstatic| is entailed by the prejacent, violating Prejacent Condition (i) (repeated as (73) in section 5.5)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cello : LinguisticExample :=
  { id := "thomas2026_cello"
    source := ⟨"thomas-2026", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Avery plays an instrument. Bailey plays the cello, too."
    discourseSegments := ["Avery plays an instrument.", "Bailey plays the cello, too."]
    glossedTokens := []
    translation := "Avery plays an instrument. Bailey plays the cello, too."
    context := "RQ: Who plays an instrument?"
    judgment := .unacceptable
    alternatives := [("Avery plays the cello. Bailey plays an instrument, too.", .acceptable)]
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "standard"), ("def64_status", "prejacent_violation_ii")]
    comment := "The weaker alternative 'Bailey plays an instrument' would evidence the resolution just as strongly, violating Prejacent Condition (ii) (repeated as (74) in section 5.5). The (30A') alternative shows the constraint has no antecedent analogue."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def hotel_fancy : LinguisticExample :=
  { id := "thomas2026_hotel_fancy"
    source := ⟨"thomas-2026", "(18c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A room just opened up at this hotel. It looks like a fancy one, too."
    discourseSegments := ["A room just opened up at this hotel.", "It looks like a fancy one, too."]
    glossedTokens := []
    translation := "A room just opened up at this hotel. It looks like a fancy one, too."
    context := "Q: What would be a good hotel to stay at? Antecedent and prejacent jointly argue for the conclusion that this hotel would be a good one to stay at."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "argumentBuilding"), ("def64_status", "satisfied")]
    comment := "Argument-building use: antecedent and prejacent are neither complete nor partial answers to the question shown but each merely provides evidence for an answer. Attested COCA dialogue, introduced as (1c) and (14c)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def hotel_dingy : LinguisticExample :=
  { id := "thomas2026_hotel_dingy"
    source := ⟨"thomas-2026", "(19c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A room just opened up at this hotel. It looks like a dingy one, too."
    discourseSegments := ["A room just opened up at this hotel.", "It looks like a dingy one, too."]
    glossedTokens := []
    translation := "A room just opened up at this hotel. It looks like a dingy one, too."
    context := "Same context as (18c): the interlocutors are looking for a nice hotel room to stay in."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "too"), ("use_type", "argumentBuilding"), ("def64_status", "conjunction_violation")]
    comment := "Reversing the prejacent's argumentative force destroys the argument-building use: there is no question relevant to the discourse goal to which the conjunction of antecedent and prejacent provides evidence of a resolution (introduced as (15c))."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [canonical_too, rullmann_too, rullmann_either, kripke_dinner, dogs_mammals, ecstatic, cello, hotel_fancy, hotel_dingy]

end Thomas2026.Examples
