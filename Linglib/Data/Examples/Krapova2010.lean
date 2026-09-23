module

public import Linglib.Data.Examples.Schema

/-!
# `Krapova2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Krapova2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Krapova2010.Examples`.
-/

@[expose] public section

namespace Krapova2010.Examples

open Data.Examples

def ex_56a : LinguisticExample :=
  { id := "krapova2010_56a"
    source := ⟨"krapova-2010", "(56a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Naistina săžaljavam, deto ne otdelix poveče vnimanie na postrojkata."
    discourseSegments := []
    glossedTokens := [("Naistina", "really"), ("săžaljavam,", "regret-1sg"), ("deto", "that"), ("ne", "not"), ("otdelix", "devoted-1sg"), ("poveče", "more"), ("vnimanie", "attention"), ("na", "to"), ("postrojkata", "construction-the")]
    translation := "I really regret that I did not devote greater attention to the construction."
    context := ""
    judgment := .acceptable
    alternatives := [("Naistina săžaljavam, če ne otdelix poveče vnimanie na postrojkata.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "săžaljavam"), ("complementizer", "deto"), ("diagnostic", "detoSelection")]
    comment := "deto alternates freely with če, apart from style and register; colloquial speech."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_56b : LinguisticExample :=
  { id := "krapova2010_56b"
    source := ⟨"krapova-2010", "(56b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Samo me e jad, deto grivnata izčezna sled zatămnenieto."
    discourseSegments := []
    glossedTokens := [("Samo", "only"), ("me", "me-ClAcc"), ("e", "is"), ("jad,", "anger"), ("deto", "that"), ("grivnata", "bracelet-the"), ("izčezna", "disappeared-3sg"), ("sled", "after"), ("zatămnenieto", "eclipse-the")]
    translation := "I am only angry that the bracelet disappeared after the eclipse."
    context := ""
    judgment := .acceptable
    alternatives := [("Samo me e jad, če grivnata izčezna sled zatămnenieto.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "jad me e"), ("complementizer", "deto"), ("diagnostic", "detoSelection")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_57a : LinguisticExample :=
  { id := "krapova2010_57a"
    source := ⟨"krapova-2010", "(57a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Nikak ne săžaljavam, deto sreštata im se e provalila."
    discourseSegments := []
    glossedTokens := [("Nikak", "not-at-all"), ("ne", "not"), ("săžaljavam,", "regret-1sg"), ("deto", "that"), ("sreštata", "meeting-the"), ("im", "their"), ("se", "refl"), ("e", "is"), ("provalila", "failed-prt")]
    translation := "I do not regret at all that their meeting has not taken place."
    context := ""
    judgment := .acceptable
    alternatives := [("Nikak ne săžaljavam, če sreštata im se e provalila.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "săžaljavam"), ("complementizer", "deto"), ("diagnostic", "projection"), ("environment", "negation"), ("projective", "yes"), ("person", "1")]
    comment := "Presupposes that the meeting has failed, although the speaker does not regret that."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_57b : LinguisticExample :=
  { id := "krapova2010_57b"
    source := ⟨"krapova-2010", "(57b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Vinoven li săm deto gostite pristignaxa kăsno?"
    discourseSegments := []
    glossedTokens := [("Vinoven", "guilty"), ("li", "Q"), ("săm", "am"), ("deto", "that"), ("gostite", "guests-the"), ("pristignaxa", "arrived-3pl"), ("kăsno", "late")]
    translation := "Is it my fault that the guests arrived late?"
    context := ""
    judgment := .acceptable
    alternatives := [("Vinoven li săm če gostite pristignaxa kăsno?", .acceptable)]
    readings := []
    paperFeatures := [("verb", "vinoven săm"), ("complementizer", "deto"), ("diagnostic", "projection"), ("environment", "question"), ("projective", "yes"), ("person", "1")]
    comment := "Presupposes that the visitors arrived late."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_57c : LinguisticExample :=
  { id := "krapova2010_57c"
    source := ⟨"krapova-2010", "(57c)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Săžaljavam, deto ne moža da ostaneš poveče."
    discourseSegments := []
    glossedTokens := [("Săžaljavam,", "regret-1sg"), ("deto", "that"), ("ne", "not"), ("moža", "could-2sg"), ("da", "Mod"), ("ostaneš", "stay-2sg"), ("poveče", "more")]
    translation := "I regret that you couldn't stay longer."
    context := ""
    judgment := .acceptable
    alternatives := [("Săžaljavam, če ne moža da ostaneš poveče.", .acceptable), ("Săžaljavam, deto ne moža da ostaneš poveče, no vsăšnost ti ostana poveče.", .unacceptable)]
    readings := []
    paperFeatures := [("verb", "săžaljavam"), ("complementizer", "deto"), ("diagnostic", "contradiction"), ("person", "1")]
    comment := "Adding 'but in fact you stayed longer' cancels the presupposition and is a contradiction."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_58a : LinguisticExample :=
  { id := "krapova2010_58a"
    source := ⟨"krapova-2010", "(58a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Văzmutix se deto ne sa mogli da provedat sreštata."
    discourseSegments := []
    glossedTokens := [("Văzmutix", "resent-1sg"), ("se", "refl"), ("deto", "that"), ("ne", "not"), ("sa", "are-3pl"), ("mogli", "able-pl"), ("da", "Mod"), ("provedat", "organize-3pl"), ("sreštata", "meeting-the")]
    translation := "I resent the fact that they were not able to organize the meeting."
    context := ""
    judgment := .ungrammatical
    alternatives := [("Văzmutix se če ne sa mogli da provedat sreštata.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "văzmuštavam se"), ("complementizer", "deto"), ("diagnostic", "detoSelection")]
    comment := "An emotive factive without a za phrase takes če only."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_58b : LinguisticExample :=
  { id := "krapova2010_58b"
    source := ⟨"krapova-2010", "(58b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Otkrix deto sreštata im se e provalila."
    discourseSegments := []
    glossedTokens := [("Otkrix", "found-out-1sg"), ("deto", "that"), ("sreštata", "meeting-the"), ("im", "their"), ("se", "refl"), ("e", "is"), ("provalila", "failed-prt")]
    translation := "I found out that their meeting has failed."
    context := ""
    judgment := .ungrammatical
    alternatives := [("Otkrix če sreštata im se e provalila.", .acceptable)]
    readings := []
    paperFeatures := [("verb", "otkrivam"), ("complementizer", "deto"), ("diagnostic", "detoSelection")]
    comment := "A semi-factive takes če only."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_59a : LinguisticExample :=
  { id := "krapova2010_59a"
    source := ⟨"krapova-2010", "(59a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Săžaljavam za provala na sreštata."
    discourseSegments := []
    glossedTokens := [("Săžaljavam", "regret-1sg"), ("za", "for"), ("provala", "failure-the"), ("na", "of"), ("sreštata", "meeting-the")]
    translation := "I am sorry about the failure of the meeting."
    context := ""
    judgment := .acceptable
    alternatives := [("Săžaljavam na provala na sreštata.", .ungrammatical), ("Săžaljavam provala na sreštata.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "săžaljavam"), ("diagnostic", "zaPhrase")]
    comment := "Other prepositions and preposition-less noun phrases are excluded; the nominal paraphrase of (57a)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_59b : LinguisticExample :=
  { id := "krapova2010_59b"
    source := ⟨"krapova-2010", "(59b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Vinoven li săm za zakăsnenieto na gostite?"
    discourseSegments := []
    glossedTokens := [("Vinoven", "guilty"), ("li", "Q"), ("săm", "am"), ("za", "for"), ("zakăsnenieto", "delay-the"), ("na", "of"), ("gostite", "visitors-the")]
    translation := "Am I responsible for the late arrival of the guests?"
    context := ""
    judgment := .acceptable
    alternatives := [("Vinoven li săm na zakăsnenieto na gostite?", .ungrammatical), ("Vinoven li săm zakăsnenieto na gostite?", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "vinoven săm"), ("diagnostic", "zaPhrase")]
    comment := "The nominal paraphrase of (57b)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def fn46i : LinguisticExample :=
  { id := "krapova2010_fn46i"
    source := ⟨"krapova-2010", "fn. 46 (i)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Văzmutix se če ne sa mogli da provedat sreštata."
    discourseSegments := []
    glossedTokens := [("Văzmutix", "resent-1sg"), ("se", "refl"), ("če", "that"), ("ne", "not"), ("sa", "are-3pl"), ("mogli", "able-pl"), ("da", "Mod"), ("provedat", "organize-3pl"), ("sreštata", "meeting-the")]
    translation := "I resent the fact that they were not able to organize the meeting."
    context := ""
    judgment := .acceptable
    alternatives := [("Văzmutix se če ne sa mogli da provedat sreštata, no vsăšnost te provedoxa sreštata.", .unacceptable)]
    readings := []
    paperFeatures := [("verb", "văzmuštavam se"), ("complementizer", "če"), ("diagnostic", "contradiction"), ("person", "1")]
    comment := "The če complement is factive too: factivity is the context's, not the complementizer's."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex_56a, ex_56b, ex_57a, ex_57b, ex_57c, ex_58a, ex_58b, ex_59a, ex_59b, fn46i]

end Krapova2010.Examples
