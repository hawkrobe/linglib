import Linglib.Data.Examples.Schema

/-!
# `Schwab2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Schwab2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Schwab2022.Examples`.
-/

namespace Schwab2022.Examples

open Data.Examples

def ex7a_jemals : LinguisticExample :=
  { id := "schwab2022_ex7a_jemals"
    source := ⟨"schwab-2022", "(7a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Bauer, der kein Pestizid verwendete, war jemals von dem Ernteertrag begeistert."
    discourseSegments := []
    glossedTokens := [("Der", "the"), ("Bauer", "farmer"), ("der", "who"), ("kein", "no"), ("Pestizid", "pesticide"), ("verwendete", "used"), ("war", "was"), ("jemals", "ever"), ("von", "by"), ("dem", "the"), ("Ernteertrag", "crop_yield"), ("begeistert", "amazed")]
    translation := "The farmer who used no pesticide was ever amazed by the crop yield."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("npi", "jemals"), ("npiType", "strengthening"), ("negation", "rc"), ("extraction", "subject"), ("illusion", "inconclusive")]
    comment := "Illusory licensing condition: negative quantifier inside the subject-extracted relative clause. Experiment 1 Bayes factor for an illusion: 9.65 (moderate evidence for an illusion)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex7b_jemals : LinguisticExample :=
  { id := "schwab2022_ex7b_jemals"
    source := ⟨"schwab-2022", "(7b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Kein Bauer, der das Pestizid verwendete, war jemals von dem Ernteertrag begeistert."
    discourseSegments := []
    glossedTokens := [("Kein", "no"), ("Bauer", "farmer"), ("der", "who"), ("das", "the"), ("Pestizid", "pesticide"), ("verwendete", "used"), ("war", "was"), ("jemals", "ever"), ("von", "by"), ("dem", "the"), ("Ernteertrag", "crop_yield"), ("begeistert", "amazed")]
    translation := "No farmer who used the pesticide was ever amazed by the crop yield."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("npi", "jemals"), ("npiType", "strengthening"), ("negation", "matrix"), ("extraction", "subject")]
    comment := "Grammatical: matrix negative quantifier licenses the NPI."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex7c_jemals : LinguisticExample :=
  { id := "schwab2022_ex7c_jemals"
    source := ⟨"schwab-2022", "(7c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Bauer, der das Pestizid verwendete, war jemals von dem Ernteertrag begeistert."
    discourseSegments := []
    glossedTokens := [("Der", "the"), ("Bauer", "farmer"), ("der", "who"), ("das", "the"), ("Pestizid", "pesticide"), ("verwendete", "used"), ("war", "was"), ("jemals", "ever"), ("von", "by"), ("dem", "the"), ("Ernteertrag", "crop_yield"), ("begeistert", "amazed")]
    translation := "The farmer who used the pesticide was ever amazed by the crop yield."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("npi", "jemals"), ("npiType", "strengthening"), ("negation", "none"), ("extraction", "subject")]
    comment := "Ungrammatical baseline: no negation."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex7a_sorecht : LinguisticExample :=
  { id := "schwab2022_ex7a_sorecht"
    source := ⟨"schwab-2022", "(7a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Bauer, der kein Pestizid verwendete, war so recht von dem Ernteertrag begeistert."
    discourseSegments := []
    glossedTokens := [("Der", "the"), ("Bauer", "farmer"), ("der", "who"), ("kein", "no"), ("Pestizid", "pesticide"), ("verwendete", "used"), ("war", "was"), ("so recht", "really"), ("von", "by"), ("dem", "the"), ("Ernteertrag", "crop_yield"), ("begeistert", "amazed")]
    translation := "The farmer who used no pesticide was really amazed by the crop yield."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("npi", "so recht"), ("npiType", "attenuating"), ("negation", "rc"), ("extraction", "subject"), ("illusion", "inconclusive")]
    comment := "Illusory licensing condition: negative quantifier inside the subject-extracted relative clause. Experiment 1 Bayes factor for an illusion: 0.43 (slightly favouring no illusion)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex7b_sorecht : LinguisticExample :=
  { id := "schwab2022_ex7b_sorecht"
    source := ⟨"schwab-2022", "(7b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Kein Bauer, der das Pestizid verwendete, war so recht von dem Ernteertrag begeistert."
    discourseSegments := []
    glossedTokens := [("Kein", "no"), ("Bauer", "farmer"), ("der", "who"), ("das", "the"), ("Pestizid", "pesticide"), ("verwendete", "used"), ("war", "was"), ("so recht", "really"), ("von", "by"), ("dem", "the"), ("Ernteertrag", "crop_yield"), ("begeistert", "amazed")]
    translation := "No farmer who used the pesticide was really amazed by the crop yield."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("npi", "so recht"), ("npiType", "attenuating"), ("negation", "matrix"), ("extraction", "subject")]
    comment := "Grammatical: matrix negative quantifier licenses the NPI."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex7c_sorecht : LinguisticExample :=
  { id := "schwab2022_ex7c_sorecht"
    source := ⟨"schwab-2022", "(7c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Bauer, der das Pestizid verwendete, war so recht von dem Ernteertrag begeistert."
    discourseSegments := []
    glossedTokens := [("Der", "the"), ("Bauer", "farmer"), ("der", "who"), ("das", "the"), ("Pestizid", "pesticide"), ("verwendete", "used"), ("war", "was"), ("so recht", "really"), ("von", "by"), ("dem", "the"), ("Ernteertrag", "crop_yield"), ("begeistert", "amazed")]
    translation := "The farmer who used the pesticide was really amazed by the crop yield."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "1"), ("npi", "so recht"), ("npiType", "attenuating"), ("negation", "none"), ("extraction", "subject")]
    comment := "Ungrammatical baseline: no negation."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex8a_jemals : LinguisticExample :=
  { id := "schwab2022_ex8a_jemals"
    source := ⟨"schwab-2022", "(8a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Sänger, den kein Label unterstützte, war jemals in der Musikbranche erfolgreich."
    discourseSegments := []
    glossedTokens := [("Der", "the"), ("Sänger", "singer"), ("den", "whom"), ("kein", "no"), ("Label", "label"), ("unterstützte", "supported"), ("war", "was"), ("jemals", "ever"), ("in", "in"), ("der", "the"), ("Musikbranche", "music_business"), ("erfolgreich", "successful")]
    translation := "The singer whom no label supported was ever successful in the music business."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("npi", "jemals"), ("npiType", "strengthening"), ("negation", "rc"), ("extraction", "object"), ("illusion", "attested")]
    comment := "Illusory licensing condition: negative quantifier inside the object-extracted relative clause. Experiment 2 Bayes factor for an illusion: 987.4 (very strong evidence for an illusion; posterior estimate 0.58, CrI [0.28, 0.89])."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex8b_jemals : LinguisticExample :=
  { id := "schwab2022_ex8b_jemals"
    source := ⟨"schwab-2022", "(8b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Kein Sänger, den das Label unterstützte, war jemals in der Musikbranche erfolgreich."
    discourseSegments := []
    glossedTokens := [("Kein", "no"), ("Sänger", "singer"), ("den", "whom"), ("das", "the"), ("Label", "label"), ("unterstützte", "supported"), ("war", "was"), ("jemals", "ever"), ("in", "in"), ("der", "the"), ("Musikbranche", "music_business"), ("erfolgreich", "successful")]
    translation := "No singer whom the label supported was ever successful in the music business."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("npi", "jemals"), ("npiType", "strengthening"), ("negation", "matrix"), ("extraction", "object")]
    comment := "Grammatical: matrix negative quantifier licenses the NPI."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex8c_jemals : LinguisticExample :=
  { id := "schwab2022_ex8c_jemals"
    source := ⟨"schwab-2022", "(8c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Sänger, den das Label unterstützte, war jemals in der Musikbranche erfolgreich."
    discourseSegments := []
    glossedTokens := [("Der", "the"), ("Sänger", "singer"), ("den", "whom"), ("das", "the"), ("Label", "label"), ("unterstützte", "supported"), ("war", "was"), ("jemals", "ever"), ("in", "in"), ("der", "the"), ("Musikbranche", "music_business"), ("erfolgreich", "successful")]
    translation := "The singer whom the label supported was ever successful in the music business."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("npi", "jemals"), ("npiType", "strengthening"), ("negation", "none"), ("extraction", "object")]
    comment := "Ungrammatical baseline: no negation."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex8a_sorecht : LinguisticExample :=
  { id := "schwab2022_ex8a_sorecht"
    source := ⟨"schwab-2022", "(8a)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Sänger, den kein Label unterstützte, war so recht in der Musikbranche erfolgreich."
    discourseSegments := []
    glossedTokens := [("Der", "the"), ("Sänger", "singer"), ("den", "whom"), ("kein", "no"), ("Label", "label"), ("unterstützte", "supported"), ("war", "was"), ("so recht", "really"), ("in", "in"), ("der", "the"), ("Musikbranche", "music_business"), ("erfolgreich", "successful")]
    translation := "The singer whom no label supported was really successful in the music business."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("npi", "so recht"), ("npiType", "attenuating"), ("negation", "rc"), ("extraction", "object"), ("illusion", "absent")]
    comment := "Illusory licensing condition: negative quantifier inside the object-extracted relative clause. Experiment 2 Bayes factor for an illusion: 0.33 (moderate evidence for no illusion; posterior estimate -0.09, CrI [-0.37, 0.20])."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex8b_sorecht : LinguisticExample :=
  { id := "schwab2022_ex8b_sorecht"
    source := ⟨"schwab-2022", "(8b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Kein Sänger, den das Label unterstützte, war so recht in der Musikbranche erfolgreich."
    discourseSegments := []
    glossedTokens := [("Kein", "no"), ("Sänger", "singer"), ("den", "whom"), ("das", "the"), ("Label", "label"), ("unterstützte", "supported"), ("war", "was"), ("so recht", "really"), ("in", "in"), ("der", "the"), ("Musikbranche", "music_business"), ("erfolgreich", "successful")]
    translation := "No singer whom the label supported was really successful in the music business."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("npi", "so recht"), ("npiType", "attenuating"), ("negation", "matrix"), ("extraction", "object")]
    comment := "Grammatical: matrix negative quantifier licenses the NPI."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex8c_sorecht : LinguisticExample :=
  { id := "schwab2022_ex8c_sorecht"
    source := ⟨"schwab-2022", "(8c)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Sänger, den das Label unterstützte, war so recht in der Musikbranche erfolgreich."
    discourseSegments := []
    glossedTokens := [("Der", "the"), ("Sänger", "singer"), ("den", "whom"), ("das", "the"), ("Label", "label"), ("unterstützte", "supported"), ("war", "was"), ("so recht", "really"), ("in", "in"), ("der", "the"), ("Musikbranche", "music_business"), ("erfolgreich", "successful")]
    translation := "The singer whom the label supported was really successful in the music business."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("experiment", "2"), ("npi", "so recht"), ("npiType", "attenuating"), ("negation", "none"), ("extraction", "object")]
    comment := "Ungrammatical baseline: no negation."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex7a_jemals, ex7b_jemals, ex7c_jemals, ex7a_sorecht, ex7b_sorecht, ex7c_sorecht, ex8a_jemals, ex8b_jemals, ex8c_jemals, ex8a_sorecht, ex8b_sorecht, ex8c_sorecht]

end Schwab2022.Examples
