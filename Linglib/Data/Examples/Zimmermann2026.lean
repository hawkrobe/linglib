import Linglib.Data.Examples.Schema

/-!
# `Zimmermann2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Zimmermann2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Zimmermann2026.Examples`.
-/

namespace Zimmermann2026.Examples

open Data.Examples

def ex_12 : LinguisticExample :=
  { id := "zimmermann2026_12"
    source := ⟨"zimmermann-2026", "(12)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "John ya karanta wani littafi, amma ban san ko wanne ba ne."
    discourseSegments := []
    glossedTokens := [("John", "John"), ("ya", "3SG.M.PFV"), ("karanta", "read"), ("wani", "INDEF"), ("littafi", "book"), ("amma", "but"), ("ban", "NEG-1SG"), ("san", "know"), ("ko", "Q"), ("wanne", "which"), ("ba", "NEG"), ("ne", "COP")]
    translation := "John has read a certain book, but I don't know which."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "sluicing antecedent")]
    comment := "Both the bare and the wani-marked indefinite serve as sluicing antecedents."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_13a : LinguisticExample :=
  { id := "zimmermann2026_13a"
    source := ⟨"zimmermann-2026", "(13a)"⟩
    reportedIn := some ⟨"zimmermann-2014", ""⟩
    language := "haus1257"
    primaryText := "Audù bà-i sàyi wani kiifii ba."
    discourseSegments := []
    glossedTokens := [("Audù", "Audu"), ("bà-i", "NEG-3SG.M"), ("sàyi", "buy"), ("wani", "INDEF"), ("kiifii", "fish"), ("ba", "NEG")]
    translation := "Audu didn't buy some fish."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("scope", "wide"), ("context", "Audu bought a lot of fish, but")]
    comment := "Wide-scope context: the marker wani is required; the bare NP would force the narrow-scope reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_13b : LinguisticExample :=
  { id := "zimmermann2026_13b"
    source := ⟨"zimmermann-2026", "(13b)"⟩
    reportedIn := some ⟨"zimmermann-2014", ""⟩
    language := "haus1257"
    primaryText := "Audù bà-i sàyi wani kiifii ba."
    discourseSegments := []
    glossedTokens := [("Audù", "Audu"), ("bà-i", "NEG-3SG.M"), ("sàyi", "buy"), ("wani", "INDEF"), ("kiifii", "fish"), ("ba", "NEG")]
    translation := "Audu didn't buy any fish."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("scope", "narrow"), ("context", "the market was closed, so")]
    comment := "Narrow-scope context: wani phrases may also scope below negation, like the bare NP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "zimmermann2026_14"
    source := ⟨"zimmermann-2026", "(14)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Me-re-kɔ-tɔ mpaboa bí."
    discourseSegments := []
    glossedTokens := [("Me-re-kɔ-tɔ", "1SG-PROG-go-buy"), ("mpaboa", "shoes"), ("bí", "INDEF")]
    translation := "I am going to buy a certain pair of shoes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "specificity")]
    comment := "The marker bí triggers a specificity inference in non-modal environments; cited from Amfo (2010)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15 : LinguisticExample :=
  { id := "zimmermann2026_15"
    source := ⟨"zimmermann-2026", "(15)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Me-n-ni fish bí."
    discourseSegments := []
    glossedTokens := [("Me-n-ni", "1SG-NEG-eat"), ("fish", "fish"), ("bí", "INDEF")]
    translation := "I don't eat a certain kind of fish."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("scope", "wide only")]
    comment := "The narrow-scope reading, that I don't eat any fish, is unavailable: bí phrases must outscope negation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17 : LinguisticExample :=
  { id := "zimmermann2026_17"
    source := ⟨"zimmermann-2026", "(17)"⟩
    reportedIn := none
    language := "gaaa1244"
    primaryText := "Nikasel ko kε e-wolo ko ni e-ma lε e-ya-aa."
    discourseSegments := []
    glossedTokens := [("Nikasel", "student"), ("ko", "INDEF"), ("kε", "take"), ("e-wolo", "3SG.POSS-letter"), ("ko", "INDEF"), ("ni", "REL"), ("e-ma", "3SG-write"), ("lε", "DEF"), ("e-ya-aa", "3SG-send-NEG")]
    translation := "No student sent every letter (s)he wrote."
    context := "There were three students: Mary, Sue, and Joe. All of them wrote letters, but none of them sent all of them."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "ko"), ("reading", "existentially closed choice function")]
    comment := "True in the context; cited from Renans (2018). Unavailable for Akan bí."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18 : LinguisticExample :=
  { id := "zimmermann2026_18"
    source := ⟨"zimmermann-2026", "(18)"⟩
    reportedIn := none
    language := "akan1250"
    primaryText := "Papa bí nó bisa me me nɔma."
    discourseSegments := []
    glossedTokens := [("Papa", "man"), ("bí", "INDEF"), ("nó", "DEF"), ("bisa", "ask-PST"), ("me", "1SG"), ("me", "1SG"), ("nɔma", "number")]
    translation := "After the party, that certain man asked me for my number."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("co-occurrence", "INDEF and DEF")]
    comment := "Cited from Bombi et al. (2019)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_19 : LinguisticExample :=
  { id := "zimmermann2026_19"
    source := ⟨"zimmermann-2026", "(19)"⟩
    reportedIn := none
    language := "haus1257"
    primaryText := "tùuluu yaa fashèe"
    discourseSegments := []
    glossedTokens := [("tùuluu", "pot"), ("yaa", "3SG.PFV"), ("fashèe", "break")]
    translation := "The/A water pot broke."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("bare NP", "definite or indefinite")]
    comment := "Cited from Newman (2000); a uniqueness-based definite reading of a bare NP in topical subject position."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_12, ex_13a, ex_13b, ex_14, ex_15, ex_17, ex_18, ex_19]

end Zimmermann2026.Examples
