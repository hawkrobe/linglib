module

public import Linglib.Data.Examples.Schema

/-!
# `Nadathur2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Nadathur2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Nadathur2023.Examples`.
-/

@[expose] public section

namespace Nadathur2023.Examples

open Data.Examples

def ex_2a : Datum :=
  { id := "nadathur2023_2a"
    source := ⟨"nadathur-2023-implicatives", "(2a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Eman onnistu-i kuitenkin pakenema-an."
    glossedTokens := [("Eman", "Eman"), ("onnistu-i", "succeed-PST.3SG"), ("kuitenkin", "however"), ("pakenema-an", "flee-INF.ILL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "onnistua"), ("matrix", "positive"), ("entails", "complement")] }

def ex_2b : Datum :=
  { id := "nadathur2023_2b"
    source := ⟨"nadathur-2023-implicatives", "(2b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Eman e-i onnistu-nut kuitenkaan pakenema-an."
    glossedTokens := [("Eman", "Eman"), ("e-i", "NEG-3SG"), ("onnistu-nut", "succeed-SG.PP"), ("kuitenkaan", "however"), ("pakenema-an", "flee-INF.ILL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "onnistua"), ("matrix", "negated"), ("entails", "negation")] }

def ex_4a : Datum :=
  { id := "nadathur2023_4a"
    source := ⟨"nadathur-2023-implicatives", "(4a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno uskals-i avat-a ove-n."
    glossedTokens := [("Juno", "Juno"), ("uskals-i", "dare-PST.3SG"), ("avat-a", "open-INF"), ("ove-n", "door-GEN/ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "uskaltaa"), ("matrix", "positive"), ("entails", "complement")] }

def ex_4b : Datum :=
  { id := "nadathur2023_4b"
    source := ⟨"nadathur-2023-implicatives", "(4b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno e-i uskalta-nut avat-a ove-a."
    glossedTokens := [("Juno", "Juno"), ("e-i", "NEG-3SG"), ("uskalta-nut", "dare-SG.PP"), ("avat-a", "open-INF"), ("ove-a", "door-PART")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "uskaltaa"), ("matrix", "negated"), ("entails", "negation")] }

def ex_5a : Datum :=
  { id := "nadathur2023_5a"
    source := ⟨"nadathur-2023-implicatives", "(5a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Sampo jakso-i noust-a."
    glossedTokens := [("Sampo", "Sampo"), ("jakso-i", "have.strength-PST.3SG"), ("noust-a", "rise-INF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "jaksaa"), ("matrix", "positive"), ("entails", "nothing")] }

def ex_5b : Datum :=
  { id := "nadathur2023_5b"
    source := ⟨"nadathur-2023-implicatives", "(5b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Sampo e-i jaksa-nut noust-a."
    glossedTokens := [("Sampo", "Sampo"), ("e-i", "NEG-3SG"), ("jaksa-nut", "have.strength-PP.SG"), ("noust-a", "rise-INF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "jaksaa"), ("matrix", "negated"), ("entails", "negation")] }

def ex_10a : Datum :=
  { id := "nadathur2023_10a"
    source := ⟨"nadathur-2023-implicatives", "(10a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän viits-i vastat-a."
    glossedTokens := [("Hän", "he.NOM"), ("viits-i", "bother-PST.3SG"), ("vastat-a", "answer-INF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "viitsiä"), ("matrix", "positive"), ("entails", "complement")] }

def ex_10b : Datum :=
  { id := "nadathur2023_10b"
    source := ⟨"nadathur-2023-implicatives", "(10b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän e-i viitsi-nyt vastat-a."
    glossedTokens := [("Hän", "he.NOM"), ("e-i", "NEG-3SG"), ("viitsi-nyt", "bother-PP.SG"), ("vastat-a", "answer-INF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "viitsiä"), ("matrix", "negated"), ("entails", "negation")] }

def ex_11a : Datum :=
  { id := "nadathur2023_11a"
    source := ⟨"nadathur-2023-implicatives", "(11a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Marja maltto-i odotta-a."
    glossedTokens := [("Marja", "Marja"), ("maltto-i", "have.patience-PST.3SG"), ("odotta-a", "wait-INF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "malttaa"), ("matrix", "positive"), ("entails", "complement")] }

def ex_11b : Datum :=
  { id := "nadathur2023_11b"
    source := ⟨"nadathur-2023-implicatives", "(11b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Marja e-i maltta-nut odotta-a."
    glossedTokens := [("Marja", "Marja"), ("e-i", "NEG-3SG"), ("maltta-nut", "have.patience-SG.PP"), ("odotta-a", "wait-INF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "malttaa"), ("matrix", "negated"), ("entails", "negation")] }

def ex_27a : Datum :=
  { id := "nadathur2023_27a"
    source := ⟨"nadathur-2023-implicatives", "(27a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän henno-i tappa-a kissa-n."
    glossedTokens := [("Hän", "he.NOM"), ("henno-i", "have.heart-PST.3SG"), ("tappa-a", "kill-INF"), ("kissa-n", "cat-GEN/ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hennoa"), ("matrix", "positive"), ("entails", "complement")] }

def ex_27b : Datum :=
  { id := "nadathur2023_27b"
    source := ⟨"nadathur-2023-implicatives", "(27b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän e-i henno-nut tappa-a kissa-a."
    glossedTokens := [("Hän", "he.NOM"), ("e-i", "NEG-3SG"), ("henno-nut", "have.heart-SG.PP"), ("tappa-a", "kill-INF"), ("kissa-a", "cat-PART")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hennoa"), ("matrix", "negated"), ("entails", "negation")] }

def ex_29a : Datum :=
  { id := "nadathur2023_29a"
    source := ⟨"nadathur-2023-implicatives", "(29a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Maarit pysty-i tappelema-an."
    glossedTokens := [("Maarit", "Maarit"), ("pysty-i", "able-PST.3SG"), ("tappelema-an", "fight-INF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "pystyä"), ("matrix", "positive"), ("entails", "nothing")] }

def ex_29b : Datum :=
  { id := "nadathur2023_29b"
    source := ⟨"nadathur-2023-implicatives", "(29b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Maarit e-i pysty-nyt tappelema-an."
    glossedTokens := [("Maarit", "Maarit"), ("e-i", "NEG-3SG"), ("pysty-nyt", "able-SG.PP"), ("tappelema-an", "fight-INF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "pystyä"), ("matrix", "negated"), ("entails", "negation")] }

def ex_30a : Datum :=
  { id := "nadathur2023_30a"
    source := ⟨"nadathur-2023-implicatives", "(30a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Freija mahtu-i kulke-ma-an ove-sta."
    glossedTokens := [("Freija", "Freija"), ("mahtu-i", "fit-PST.3SG"), ("kulke-ma-an", "go-INF-ILL"), ("ove-sta", "door-ELA")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "mahtua"), ("matrix", "positive"), ("entails", "nothing")] }

def ex_30b : Datum :=
  { id := "nadathur2023_30b"
    source := ⟨"nadathur-2023-implicatives", "(30b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Freija e-i mahtu-nut kulke-ma-an ove-sta."
    glossedTokens := [("Freija", "Freija"), ("e-i", "NEG-3SG"), ("mahtu-nut", "fit-PP.SG"), ("kulke-ma-an", "go-INF-ILL"), ("ove-sta", "door-ELA")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "mahtua"), ("matrix", "negated"), ("entails", "negation")] }

def ex_44a : Datum :=
  { id := "nadathur2023_44a"
    source := ⟨"nadathur-2023-implicatives", "(44a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän laiminlö-i korjat-a virhee-n."
    glossedTokens := [("Hän", "he.NOM"), ("laiminlö-i", "neglect-PST.3SG"), ("korjat-a", "repair-INF"), ("virhee-n", "error-GEN/ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "laiminlyödä"), ("matrix", "positive"), ("entails", "negation")] }

def ex_44b : Datum :=
  { id := "nadathur2023_44b"
    source := ⟨"nadathur-2023-implicatives", "(44b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Hän e-i laiminlyö-nyt korjat-a virhe-ttä."
    glossedTokens := [("Hän", "he.NOM"), ("e-i", "NEG-3SG"), ("laiminlyö-nyt", "neglect-PP.SG"), ("korjat-a", "repair-INF"), ("virhe-ttä", "error-PART")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "laiminlyödä"), ("matrix", "negated"), ("entails", "complement")] }

def ex_46a : Datum :=
  { id := "nadathur2023_46a"
    source := ⟨"nadathur-2023-implicatives", "(46a)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno epärö-i otta-a osa-a kilpailu-un."
    glossedTokens := [("Juno", "Juno"), ("epärö-i", "hesitate-PST.3SG"), ("otta-a", "take-INF"), ("osa-a", "part-PART"), ("kilpailu-un", "race-ILL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "epäröidä"), ("matrix", "positive"), ("entails", "nothing")] }

def ex_46b : Datum :=
  { id := "nadathur2023_46b"
    source := ⟨"nadathur-2023-implicatives", "(46b)"⟩
    reportedIn := none
    language := "finn1318"
    primaryText := "Juno e-i epäröi-nyt otta-a osa-a kilpailu-un."
    glossedTokens := [("Juno", "Juno"), ("e-i", "NEG-3SG"), ("epäröi-nyt", "hesitate-PP.SG"), ("otta-a", "take-INF"), ("osa-a", "part-PART"), ("kilpailu-un", "race-ILL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "epäröidä"), ("matrix", "negated"), ("entails", "complement")] }

def all : List Datum := [ex_2a, ex_2b, ex_4a, ex_4b, ex_5a, ex_5b, ex_10a, ex_10b, ex_11a, ex_11b, ex_27a, ex_27b, ex_29a, ex_29b, ex_30a, ex_30b, ex_44a, ex_44b, ex_46a, ex_46b]

end Nadathur2023.Examples
