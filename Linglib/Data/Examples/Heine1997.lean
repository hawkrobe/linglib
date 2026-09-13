import Linglib.Data.Examples.Schema

/-!
# `Heine1997` — typed example data

Auto-generated from `Linglib/Data/Examples/Heine1997.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Heine1997.Examples`.
-/

namespace Heine1997.Examples

open Data.Examples

def ex_2_pt : LinguisticExample :=
  { id := "heine1997_2_pt"
    source := ⟨"heine-1997", "(2)"⟩
    reportedIn := none
    language := "port1283"
    primaryText := "O menino tem fome."
    discourseSegments := []
    glossedTokens := [("O", "the"), ("menino", "child"), ("tem", "takes/has"), ("fome", "hunger")]
    translation := "The child is hungry."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "action")]
    comment := "Action Schema: the verb 'take/have' with the possessor as subject."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_73a : LinguisticExample :=
  { id := "heine1997_73a"
    source := ⟨"heine-1997", "(73a)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Lampa stoit u okna."
    discourseSegments := []
    glossedTokens := []
    translation := "The lamp stands by the window."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("location", .acceptable)]
    paperFeatures := [("schema", "location"), ("source", "true"), ("target", "false")]
    comment := "Stage I of the Overlap Model: u is an adessive preposition, the structure expresses 'Y is at X'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_73b : LinguisticExample :=
  { id := "heine1997_73b"
    source := ⟨"heine-1997", "(73b)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Mašina u Peti."
    discourseSegments := []
    glossedTokens := []
    translation := "The car is with/at Peter."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("location", .acceptable)]
    paperFeatures := [("schema", "location"), ("source", "true"), ("target", "false")]
    comment := "Stage I: locative meaning only."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_73c : LinguisticExample :=
  { id := "heine1997_73c"
    source := ⟨"heine-1997", "(73c)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "Sejčas u Markovyx gripp."
    discourseSegments := []
    glossedTokens := []
    translation := "There is flu at the Markovs. / The Markovs have the flu now."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("There is flu at the Markovs.", .acceptable), ("The Markovs have the flu now.", .acceptable)]
    paperFeatures := [("schema", "location"), ("source", "true"), ("target", "true")]
    comment := "Stage II: the construction is ambiguous between the Location Schema and the possessive target."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_73d : LinguisticExample :=
  { id := "heine1997_73d"
    source := ⟨"heine-1997", "(73d)"⟩
    reportedIn := none
    language := "russ1263"
    primaryText := "U Peti est' mašina."
    discourseSegments := []
    glossedTokens := []
    translation := "Peter has a car."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possession", .acceptable)]
    paperFeatures := [("schema", "location"), ("source", "false"), ("target", "true")]
    comment := "Stage III: interpreted only with reference to the possessive target schema."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_84a : LinguisticExample :=
  { id := "heine1997_84a"
    source := ⟨"heine-1997", "(84a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The car is mine."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "equation"), ("notion", "permanent")]
    comment := "The Equation Schema ('Y is X's') expresses permanent possession, like 'I own a car'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_84b : LinguisticExample :=
  { id := "heine1997_84b"
    source := ⟨"heine-1997", "(84b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "?Two sisters are mine."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "equation"), ("notion", "inalienable")]
    comment := "Marginal with inalienable possession, like '?I own two sisters'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_84c : LinguisticExample :=
  { id := "heine1997_84c"
    source := ⟨"heine-1997", "(84c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "?The cold is mine."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "equation"), ("notion", "abstract")]
    comment := "Marginal with abstract possession, like '?I own a cold'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_84d : LinguisticExample :=
  { id := "heine1997_84d"
    source := ⟨"heine-1997", "(84d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "?Two bedrooms are my house's."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "equation"), ("notion", "inanimateInalienable")]
    comment := "Marginal with inanimate inalienable possession, like '?My house owns two bedrooms'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_85a : LinguisticExample :=
  { id := "heine1997_85a"
    source := ⟨"heine-1997", "(85a)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "pennu vaːḍi-daggara undi"
    discourseSegments := []
    glossedTokens := [("pennu", "pen"), ("vaːḍi-daggara", "him-at"), ("undi", "is")]
    translation := "He has a pen (with him, which may not necessarily belong to him)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "location"), ("notion", "physical")]
    comment := "The Location Schema, grammaticalized for physical and temporary possession."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_85b : LinguisticExample :=
  { id := "heine1997_85b"
    source := ⟨"heine-1997", "(85b)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "pennu vaːḍi-ki undi"
    discourseSegments := []
    glossedTokens := [("pennu", "pen"), ("vaːḍi-ki", "him-to"), ("undi", "is")]
    translation := "He has a pen (which belongs to him)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "goal"), ("notion", "permanent")]
    comment := "The Goal sub-schema of Existence for permanent possession."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_85c : LinguisticExample :=
  { id := "heine1997_85c"
    source := ⟨"heine-1997", "(85c)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "reṇḍu kaḷḷu naː-ku unnaːy"
    discourseSegments := []
    glossedTokens := [("reṇḍu", "two"), ("kaḷḷu", "eyes"), ("naː-ku", "me-to"), ("unnaːy", "are")]
    translation := "I have two eyes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "goal"), ("notion", "inalienable")]
    comment := "The Goal sub-schema for inalienable possession."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_85d : LinguisticExample :=
  { id := "heine1997_85d"
    source := ⟨"heine-1997", "(85d)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "iddaru pillalu naː-ku unnaːru"
    discourseSegments := []
    glossedTokens := [("iddaru", "two"), ("pillalu", "children"), ("naː-ku", "me-to"), ("unnaːru", "are")]
    translation := "I have two children."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "goal"), ("notion", "inalienable")]
    comment := "The Goal sub-schema for inalienable (kinship) possession."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_85e : LinguisticExample :=
  { id := "heine1997_85e"
    source := ⟨"heine-1997", "(85e)"⟩
    reportedIn := none
    language := "telu1262"
    primaryText := "kommalu ceṭṭu-ki unnaːy"
    discourseSegments := []
    glossedTokens := [("kommalu", "branches"), ("ceṭṭu-ki", "tree-to"), ("unnaːy", "are")]
    translation := "The tree has branches."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "goal"), ("notion", "inanimateInalienable")]
    comment := "The Goal sub-schema for inanimate inalienable possession."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_86a : LinguisticExample :=
  { id := "heine1997_86a"
    source := ⟨"heine-1997", "(86a)"⟩
    reportedIn := none
    language := "ewee1241"
    primaryText := "dɔ li na Kofi"
    discourseSegments := []
    glossedTokens := [("dɔ", "work"), ("li", "exist"), ("na", "to"), ("Kofi", "Kofi")]
    translation := "Kofi has work."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "goal"), ("possessee", "indefinite"), ("notion", "permanent")]
    comment := "With an indefinite possessee the Goal construction expresses permanent possession."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_86b : LinguisticExample :=
  { id := "heine1997_86b"
    source := ⟨"heine-1997", "(86b)"⟩
    reportedIn := none
    language := "ewee1241"
    primaryText := "dɔ la li na Kofi"
    discourseSegments := []
    glossedTokens := [("dɔ", "work"), ("la", "the"), ("li", "exist"), ("na", "to"), ("Kofi", "Kofi")]
    translation := "Kofi has work to do (the work is there for Kofi)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "goal"), ("possessee", "definite"), ("notion", "physical")]
    comment := "With a definite possessee the same construction denotes physical possession."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_87a : LinguisticExample :=
  { id := "heine1997_87a"
    source := ⟨"heine-1997", "(87a)"⟩
    reportedIn := none
    language := "ewee1241"
    primaryText := "ga le Kofi si"
    discourseSegments := []
    glossedTokens := [("ga", "money"), ("le", "be.at"), ("Kofi", "Kofi"), ("si", "hand")]
    translation := "Kofi has money."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "location"), ("possessee", "indefinite"), ("notion", "permanent")]
    comment := "The Location construction with an indefinite possessee: permanent possession."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_87b : LinguisticExample :=
  { id := "heine1997_87b"
    source := ⟨"heine-1997", "(87b)"⟩
    reportedIn := none
    language := "ewee1241"
    primaryText := "ga la le Kofi si"
    discourseSegments := []
    glossedTokens := [("ga", "money"), ("la", "the"), ("le", "be.at"), ("Kofi", "Kofi"), ("si", "hand")]
    translation := "The money is with Kofi."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("schema", "location"), ("possessee", "definite"), ("notion", "physical")]
    comment := "With a definite possessee, physical possession."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_2_pt, ex_73a, ex_73b, ex_73c, ex_73d, ex_84a, ex_84b, ex_84c, ex_84d, ex_85a, ex_85b, ex_85c, ex_85d, ex_85e, ex_86a, ex_86b, ex_87a, ex_87b]

end Heine1997.Examples
