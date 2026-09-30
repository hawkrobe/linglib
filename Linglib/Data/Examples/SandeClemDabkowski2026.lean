module

public import Linglib.Data.Examples.Schema

/-!
# `SandeClemDabkowski2026` — typed example data

Auto-generated from `Linglib/Data/Examples/SandeClemDabkowski2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace SandeClemDabkowski2026.Examples`.
-/

@[expose] public section

namespace SandeClemDabkowski2026.Examples

def ex11a : Datum :=
  { id := "sandeclemdabkowski2026_ex11a"
    source := ⟨"sande-clem-dabkowski-2026", "(11a)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "e ji ɟaci joku-ni"
    glossedTokens := [("e", "1SG.NOM"), ("ji", "FUT"), ("ɟaci", "Djatchi"), ("joku-ni", "PART-see")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "SAuxOPartV"), ("pattern", "S Aux O Part V"), ("verb", "ni"), ("particleATR", "plus")] }

def ex11b : Datum :=
  { id := "sandeclemdabkowski2026_ex11b"
    source := ⟨"sande-clem-dabkowski-2026", "(11b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "e ni ɟaci jɔkʊ"
    glossedTokens := [("e", "1SG.NOM"), ("ni", "see.PFV"), ("ɟaci", "Djatchi"), ("jɔkʊ", "PART")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "SVOPart"), ("pattern", "S V O Part"), ("verb", "ni"), ("particleATR", "minus")] }

def ex11c : Datum :=
  { id := "sandeclemdabkowski2026_ex11c"
    source := ⟨"sande-clem-dabkowski-2026", "(11c)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "e joku-ni ɟaci"
    glossedTokens := [("e", "1SG.NOM"), ("joku-ni", "PART-see.PFV"), ("ɟaci", "Djatchi")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "S Part V O")] }

def ex12b : Datum :=
  { id := "sandeclemdabkowski2026_ex12b"
    source := ⟨"sande-clem-dabkowski-2026", "(12b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "ɟaci ji ɔnɛ ɡbɔɡɔ jɔkʊ-ŋwɔsa"
    glossedTokens := [("ɟaci", "Djatchi"), ("ji", "FUT"), ("ɔnɛ", "3SG.POSS"), ("ɡbɔɡɔ", "leg"), ("jɔkʊ-ŋwɔsa", "PART-scrape")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "SAuxOPartV"), ("pattern", "S Aux O Part V"), ("verb", "ngwOsa"), ("particleATR", "minus")] }

def ex13b : Datum :=
  { id := "sandeclemdabkowski2026_ex13b"
    source := ⟨"sande-clem-dabkowski-2026", "(13b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "ɟaci ŋwɔsa ɔnɛ ɡbɔɡɔ jɔkʊ"
    glossedTokens := [("ɟaci", "Djatchi"), ("ŋwɔsa", "scrape.PFV"), ("ɔnɛ", "3SG.POSS"), ("ɡbɔɡɔ", "leg"), ("jɔkʊ", "PART")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "SVOPart"), ("pattern", "S V O Part"), ("verb", "ngwOsa"), ("particleATR", "minus")] }

def ex21a : Datum :=
  { id := "sandeclemdabkowski2026_ex21a"
    source := ⟨"sande-clem-dabkowski-2026", "(21a)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "jɔkʊ ɔ ni=ɔ"
    glossedTokens := [("jɔkʊ", "PART"), ("ɔ", "3SG.NOM"), ("ni=ɔ", "see.PFV=3SG.ACC")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "PartSVO"), ("pattern", "Part S V O"), ("verb", "ni"), ("particleATR", "minus")] }

def ex21b : Datum :=
  { id := "sandeclemdabkowski2026_ex21b"
    source := ⟨"sande-clem-dabkowski-2026", "(21b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "joku-ni ɔ ni=ɔ"
    glossedTokens := [("joku-ni", "PART-see"), ("ɔ", "3SG.NOM"), ("ni=ɔ", "see.PFV=3SG.ACC")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "Part V S V O")] }

def ex21c : Datum :=
  { id := "sandeclemdabkowski2026_ex21c"
    source := ⟨"sande-clem-dabkowski-2026", "(21c)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "ni ɔ ni=ɔ jɔkʊ"
    glossedTokens := [("ni", "see"), ("ɔ", "3SG.NOM"), ("ni=ɔ", "see.PFV=3SG.ACC"), ("jɔkʊ", "PART")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "V S V O Part")] }

def ex21d : Datum :=
  { id := "sandeclemdabkowski2026_ex21d"
    source := ⟨"sande-clem-dabkowski-2026", "(21d)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "ni ɔ =ɔ jɔkʊ"
    glossedTokens := [("ni", "see"), ("ɔ", "3SG.NOM"), ("=ɔ", "3SG.ACC"), ("jɔkʊ", "PART")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "V S O Part")] }

def ex21e : Datum :=
  { id := "sandeclemdabkowski2026_ex21e"
    source := ⟨"sande-clem-dabkowski-2026", "(21e)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "joku ɔ ni=ɔ jɔkʊ"
    glossedTokens := [("joku", "PART"), ("ɔ", "3SG.NOM"), ("ni=ɔ", "see.PFV=3SG.ACC"), ("jɔkʊ", "PART")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "Part S V O Part")] }

def ex22 : Datum :=
  { id := "sandeclemdabkowski2026_ex22"
    source := ⟨"sande-clem-dabkowski-2026", "(22)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "joku ɔ ji ɟaci ni"
    glossedTokens := [("joku", "PART"), ("ɔ", "3SG.NOM"), ("ji", "FUT"), ("ɟaci", "Djatchi"), ("ni", "see")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "PartSAuxOV"), ("pattern", "Part S Aux O V"), ("verb", "ni"), ("particleATR", "plus")] }

def ex24b : Datum :=
  { id := "sandeclemdabkowski2026_ex24b"
    source := ⟨"sande-clem-dabkowski-2026", "(24b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "joku ɔ ji ɟaci ni"
    glossedTokens := [("joku", "PART"), ("ɔ", "3SG.NOM"), ("ji", "FUT"), ("ɟaci", "Djatchi"), ("ni", "see")]
    context := ""
    judgment := .acceptable
    alternatives := [("jɔkʊ ɔ ji ɟaci ni", .ungrammatical)]
    readings := []
    paperFeatures := [("order", "PartSAuxOV"), ("pattern", "Part S Aux O V"), ("verb", "ni"), ("particleATR", "plus")] }

def ex49a : Datum :=
  { id := "sandeclemdabkowski2026_ex49a"
    source := ⟨"sande-clem-dabkowski-2026", "(49a)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "fas w-ale"
    glossedTokens := [("fas", "horse"), ("w-ale", "CL-DEM.DIST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "localDP"), ("headATR", "minus"), ("demATR", "minus")] }

def ex49b : Datum :=
  { id := "sandeclemdabkowski2026_ex49b"
    source := ⟨"sande-clem-dabkowski-2026", "(49b)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "béy w-ëlé"
    glossedTokens := [("béy", "goat"), ("w-ëlé", "CL-DEM.DIST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "localDP"), ("headATR", "plus"), ("demATR", "plus")] }

def ex50a : Datum :=
  { id := "sandeclemdabkowski2026_ex50a"
    source := ⟨"sande-clem-dabkowski-2026", "(50a)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "xaj b-u weex b-ale"
    glossedTokens := [("xaj", "dog"), ("b-u", "CL-REL"), ("weex", "be.white"), ("b-ale", "CL-DEM.DIST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "relClause"), ("headATR", "minus"), ("stativeATR", "minus"), ("demATR", "minus")] }

def ex50b : Datum :=
  { id := "sandeclemdabkowski2026_ex50b"
    source := ⟨"sande-clem-dabkowski-2026", "(50b)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "béy w-u réy w-ëlé"
    glossedTokens := [("béy", "goat"), ("w-u", "CL-REL"), ("réy", "be.big"), ("w-ëlé", "CL-DEM.DIST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "relClause"), ("headATR", "plus"), ("stativeATR", "plus"), ("demATR", "plus")] }

def ex50c : Datum :=
  { id := "sandeclemdabkowski2026_ex50c"
    source := ⟨"sande-clem-dabkowski-2026", "(50c)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "xaj b-u réy b-ale"
    glossedTokens := [("xaj", "dog"), ("b-u", "CL-REL"), ("réy", "be.big"), ("b-ale", "CL-DEM.DIST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "relClause"), ("headATR", "minus"), ("stativeATR", "plus"), ("demATR", "minus")] }

def ex50d : Datum :=
  { id := "sandeclemdabkowski2026_ex50d"
    source := ⟨"sande-clem-dabkowski-2026", "(50d)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "béy w-u weex w-ëlé"
    glossedTokens := [("béy", "goat"), ("w-u", "CL-REL"), ("weex", "be.white"), ("w-ëlé", "CL-DEM.DIST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "relClause"), ("headATR", "plus"), ("stativeATR", "minus"), ("demATR", "plus")] }

def all : List Datum := [ex11a, ex11b, ex11c, ex12b, ex13b, ex21a, ex21b, ex21c, ex21d, ex21e, ex22, ex24b, ex49a, ex49b, ex50a, ex50b, ex50c, ex50d]

end SandeClemDabkowski2026.Examples
