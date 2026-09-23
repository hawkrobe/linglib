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

open Data.Examples

def ex11a : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex11a"
    source := ⟨"sande-clem-dabkowski-2026", "(11a)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "e ji ɟaci joku-ni"
    discourseSegments := []
    glossedTokens := [("e", "1SG.NOM"), ("ji", "FUT"), ("ɟaci", "Djatchi"), ("joku-ni", "PART-see")]
    translation := "I will see Djatchi."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "SAuxOPartV"), ("pattern", "S Aux O Part V"), ("verb", "ni"), ("particleATR", "plus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex11b : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex11b"
    source := ⟨"sande-clem-dabkowski-2026", "(11b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "e ni ɟaci jɔkʊ"
    discourseSegments := []
    glossedTokens := [("e", "1SG.NOM"), ("ni", "see.PFV"), ("ɟaci", "Djatchi"), ("jɔkʊ", "PART")]
    translation := "I saw Djatchi."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "SVOPart"), ("pattern", "S V O Part"), ("verb", "ni"), ("particleATR", "minus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex11c : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex11c"
    source := ⟨"sande-clem-dabkowski-2026", "(11c)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "e joku-ni ɟaci"
    discourseSegments := []
    glossedTokens := [("e", "1SG.NOM"), ("joku-ni", "PART-see.PFV"), ("ɟaci", "Djatchi")]
    translation := "I saw Djatchi."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "S Part V O")]
    comment := "The particle cannot surface with the verb in the post-subject position."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex12b : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex12b"
    source := ⟨"sande-clem-dabkowski-2026", "(12b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "ɟaci ji ɔnɛ ɡbɔɡɔ jɔkʊ-ŋwɔsa"
    discourseSegments := []
    glossedTokens := [("ɟaci", "Djatchi"), ("ji", "FUT"), ("ɔnɛ", "3SG.POSS"), ("ɡbɔɡɔ", "leg"), ("jɔkʊ-ŋwɔsa", "PART-scrape")]
    translation := "Djatchi will scrape his leg."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "SAuxOPartV"), ("pattern", "S Aux O Part V"), ("verb", "ngwOsa"), ("particleATR", "minus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex13b : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex13b"
    source := ⟨"sande-clem-dabkowski-2026", "(13b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "ɟaci ŋwɔsa ɔnɛ ɡbɔɡɔ jɔkʊ"
    discourseSegments := []
    glossedTokens := [("ɟaci", "Djatchi"), ("ŋwɔsa", "scrape.PFV"), ("ɔnɛ", "3SG.POSS"), ("ɡbɔɡɔ", "leg"), ("jɔkʊ", "PART")]
    translation := "Djatchi scraped his leg."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "SVOPart"), ("pattern", "S V O Part"), ("verb", "ngwOsa"), ("particleATR", "minus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex21a : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex21a"
    source := ⟨"sande-clem-dabkowski-2026", "(21a)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "jɔkʊ ɔ ni=ɔ"
    discourseSegments := []
    glossedTokens := [("jɔkʊ", "PART"), ("ɔ", "3SG.NOM"), ("ni=ɔ", "see.PFV=3SG.ACC")]
    translation := "He SAW him."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "PartSVO"), ("pattern", "Part S V O"), ("verb", "ni"), ("particleATR", "minus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex21b : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex21b"
    source := ⟨"sande-clem-dabkowski-2026", "(21b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "joku-ni ɔ ni=ɔ"
    discourseSegments := []
    glossedTokens := [("joku-ni", "PART-see"), ("ɔ", "3SG.NOM"), ("ni=ɔ", "see.PFV=3SG.ACC")]
    translation := "He SAW him."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "Part V S V O")]
    comment := "Also unacceptable with a clause-final copy of the particle."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex21c : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex21c"
    source := ⟨"sande-clem-dabkowski-2026", "(21c)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "ni ɔ ni=ɔ jɔkʊ"
    discourseSegments := []
    glossedTokens := [("ni", "see"), ("ɔ", "3SG.NOM"), ("ni=ɔ", "see.PFV=3SG.ACC"), ("jɔkʊ", "PART")]
    translation := "He SAW him."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "V S V O Part")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex21d : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex21d"
    source := ⟨"sande-clem-dabkowski-2026", "(21d)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "ni ɔ =ɔ jɔkʊ"
    discourseSegments := []
    glossedTokens := [("ni", "see"), ("ɔ", "3SG.NOM"), ("=ɔ", "3SG.ACC"), ("jɔkʊ", "PART")]
    translation := "He SAW him."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "V S O Part")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex21e : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex21e"
    source := ⟨"sande-clem-dabkowski-2026", "(21e)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "joku ɔ ni=ɔ jɔkʊ"
    discourseSegments := []
    glossedTokens := [("joku", "PART"), ("ɔ", "3SG.NOM"), ("ni=ɔ", "see.PFV=3SG.ACC"), ("jɔkʊ", "PART")]
    translation := "He SAW him."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("pattern", "Part S V O Part")]
    comment := "Unacceptable with either value of the fronted particle's vowels."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex22 : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex22"
    source := ⟨"sande-clem-dabkowski-2026", "(22)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "joku ɔ ji ɟaci ni"
    discourseSegments := []
    glossedTokens := [("joku", "PART"), ("ɔ", "3SG.NOM"), ("ji", "FUT"), ("ɟaci", "Djatchi"), ("ni", "see")]
    translation := "He will SEE Djatchi."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("order", "PartSAuxOV"), ("pattern", "Part S Aux O V"), ("verb", "ni"), ("particleATR", "plus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex24b : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex24b"
    source := ⟨"sande-clem-dabkowski-2026", "(24b)"⟩
    reportedIn := none
    language := "gabo1234"
    primaryText := "joku ɔ ji ɟaci ni"
    discourseSegments := []
    glossedTokens := [("joku", "PART"), ("ɔ", "3SG.NOM"), ("ji", "FUT"), ("ɟaci", "Djatchi"), ("ni", "see")]
    translation := "He will SEE Djatchi."
    context := ""
    judgment := .acceptable
    alternatives := [("jɔkʊ ɔ ji ɟaci ni", .ungrammatical)]
    readings := []
    paperFeatures := [("order", "PartSAuxOV"), ("pattern", "Part S Aux O V"), ("verb", "ni"), ("particleATR", "plus")]
    comment := "The fronted particle harmonizes with the clause-final verb across the subject, auxiliary and object."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex49a : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex49a"
    source := ⟨"sande-clem-dabkowski-2026", "(49a)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "fas w-ale"
    discourseSegments := []
    glossedTokens := [("fas", "horse"), ("w-ale", "CL-DEM.DIST")]
    translation := "that horse"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "localDP"), ("headATR", "minus"), ("demATR", "minus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex49b : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex49b"
    source := ⟨"sande-clem-dabkowski-2026", "(49b)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "béy w-ëlé"
    discourseSegments := []
    glossedTokens := [("béy", "goat"), ("w-ëlé", "CL-DEM.DIST")]
    translation := "that goat"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "localDP"), ("headATR", "plus"), ("demATR", "plus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex50a : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex50a"
    source := ⟨"sande-clem-dabkowski-2026", "(50a)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "xaj b-u weex b-ale"
    discourseSegments := []
    glossedTokens := [("xaj", "dog"), ("b-u", "CL-REL"), ("weex", "be.white"), ("b-ale", "CL-DEM.DIST")]
    translation := "that white dog"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "relClause"), ("headATR", "minus"), ("stativeATR", "minus"), ("demATR", "minus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex50b : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex50b"
    source := ⟨"sande-clem-dabkowski-2026", "(50b)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "béy w-u réy w-ëlé"
    discourseSegments := []
    glossedTokens := [("béy", "goat"), ("w-u", "CL-REL"), ("réy", "be.big"), ("w-ëlé", "CL-DEM.DIST")]
    translation := "that big goat"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "relClause"), ("headATR", "plus"), ("stativeATR", "plus"), ("demATR", "plus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex50c : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex50c"
    source := ⟨"sande-clem-dabkowski-2026", "(50c)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "xaj b-u réy b-ale"
    discourseSegments := []
    glossedTokens := [("xaj", "dog"), ("b-u", "CL-REL"), ("réy", "be.big"), ("b-ale", "CL-DEM.DIST")]
    translation := "that big dog"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "relClause"), ("headATR", "minus"), ("stativeATR", "plus"), ("demATR", "minus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex50d : LinguisticExample :=
  { id := "sandeclemdabkowski2026_ex50d"
    source := ⟨"sande-clem-dabkowski-2026", "(50d)"⟩
    reportedIn := none
    language := "nucl1347"
    primaryText := "béy w-u weex w-ëlé"
    discourseSegments := []
    glossedTokens := [("béy", "goat"), ("w-u", "CL-REL"), ("weex", "be.white"), ("w-ëlé", "CL-DEM.DIST")]
    translation := "that white goat"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("shape", "relClause"), ("headATR", "plus"), ("stativeATR", "minus"), ("demATR", "plus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex11a, ex11b, ex11c, ex12b, ex13b, ex21a, ex21b, ex21c, ex21d, ex21e, ex22, ex24b, ex49a, ex49b, ex50a, ex50b, ex50c, ex50d]

end SandeClemDabkowski2026.Examples
