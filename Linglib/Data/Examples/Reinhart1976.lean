import Linglib.Data.Examples.Schema

/-!
# `Reinhart1976` — typed example data

Auto-generated from `Linglib/Data/Examples/Reinhart1976.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Reinhart1976.Examples`.
-/

namespace Reinhart1976.Examples

open Data.Examples

def ex_11a : LinguisticExample :=
  { id := "reinhart1976_11a"
    source := ⟨"reinhart-1976", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Rosa denied that Rosa has met the Shah."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "denied"), ("np1", "0"), ("np2", "110"), ("pronouns", "none")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11b : LinguisticExample :=
  { id := "reinhart1976_11b"
    source := ⟨"reinhart-1976", "(11b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She denied that Rosa has met the Shah."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "denied"), ("np1", "0"), ("np2", "110"), ("pronouns", "np1")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11c : LinguisticExample :=
  { id := "reinhart1976_11c"
    source := ⟨"reinhart-1976", "(11c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Rosa denied that she has met the Shah."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "denied"), ("np1", "0"), ("np2", "110"), ("pronouns", "np2")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11d : LinguisticExample :=
  { id := "reinhart1976_11d"
    source := ⟨"reinhart-1976", "(11d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She denied that she has met the Shah."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "denied"), ("np1", "0"), ("np2", "110"), ("pronouns", "both")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def IIa : LinguisticExample :=
  { id := "reinhart1976_IIa"
    source := ⟨"reinhart-1976", "(IIa)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The man who traveled with Rosa denied that she met the Shah."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "relative"), ("np1", "02111"), ("np2", "110"), ("pronouns", "np2")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def IIb : LinguisticExample :=
  { id := "reinhart1976_IIb"
    source := ⟨"reinhart-1976", "(IIb)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The man who traveled with her denied that Rosa met the Shah."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "relative"), ("np1", "02111"), ("np2", "110"), ("pronouns", "np1")]
    comment := "repeated as (3)"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12a : LinguisticExample :=
  { id := "reinhart1976_12a"
    source := ⟨"reinhart-1976", "(12a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People who know Nixon hate him."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "relativeObject"), ("np1", "0111"), ("np2", "11"), ("pronouns", "np2")]
    comment := "from Lasnik (1976)"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12b : LinguisticExample :=
  { id := "reinhart1976_12b"
    source := ⟨"reinhart-1976", "(12b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People who know him hate Nixon."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "relativeObject"), ("np1", "0111"), ("np2", "11"), ("pronouns", "np1")]
    comment := "from Lasnik (1976)"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12c : LinguisticExample :=
  { id := "reinhart1976_12c"
    source := ⟨"reinhart-1976", "(12c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "People who know Nixon hate Nixon."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "relativeObject"), ("np1", "0111"), ("np2", "11"), ("pronouns", "none")]
    comment := "from Lasnik (1976); marginal for some speakers, but not blocked, unlike (11a)"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_43a : LinguisticExample :=
  { id := "reinhart1976_43a"
    source := ⟨"reinhart-1976", "(43a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Near Dan, he saw a snake."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "preposedPP"), ("np1", "01"), ("np2", "1"), ("pronouns", "np2")]
    comment := "repeated from (20a)"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_43b : LinguisticExample :=
  { id := "reinhart1976_43b"
    source := ⟨"reinhart-1976", "(43b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Near Dan, Dan saw a snake."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "preposedPP"), ("np1", "01"), ("np2", "1"), ("pronouns", "none")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_45 : LinguisticExample :=
  { id := "reinhart1976_45"
    source := ⟨"reinhart-1976", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Near him, Dan saw a snake."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "preposedPP"), ("np1", "01"), ("np2", "1"), ("pronouns", "np1")]
    comment := "repeated from (18a)"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_47 : LinguisticExample :=
  { id := "reinhart1976_47"
    source := ⟨"reinhart-1976", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In Dan's apartment, Rosa showed him her new tricks."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "preposedPP"), ("np1", "010"), ("np2", "21"), ("pronouns", "np2")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_44a : LinguisticExample :=
  { id := "reinhart1976_44a"
    source := ⟨"reinhart-1976", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He was fired since McIntosh's weird habits had finally reached an intolerable stage."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "sententialPP"), ("np1", "0"), ("np2", "2100"), ("pronouns", "np1")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_44b : LinguisticExample :=
  { id := "reinhart1976_44b"
    source := ⟨"reinhart-1976", "(44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "McIntosh was fired since McIntosh's weird habits had finally reached an intolerable stage."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "sententialPP"), ("np1", "0"), ("np2", "2100"), ("pronouns", "none")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_46 : LinguisticExample :=
  { id := "reinhart1976_46"
    source := ⟨"reinhart-1976", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We had to fire him since McIntosh's weird habits had reached an intolerable stage."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "sententialPP"), ("np1", "11"), ("np2", "2100"), ("pronouns", "np1")]
    comment := "repeated from (19b)"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_48a : LinguisticExample :=
  { id := "reinhart1976_48a"
    source := ⟨"reinhart-1976", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I'm willing to give him 2 grand for Ben's car."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "verbalPP"), ("np1", "111"), ("np2", "11310"), ("pronouns", "np1")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_51a : LinguisticExample :=
  { id := "reinhart1976_51a"
    source := ⟨"reinhart-1976", "(51a)"⟩
    reportedIn := none
    language := "plat1254"
    primaryText := "namono azy ny anadahin-dRakoto"
    discourseSegments := []
    glossedTokens := []
    translation := "Rakoto's sister killed him."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "vos"), ("np1", "01"), ("np2", "11"), ("pronouns", "np1")]
    comment := "from Ed Keenan, personal communication"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_51b : LinguisticExample :=
  { id := "reinhart1976_51b"
    source := ⟨"reinhart-1976", "(51b)"⟩
    reportedIn := none
    language := "plat1254"
    primaryText := "namono ny anadahin-dRakoto izy"
    discourseSegments := []
    glossedTokens := []
    translation := "he killed Rakoto's sister."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("structure", "vos"), ("np1", "011"), ("np2", "1"), ("pronouns", "np2")]
    comment := "from Ed Keenan, personal communication"
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_11a, ex_11b, ex_11c, ex_11d, IIa, IIb, ex_12a, ex_12b, ex_12c, ex_43a, ex_43b, ex_45, ex_47, ex_44a, ex_44b, ex_46, ex_48a, ex_51a, ex_51b]

end Reinhart1976.Examples
