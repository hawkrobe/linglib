module

public import Linglib.Data.Examples.Schema

/-!
# `HahnDegenFutrell2021` — typed example data

Auto-generated from `Linglib/Data/Examples/HahnDegenFutrell2021.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace HahnDegenFutrell2021.Examples`.
-/

@[expose] public section

namespace HahnDegenFutrell2021.Examples

open Data.Examples

def ex2a : LinguisticExample :=
  { id := "hahndegenfutrell2021_ex2a"
    source := ⟨"hahn-degen-futrell-2021", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucy ate the broccoli with a fork."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "heavyNPShift")]
    comment := "NP objects ordinarily precede PPs; the paper takes the example from Staub et al. (2006)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2b : LinguisticExample :=
  { id := "hahndegenfutrell2021_ex2b"
    source := ⟨"hahn-degen-futrell-2021", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucy ate with a fork the broccoli."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "heavyNPShift")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2c : LinguisticExample :=
  { id := "hahndegenfutrell2021_ex2c"
    source := ⟨"hahn-degen-futrell-2021", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucy ate the extremely delicious, bright green broccoli with a fork."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "heavyNPShift")]
    comment := "Less preferred with a long NP: the verb and the PP are far apart."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2d : LinguisticExample :=
  { id := "hahndegenfutrell2021_ex2d"
    source := ⟨"hahn-degen-futrell-2021", "(2d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Lucy ate with a fork the extremely delicious, bright green broccoli."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "heavyNPShift")]
    comment := "Heavy NP shift: shortens the verb-to-PP dependency while only modestly lengthening the verb-to-object one."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def si1 : LinguisticExample :=
  { id := "hahndegenfutrell2021_si1"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 1"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mi-naka-tta"
    discourseSegments := []
    glossedTokens := [("mi", "see"), ("naka", "NEG"), ("tta", "PST")]
    translation := "did not see"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's table of relative orderings of the Japanese verb suffixes, segmented as there; the supplement takes the form from Vaccari and Vaccari's grammar (1938)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def si2 : LinguisticExample :=
  { id := "hahndegenfutrell2021_si2"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 2"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mi-taku-nai"
    discourseSegments := []
    glossedTokens := [("mi", "see"), ("taku", "DESID"), ("nai", "NEG")]
    translation := "I do not wish to see"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's table of relative orderings of the Japanese verb suffixes, segmented as there; the supplement takes the form from Vaccari and Vaccari's grammar (1938)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def si3 : LinguisticExample :=
  { id := "hahndegenfutrell2021_si3"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mi-taku-naka-tta"
    discourseSegments := []
    glossedTokens := [("mi", "see"), ("taku", "DESID"), ("naka", "NEG"), ("tta", "PST")]
    translation := "I did not wish to see"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's table of relative orderings of the Japanese verb suffixes, segmented as there; the supplement takes the form from Vaccari and Vaccari's grammar (1938)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def si4 : LinguisticExample :=
  { id := "hahndegenfutrell2021_si4"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 4"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "tat-ase-rare-ta"
    discourseSegments := []
    glossedTokens := [("tat", "stand"), ("ase", "CAUS"), ("rare", "PASS"), ("ta", "PST")]
    translation := "was made to stand up"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's table of relative orderings of the Japanese verb suffixes, segmented as there; the supplement takes the form from Kaiser et al. (2013)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def si5 : LinguisticExample :=
  { id := "hahndegenfutrell2021_si5"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 5"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "waraw-are-ta"
    discourseSegments := []
    glossedTokens := [("waraw", "laugh"), ("are", "PASS"), ("ta", "PST")]
    translation := "was laughed at"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's table of relative orderings of the Japanese verb suffixes, segmented as there; the supplement takes the form from Kaiser et al. (2013)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def si6 : LinguisticExample :=
  { id := "hahndegenfutrell2021_si6"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 6"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mi-rare-mase-n"
    discourseSegments := []
    glossedTokens := [("mi", "see"), ("rare", "PASS"), ("mase", "POL"), ("n", "NEG")]
    translation := "is not seen"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's table of relative orderings of the Japanese verb suffixes, segmented as there; the supplement takes the form from Vaccari and Vaccari's grammar (1938)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def si7 : LinguisticExample :=
  { id := "hahndegenfutrell2021_si7"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 7"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mi-rare-mash-yoo"
    discourseSegments := []
    glossedTokens := [("mi", "see"), ("rare", "PASS"), ("mash", "POL"), ("yoo", "HORT")]
    translation := "will be seen"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's table of relative orderings of the Japanese verb suffixes, segmented as there; the supplement takes the form from Vaccari and Vaccari's grammar (1938)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def si8 : LinguisticExample :=
  { id := "hahndegenfutrell2021_si8"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "de-naka-roo"
    discourseSegments := []
    glossedTokens := [("de", "go.out"), ("naka", "NEG"), ("roo", "HORT")]
    translation := "will not go out"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's table of relative orderings of the Japanese verb suffixes, segmented as there; the supplement takes the form from Vaccari and Vaccari's grammar (1938)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def si9 : LinguisticExample :=
  { id := "hahndegenfutrell2021_si9"
    source := ⟨"hahn-degen-futrell-2021", "SI, Japanese, ordering table row 9"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "mi-e-mase-n"
    discourseSegments := []
    glossedTokens := [("mi", "see"), ("e", "POT"), ("mase", "POL"), ("n", "NEG")]
    translation := "cannot see"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Japanese"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's table of relative orderings of the Japanese verb suffixes, segmented as there; the supplement takes the form from Vaccari and Vaccari's grammar (1938)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def so1 : LinguisticExample :=
  { id := "hahndegenfutrell2021_so1"
    source := ⟨"hahn-degen-futrell-2021", "(2a)"⟩
    reportedIn := none
    language := "sout2807"
    primaryText := "oa-di-rek-a"
    discourseSegments := []
    glossedTokens := [("oa", "SM"), ("di", "OM"), ("rek", "buy"), ("a", "IND")]
    translation := "(he) is buying (it)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("phenomenon", "morphemeOrder")]
    comment := "The paper takes the form from Demuth (1992)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def so2 : LinguisticExample :=
  { id := "hahndegenfutrell2021_so2"
    source := ⟨"hahn-degen-futrell-2021", "(2b)"⟩
    reportedIn := none
    language := "sout2807"
    primaryText := "o-pheh-el-a"
    discourseSegments := []
    glossedTokens := [("o", "SM"), ("pheh", "cook"), ("el", "APPL"), ("a", "IND")]
    translation := "(he) cooks (food) for (him)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("phenomenon", "morphemeOrder")]
    comment := "The paper takes the form from Demuth (1992)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def so3 : LinguisticExample :=
  { id := "hahndegenfutrell2021_so3"
    source := ⟨"hahn-degen-futrell-2021", "SI, Sesotho, examples table row 1"⟩
    reportedIn := none
    language := "sout2807"
    primaryText := "o-pheh-il-e"
    discourseSegments := []
    glossedTokens := [("o", "SM"), ("pheh", "cook"), ("il", "PRF"), ("e", "IND")]
    translation := "(Thabo) cooked (food)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Sesotho"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's table of Sesotho examples, segmented as there; the supplement takes the form from Demuth (1992)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def so4 : LinguisticExample :=
  { id := "hahndegenfutrell2021_so4"
    source := ⟨"hahn-degen-futrell-2021", "SI, Sesotho, examples table row 2"⟩
    reportedIn := none
    language := "sout2807"
    primaryText := "ke-e-f-uw-e"
    discourseSegments := []
    glossedTokens := [("ke", "SM"), ("e", "OM"), ("f", "give"), ("uw", "PASS"), ("e", "IND")]
    translation := "(I) was given (the book)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Sesotho"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's table of Sesotho examples, segmented as there; the supplement takes the form from Demuth (1992)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def so5 : LinguisticExample :=
  { id := "hahndegenfutrell2021_so5"
    source := ⟨"hahn-degen-futrell-2021", "SI, Sesotho, examples table row 4"⟩
    reportedIn := none
    language := "sout2807"
    primaryText := "o-pheh-el-w-a"
    discourseSegments := []
    glossedTokens := [("o", "SM"), ("pheh", "cook"), ("el", "APPL"), ("w", "PASS"), ("a", "IND")]
    translation := "(Mpho) is being cooked (food)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Sesotho"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's table of Sesotho examples, segmented as there; the supplement takes the form from Demuth (1992)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def so6 : LinguisticExample :=
  { id := "hahndegenfutrell2021_so6"
    source := ⟨"hahn-degen-futrell-2021", "SI, Sesotho, completive footnote"⟩
    reportedIn := none
    language := "sout2807"
    primaryText := "u-neh-el-ets-w-a-ng"
    discourseSegments := []
    glossedTokens := [("u", "OM"), ("neh", "give"), ("el", "APPL"), ("ets", "CL"), ("w", "PASS"), ("a", "IND"), ("ng", "WH")]
    translation := "What is it that you want passed to you?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Sesotho"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's example from the Demuth corpus for the completive before the passive; it glosses u- as a present-tense marker fused with the second-singular object marker."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def so7 : LinguisticExample :=
  { id := "hahndegenfutrell2021_so7"
    source := ⟨"hahn-degen-futrell-2021", "SI, Sesotho, stacking footnote"⟩
    reportedIn := none
    language := "sout2807"
    primaryText := "ba-arol-el-an-a"
    discourseSegments := []
    glossedTokens := [("ba", "SM"), ("arol", "divide"), ("el", "APPL"), ("an", "RC"), ("a", "IND")]
    translation := "Do they share?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "SI Sesotho"), ("phenomenon", "morphemeOrder")]
    comment := "The supplement's example from the Demuth corpus for a reciprocal after an applicative; it glosses ba- as the class 2 subject marker with a fused present-tense marker."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [ex2a, ex2b, ex2c, ex2d, si1, si2, si3, si4, si5, si6, si7, si8, si9, so1, so2, so3, so4, so5, so6, so7]

end HahnDegenFutrell2021.Examples
