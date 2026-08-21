import Linglib.Data.Examples.Schema

/-!
# `McGinnis2013` — typed example data

Auto-generated from `Linglib/Data/Examples/McGinnis2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace McGinnis2013.Examples`.
-/

namespace McGinnis2013.Examples

open Data.Examples

def ex_17a : LinguisticExample :=
  { id := "mcginnis2013_17a"
    source := ⟨"mcginnis-2013", "(2), (17a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-a-t"
    discourseSegments := []
    glossedTokens := [("g-nax-a-t", "2.dat-see-aor-pl")]
    translation := "He/she saw you (pl)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "2"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "g"), ("suffix1", "a"), ("suffix2", "t")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17b : LinguisticExample :=
  { id := "mcginnis2013_17b"
    source := ⟨"mcginnis-2013", "(3a), (17b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-es"
    discourseSegments := []
    glossedTokens := [("g-nax-es", "2.dat-see-aor.3pl")]
    translation := "They saw you (sg)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "pl"), ("objPerson", "2"), ("objNumber", "sg"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "g"), ("suffix1", "es")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3b : LinguisticExample :=
  { id := "mcginnis2013_3b"
    source := ⟨"mcginnis-2013", "(3b), (17b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-es-t"
    discourseSegments := []
    glossedTokens := [("g-nax-es-t", "2.dat-see-aor.3pl-pl")]
    translation := "They saw you (pl)."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "pl"), ("objPerson", "2"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "g"), ("suffix1", "es"), ("suffix2", "t")]
    comment := "Double plural marking: the subject's Group is discharged by -es, and the object contributes no second Group."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5c : LinguisticExample :=
  { id := "mcginnis2013_5c"
    source := ⟨"mcginnis-2013", "(5c)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-a"
    discourseSegments := []
    glossedTokens := [("g-nax-a", "2.dat-see-aor")]
    translation := "She/he saw you (sg)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "2"), ("objNumber", "sg"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "g"), ("suffix1", "a")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6a : LinguisticExample :=
  { id := "mcginnis2013_6a"
    source := ⟨"mcginnis-2013", "(6a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "v-nax-es"
    discourseSegments := []
    glossedTokens := [("v-nax-es", "1-see-aor.3pl")]
    translation := "I saw them."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "1"), ("subjNumber", "sg"), ("objPerson", "3"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "v"), ("suffix1", "es")]
    comment := "A third-person object is not a clitic and is out of T's reach."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6b_we : LinguisticExample :=
  { id := "mcginnis2013_6b_we"
    source := ⟨"mcginnis-2013", "(6b), (11b), (22b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "v-nax-e-t"
    discourseSegments := []
    glossedTokens := [("v-nax-e-t", "1-see-aor.part-pl")]
    translation := "We saw him/her/it/them."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "1"), ("subjNumber", "pl"), ("objPerson", "3"), ("objNumber", "sg"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "v"), ("suffix1", "e"), ("suffix2", "t")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6b_i : LinguisticExample :=
  { id := "mcginnis2013_6b_i"
    source := ⟨"mcginnis-2013", "(6b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "v-nax-e-t"
    discourseSegments := []
    glossedTokens := [("v-nax-e-t", "1-see-aor.part-pl")]
    translation := "I saw them."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "1"), ("subjNumber", "sg"), ("objPerson", "3"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "v"), ("suffix1", "e"), ("suffix2", "t")]
    comment := "The reading on which -t registers the third-person plural object."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6c : LinguisticExample :=
  { id := "mcginnis2013_6c"
    source := ⟨"mcginnis-2013", "(6c), (22a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "v-nax-e"
    discourseSegments := []
    glossedTokens := [("v-nax-e", "1-see-aor.part")]
    translation := "I saw him/her/it/them."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "1"), ("subjNumber", "sg"), ("objPerson", "3"), ("objNumber", "sg"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "v"), ("suffix1", "e")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18a : LinguisticExample :=
  { id := "mcginnis2013_18a"
    source := ⟨"mcginnis-2013", "(12), (18a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-o-s"
    discourseSegments := []
    glossedTokens := [("g-nax-o-s", "2.dat-see-opt-#")]
    translation := "... that he/she see you (sg)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "2"), ("objNumber", "sg"), ("objCase", "dat"), ("screeve", "optative"), ("prefix", "g"), ("suffix1", "o"), ("suffix2", "s")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18b : LinguisticExample :=
  { id := "mcginnis2013_18b"
    source := ⟨"mcginnis-2013", "(15), (18b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-o-t"
    discourseSegments := []
    glossedTokens := [("g-nax-o-t", "2.dat-see-opt-pl")]
    translation := "... that he/she see you (pl)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "2"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "optative"), ("prefix", "g"), ("suffix1", "o"), ("suffix2", "t")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18b_st : LinguisticExample :=
  { id := "mcginnis2013_18b_st"
    source := ⟨"mcginnis-2013", "(15), (18b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-o-s-t"
    discourseSegments := []
    glossedTokens := [("g-nax-o-s-t", "2.dat-see-opt-#-pl")]
    translation := "... that he/she see you (pl)"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "2"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "optative"), ("prefix", "g"), ("suffix1", "o"), ("suffix2", "s"), ("suffix3", "t")]
    comment := "-t discharges [#], so -s cannot."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18b_ts : LinguisticExample :=
  { id := "mcginnis2013_18b_ts"
    source := ⟨"mcginnis-2013", "(15), (18b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "g-nax-o-t-s"
    discourseSegments := []
    glossedTokens := [("g-nax-o-t-s", "2.dat-see-opt-pl-#")]
    translation := "... that he/she see you (pl)"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "2"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "optative"), ("prefix", "g"), ("suffix1", "o"), ("suffix2", "t"), ("suffix3", "s")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21 : LinguisticExample :=
  { id := "mcginnis2013_21"
    source := ⟨"mcginnis-2013", "(21)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "gv-nax-e-t"
    discourseSegments := []
    glossedTokens := [("gv-nax-e-t", "multisp.dat-see-aor.part-pl")]
    translation := "You (pl) saw us."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "2"), ("subjNumber", "pl"), ("objPerson", "1"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "gv"), ("suffix1", "e"), ("suffix2", "t")]
    comment := "The dative first-person plural bears Multispeaker, its Group impoverished; the plural subject supplies the one Group."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23a : LinguisticExample :=
  { id := "mcginnis2013_23a"
    source := ⟨"mcginnis-2013", "(23a)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "m-nax-a"
    discourseSegments := []
    glossedTokens := [("m-nax-a", "1.dat-see-aor")]
    translation := "He/she saw me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "1"), ("objNumber", "sg"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "m"), ("suffix1", "a")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23b : LinguisticExample :=
  { id := "mcginnis2013_23b"
    source := ⟨"mcginnis-2013", "(23b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "gv-nax-a"
    discourseSegments := []
    glossedTokens := [("gv-nax-a", "multisp.dat-see-aor")]
    translation := "He/she saw us."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "1"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "gv"), ("suffix1", "a")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23b_t : LinguisticExample :=
  { id := "mcginnis2013_23b_t"
    source := ⟨"mcginnis-2013", "(23b)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "gv-nax-a-t"
    discourseSegments := []
    glossedTokens := [("gv-nax-a-t", "multisp.dat-see-aor-pl")]
    translation := "He/she saw us."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "1"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "gv"), ("suffix1", "a"), ("suffix2", "t")]
    comment := "No Group survives Impoverishment on the dative first-person plural."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_26 : LinguisticExample :=
  { id := "mcginnis2013_26"
    source := ⟨"mcginnis-2013", "(26)"⟩
    reportedIn := none
    language := "nucl1302"
    primaryText := "gv-nax-es"
    discourseSegments := []
    glossedTokens := [("gv-nax-es", "multisp.dat-see-aor.3pl")]
    translation := "They saw us."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subjPerson", "3"), ("subjNumber", "pl"), ("objPerson", "1"), ("objNumber", "pl"), ("objCase", "dat"), ("screeve", "aorist"), ("prefix", "gv"), ("suffix1", "es")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_17a, ex_17b, ex_3b, ex_5c, ex_6a, ex_6b_we, ex_6b_i, ex_6c, ex_18a, ex_18b, ex_18b_st, ex_18b_ts, ex_21, ex_23a, ex_23b, ex_23b_t, ex_26]

end McGinnis2013.Examples
