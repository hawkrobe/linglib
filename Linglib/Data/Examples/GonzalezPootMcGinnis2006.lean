import Linglib.Data.Examples.Schema

/-!
# `GonzalezPootMcGinnis2006` — typed example data

Auto-generated from `Linglib/Data/Examples/GonzalezPootMcGinnis2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GonzalezPootMcGinnis2006.Examples`.
-/

namespace GonzalezPootMcGinnis2006.Examples

open Data.Examples

def gpm2006_19 : LinguisticExample :=
  { id := "gpm2006_19"
    source := ⟨"gonzalez-poot-mcginnis-2006", "(19)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "k -a w- áːnt -ik -oʔon -éːʃ"
    discourseSegments := []
    glossedTokens := [("k", "IMPERF"), ("-a", "2ERG"), ("w-", "PSE.ERG"), ("áːnt", "help"), ("-ik", "INCOMPL"), ("-oʔon", "1NOMpl"), ("-éːʃ", "2ERGpl")]
    translation := "You (pl) help us."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "transitive"), ("subjPerson", "2"), ("subjNumber", "pl"), ("objPerson", "1"), ("objNumber", "pl"), ("aux", "a"), ("prefix", "w"), ("suffix1", "oʔon"), ("suffix2", "éːʃ")]
    comment := "Object-before-subject order, as the template (18) predicts."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gpm2006_20 : LinguisticExample :=
  { id := "gpm2006_20"
    source := ⟨"gonzalez-poot-mcginnis-2006", "(20)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "k -u j- áːnt -ik -éːʃ -oʔob"
    discourseSegments := []
    glossedTokens := [("k", "IMPERF"), ("-u", "3ERG"), ("j-", "3ERG"), ("áːnt", "help"), ("-ik", "INCOMPL"), ("-éːʃ", "2NOMpl"), ("-oʔob", "3ERGpl")]
    translation := "They help you (pl)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "transitive"), ("subjPerson", "3"), ("subjNumber", "pl"), ("objPerson", "2"), ("objNumber", "pl"), ("aux", "u"), ("prefix", "j"), ("suffix1", "éːʃ"), ("suffix2", "oʔob")]
    comment := "Also (2) and (28a)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gpm2006_21 : LinguisticExample :=
  { id := "gpm2006_21"
    source := ⟨"gonzalez-poot-mcginnis-2006", "(21)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "k -a w- áːnt -ik -oʔob -éːʃ"
    discourseSegments := []
    glossedTokens := [("k", "IMPERF"), ("-a", "2ERG"), ("w-", "PSE.ERG"), ("áːnt", "help"), ("-ik", "INCOMPL"), ("-oʔob", "3NOMpl"), ("-éːʃ", "2ERGpl")]
    translation := "You (pl) help them."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "transitive"), ("subjPerson", "2"), ("subjNumber", "pl"), ("objPerson", "3"), ("objNumber", "pl"), ("aux", "a"), ("prefix", "w"), ("suffix1", "oʔob"), ("suffix2", "éːʃ")]
    comment := "The object–subject order the template (18) imposes is ungrammatical here."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gpm2006_22 : LinguisticExample :=
  { id := "gpm2006_22"
    source := ⟨"gonzalez-poot-mcginnis-2006", "(22)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "k -a w- áːnt -ik -éːʃ -oʔob"
    discourseSegments := []
    glossedTokens := [("k", "IMPERF"), ("-a", "2ERG"), ("w-", "PSE.ERG"), ("áːnt", "help"), ("-ik", "INCOMPL"), ("-éːʃ", "2ERGpl"), ("-oʔob", "3NOMpl")]
    translation := "You (pl) help them."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "transitive"), ("subjPerson", "2"), ("subjNumber", "pl"), ("objPerson", "3"), ("objNumber", "pl"), ("aux", "a"), ("prefix", "w"), ("suffix1", "éːʃ"), ("suffix2", "oʔob")]
    comment := "Subject agreement precedes object agreement; also (29a)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gpm2006_23 : LinguisticExample :=
  { id := "gpm2006_23"
    source := ⟨"gonzalez-poot-mcginnis-2006", "(23)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "k -u j- áːnt -ik -oʔob -oʔob"
    discourseSegments := []
    glossedTokens := [("k", "IMPERF"), ("-u", "3ERG"), ("j-", "3ERG"), ("áːnt", "help"), ("-ik", "INCOMPL"), ("-oʔob", "3NOMpl"), ("-oʔob", "3ERGpl")]
    translation := "They help them."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "transitive"), ("subjPerson", "3"), ("subjNumber", "pl"), ("objPerson", "3"), ("objNumber", "pl"), ("aux", "u"), ("prefix", "j"), ("suffix1", "oʔob"), ("suffix2", "oʔob")]
    comment := "Overt agreement for both arguments is impossible."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gpm2006_24 : LinguisticExample :=
  { id := "gpm2006_24"
    source := ⟨"gonzalez-poot-mcginnis-2006", "(24)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "k -u j- áːnt -ik -oʔob -Ø"
    discourseSegments := []
    glossedTokens := [("k", "IMPERF"), ("-u", "3ERG"), ("j-", "3ERG"), ("áːnt", "help"), ("-ik", "INCOMPL"), ("-oʔob", "3NOMpl"), ("-Ø", "3ERGpl")]
    translation := "They help them."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "transitive"), ("subjPerson", "3"), ("subjNumber", "pl"), ("objPerson", "3"), ("objNumber", "pl"), ("aux", "u"), ("prefix", "j"), ("suffix1", "oʔob"), ("suffix2", "")]
    comment := "One overt suffix; also (1) and (30a)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gpm2006_16ex : LinguisticExample :=
  { id := "gpm2006_16ex"
    source := ⟨"gonzalez-poot-mcginnis-2006", "(16)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "k -u j- áːnt -ik -en"
    discourseSegments := []
    glossedTokens := [("k", "IMPERF"), ("-u", "3ERG"), ("j-", "3ERG"), ("áːnt", "help"), ("-ik", "INCOMPL"), ("-en", "1NOMsg")]
    translation := "S/he helps me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "transitive"), ("subjPerson", "3"), ("subjNumber", "sg"), ("objPerson", "1"), ("objNumber", "sg"), ("aux", "u"), ("prefix", "j"), ("suffix1", "en"), ("suffix2", "")]
    comment := "The example under the nominative marker table (16)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gpm2006_3 : LinguisticExample :=
  { id := "gpm2006_3"
    source := ⟨"gonzalez-poot-mcginnis-2006", "(3)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "k -in w- ok -ol"
    discourseSegments := []
    glossedTokens := [("k", "IMPERF"), ("-in", "1ERGsg"), ("w-", "PSE.ERG"), ("ok", "enter"), ("-ol", "INCOMPL")]
    translation := "I enter."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "intransitive"), ("subjPerson", "1"), ("subjNumber", "sg"), ("aux", "in"), ("prefix", "w"), ("suffix1", ""), ("suffix2", "")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gpm2006_4 : LinguisticExample :=
  { id := "gpm2006_4"
    source := ⟨"gonzalez-poot-mcginnis-2006", "(4)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "k -k ok -ol"
    discourseSegments := []
    glossedTokens := [("k", "IMPERF"), ("-k", "1ERGpl"), ("ok", "enter"), ("-ol", "INCOMPL")]
    translation := "We enter."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "intransitive"), ("subjPerson", "1"), ("subjNumber", "pl"), ("aux", "k"), ("prefix", ""), ("suffix1", ""), ("suffix2", "")]
    comment := "First-person plural: person and number both on the auxiliary, no prefix, no verbal suffix."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gpm2006_5 : LinguisticExample :=
  { id := "gpm2006_5"
    source := ⟨"gonzalez-poot-mcginnis-2006", "(5)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "k -a w- ok -ol"
    discourseSegments := []
    glossedTokens := [("k", "IMPERF"), ("-a", "2ERG"), ("w-", "PSE.ERG"), ("ok", "enter"), ("-ol", "INCOMPL")]
    translation := "You (sg) enter."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "intransitive"), ("subjPerson", "2"), ("subjNumber", "sg"), ("aux", "a"), ("prefix", "w"), ("suffix1", ""), ("suffix2", "")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gpm2006_6 : LinguisticExample :=
  { id := "gpm2006_6"
    source := ⟨"gonzalez-poot-mcginnis-2006", "(6)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "k -a w- ok -ol -éːʃ"
    discourseSegments := []
    glossedTokens := [("k", "IMPERF"), ("-a", "2ERG"), ("w-", "PSE.ERG"), ("ok", "enter"), ("-ol", "INCOMPL"), ("-éːʃ", "2ERGpl")]
    translation := "You (pl) enter."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "intransitive"), ("subjPerson", "2"), ("subjNumber", "pl"), ("aux", "a"), ("prefix", "w"), ("suffix1", "éːʃ"), ("suffix2", "")]
    comment := "Second person: person on the auxiliary, number on the verb."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gpm2006_7 : LinguisticExample :=
  { id := "gpm2006_7"
    source := ⟨"gonzalez-poot-mcginnis-2006", "(7)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "k -u y- ok -ol"
    discourseSegments := []
    glossedTokens := [("k", "IMPERF"), ("-u", "3ERG"), ("y-", "3ERG"), ("ok", "enter"), ("-ol", "INCOMPL")]
    translation := "He/she enters."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "intransitive"), ("subjPerson", "3"), ("subjNumber", "sg"), ("aux", "u"), ("prefix", "j"), ("suffix1", ""), ("suffix2", "")]
    comment := "The prefix surfaces as y- before a vowel; the item is j-."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gpm2006_8 : LinguisticExample :=
  { id := "gpm2006_8"
    source := ⟨"gonzalez-poot-mcginnis-2006", "(8)"⟩
    reportedIn := none
    language := "yuca1254"
    primaryText := "k -u y- ok -ol -oʔob"
    discourseSegments := []
    glossedTokens := [("k", "IMPERF"), ("-u", "3ERG"), ("y-", "3ERG"), ("ok", "enter"), ("-ol", "INCOMPL"), ("-oʔob", "3ERGpl")]
    translation := "They enter."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "intransitive"), ("subjPerson", "3"), ("subjNumber", "pl"), ("aux", "u"), ("prefix", "j"), ("suffix1", "oʔob"), ("suffix2", "")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [gpm2006_19, gpm2006_20, gpm2006_21, gpm2006_22, gpm2006_23, gpm2006_24, gpm2006_16ex, gpm2006_3, gpm2006_4, gpm2006_5, gpm2006_6, gpm2006_7, gpm2006_8]

end GonzalezPootMcGinnis2006.Examples
