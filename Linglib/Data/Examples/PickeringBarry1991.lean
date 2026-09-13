import Linglib.Data.Examples.Schema

/-!
# `PickeringBarry1991` — typed example data

Auto-generated from `Linglib/Data/Examples/PickeringBarry1991.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace PickeringBarry1991.Examples`.
-/

namespace PickeringBarry1991.Examples

open Data.Examples

def ex15 : LinguisticExample :=
  { id := "pickeringbarry1991_ex15"
    source := ⟨"pickering-barry-1991", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In which box did you put the very large and beautifully decorated wedding cake bought from the expensive bakery?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "piedPiping"), ("section", "Processing without gaps")]
    comment := "The filler associates with put as soon as the verb is read."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex16 : LinguisticExample :=
  { id := "pickeringbarry1991_ex16"
    source := ⟨"pickering-barry-1991", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which box did you put the very large and beautifully decorated wedding cake bought from the expensive bakery in?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("construction", "prepositionStranding"), ("section", "Processing without gaps")]
    comment := "Rather awkward: the filler associates with the stranded preposition at the end."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex42 : LinguisticExample :=
  { id := "pickeringbarry1991_ex42"
    source := ⟨"pickering-barry-1991", "(42)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John found the saucer on which Mary put the cup into which I poured the tea."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "multiplePiedPiping"), ("section", "Processing recursive constructions")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex44 : LinguisticExample :=
  { id := "pickeringbarry1991_ex44"
    source := ⟨"pickering-barry-1991", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw the farmer who owned the dog which chased the cat."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "multipleSubjectRelative"), ("section", "Processing recursive constructions")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex45 : LinguisticExample :=
  { id := "pickeringbarry1991_ex45"
    source := ⟨"pickering-barry-1991", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The cat which the dog which the farmer owned chased fled."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "multipleObjectRelative"), ("section", "Processing recursive constructions")]
    comment := "Grammatical but very hard to process."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48 : LinguisticExample :=
  { id := "pickeringbarry1991_ex48"
    source := ⟨"pickering-barry-1991", "(48)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Bauer der das Mädchen das den Jungen küßte schlug ging."
    discourseSegments := []
    glossedTokens := [("Der", "the.NOM"), ("Bauer", "farmer"), ("der", "who.NOM"), ("das", "the.ACC"), ("Mädchen", "girl"), ("das", "who.NOM"), ("den", "the.ACC"), ("Jungen", "boy"), ("küßte", "kissed"), ("schlug", "hit"), ("ging", "went")]
    translation := "The farmer who hit the girl who kissed the boy went."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "multipleSubjectRelative"), ("section", "Processing recursive constructions")]
    comment := "German speakers find it difficult in the same way English speakers find (45) difficult."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex51 : LinguisticExample :=
  { id := "pickeringbarry1991_ex51"
    source := ⟨"pickering-barry-1991", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw the farmer who owned the dog which chased the cat which scratched the girl."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "multipleSubjectRelative"), ("section", "Processing recursive constructions")]
    comment := "A further relative clause adds no processing complexity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex52 : LinguisticExample :=
  { id := "pickeringbarry1991_ex52"
    source := ⟨"pickering-barry-1991", "(52)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The girl who the cat which the dog which the farmer owned chased scratched fled."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "multipleObjectRelative"), ("section", "Processing recursive constructions")]
    comment := "Extreme processing difficulty."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex53 : LinguisticExample :=
  { id := "pickeringbarry1991_ex53"
    source := ⟨"pickering-barry-1991", "(53)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Der Bauer der das Mädchen das den Jungen der die Katze streichelte küßte schlug ging."
    discourseSegments := []
    glossedTokens := [("Der", "the.NOM"), ("Bauer", "farmer"), ("der", "who.NOM"), ("das", "the.ACC"), ("Mädchen", "girl"), ("das", "who.NOM"), ("den", "the.ACC"), ("Jungen", "boy"), ("der", "who.NOM"), ("die", "the.ACC"), ("Katze", "cat"), ("streichelte", "stroked"), ("küßte", "kissed"), ("schlug", "hit"), ("ging", "went")]
    translation := "The farmer who hit the girl who kissed the boy who stroked the cat went."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "multipleSubjectRelative"), ("section", "Processing recursive constructions")]
    comment := "Virtually incomprehensible."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex54 : LinguisticExample :=
  { id := "pickeringbarry1991_ex54"
    source := ⟨"pickering-barry-1991", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue found the tray upon which John placed the saucer on which Mary put the cup into which I poured the tea."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "multiplePiedPiping"), ("section", "Processing recursive constructions")]
    comment := "Processed like (51), not like (52)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex55 : LinguisticExample :=
  { id := "pickeringbarry1991_ex55"
    source := ⟨"pickering-barry-1991", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane opened the cupboard in which Bill left the box from which Sue took the tray upon which John placed the saucer on which Mary put the cup into which I poured the tea."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "multiplePiedPiping"), ("section", "Processing recursive constructions")]
    comment := "Five gaps at the end of the sentence under the empty-category analysis, with no increase in processing difficulty."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex60 : LinguisticExample :=
  { id := "pickeringbarry1991_ex60"
    source := ⟨"pickering-barry-1991", "(60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John found the saucer which Mary put the cup which I poured the tea into on."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "multiplePrepositionStranding"), ("section", "Discussion")]
    comment := "Very hard to process: the filler–preposition associations are nested."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex62 : LinguisticExample :=
  { id := "pickeringbarry1991_ex62"
    source := ⟨"pickering-barry-1991", "(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John suggested the punishment which Mary gave the slave who Tom sold the nobleman."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "multipleObjectRelativeDitransitive"), ("section", "Discussion")]
    comment := "Under the reading where Mary gave the slave the punishment and Tom sold the nobleman the slave."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex82a : LinguisticExample :=
  { id := "pickeringbarry1991_ex82a"
    source := ⟨"pickering-barry-1991", "(82a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue wonders who saw Mary."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embeddedQuestion"), ("section", "Unbounded dependencies in categorial grammar")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex82b : LinguisticExample :=
  { id := "pickeringbarry1991_ex82b"
    source := ⟨"pickering-barry-1991", "(82b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue wonders whom John saw."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embeddedQuestion"), ("section", "Unbounded dependencies in categorial grammar")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex82c : LinguisticExample :=
  { id := "pickeringbarry1991_ex82c"
    source := ⟨"pickering-barry-1991", "(82c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue wonders whom John talked to."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embeddedQuestion"), ("section", "Unbounded dependencies in categorial grammar")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex82d : LinguisticExample :=
  { id := "pickeringbarry1991_ex82d"
    source := ⟨"pickering-barry-1991", "(82d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sue wonders who John saw Mary."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "embeddedQuestion"), ("section", "Unbounded dependencies in categorial grammar")]
    comment := "Also with whom."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex93 : LinguisticExample :=
  { id := "pickeringbarry1991_ex93"
    source := ⟨"pickering-barry-1991", "(93)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A bone was given a dog which was given a man."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "recursivePassive"), ("section", "Passives")]
    comment := "Not hard to process, even if further recursions are added."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex15, ex16, ex42, ex44, ex45, ex48, ex51, ex52, ex53, ex54, ex55, ex60, ex62, ex82a, ex82b, ex82c, ex82d, ex93]

end PickeringBarry1991.Examples
