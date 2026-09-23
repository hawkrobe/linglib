module

public import Linglib.Data.Examples.Schema

/-!
# `TurcoBraunDimroth2014` — typed example data

Auto-generated from `Linglib/Data/Examples/TurcoBraunDimroth2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TurcoBraunDimroth2014.Examples`.
-/

@[expose] public section

namespace TurcoBraunDimroth2014.Examples

open Data.Examples

def ex_1A : LinguisticExample :=
  { id := "turcobraundimroth2014_1A"
    source := ⟨"turco-braun-dimroth-2014", "(1) A"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Auf meinem Bild hat das Kind nicht geweint."
    discourseSegments := []
    glossedTokens := []
    translation := "In my picture the child did not cry."
    context := "Polarity contrast: speaker A describes their own picture; B will describe a different picture."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "contrast"), ("polarity", "negative"), ("turn", "A")]
    comment := "The negative claim about A's topic situation; the negation particle is accented."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1B1 : LinguisticExample :=
  { id := "turcobraundimroth2014_1B1"
    source := ⟨"turco-braun-dimroth-2014", "(1) B1"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Auf meinem Bild HAT das Kind geweint."
    discourseSegments := []
    glossedTokens := []
    translation := "In my picture the child DID cry."
    context := "Reply to (1) A about a different picture."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "contrast"), ("polarity", "positive"), ("marking", "verumFocus")]
    comment := "Verum focus: a pitch accent on the finite auxiliary; the claims of A and B1 are compatible, being about different topic situations."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1B2 : LinguisticExample :=
  { id := "turcobraundimroth2014_1B2"
    source := ⟨"turco-braun-dimroth-2014", "(1) B2"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Auf meinem Bild hat das Kind SCHON/WOHL geweint."
    discourseSegments := []
    glossedTokens := []
    translation := "In my picture the child did INDEED cry."
    context := "Reply to (1) A about a different picture."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "contrast"), ("polarity", "positive"), ("marking", "particle")]
    comment := "An accented affirmative particle, schon or wohl, in place of Verum focus; German speakers produced no such particle in the experiment."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2A : LinguisticExample :=
  { id := "turcobraundimroth2014_2A"
    source := ⟨"turco-braun-dimroth-2014", "(2) A"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Kind hat nicht geweint."
    discourseSegments := []
    glossedTokens := []
    translation := "The child did not cry."
    context := "Polarity correction: A and B talk about the same situation."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "correction"), ("polarity", "negative"), ("turn", "A")]
    comment := "The negative claim that B corrects."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2B1 : LinguisticExample :=
  { id := "turcobraundimroth2014_2B1"
    source := ⟨"turco-braun-dimroth-2014", "(2) B1"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Kind HAT geweint."
    discourseSegments := []
    glossedTokens := []
    translation := "The child DID cry."
    context := "Reply to (2) A about the same situation."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "correction"), ("polarity", "positive"), ("marking", "verumFocus")]
    comment := "Verum focus; the claims of A and B1 exclude each other, being about the same topic situation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2B2 : LinguisticExample :=
  { id := "turcobraundimroth2014_2B2"
    source := ⟨"turco-braun-dimroth-2014", "(2) B2"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Kind hat SCHON/WOHL geweint."
    discourseSegments := []
    glossedTokens := []
    translation := "The child did INDEED cry."
    context := "Reply to (2) A about the same situation."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "correction"), ("polarity", "positive"), ("marking", "particle")]
    comment := "An accented affirmative particle in place of Verum focus."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "turcobraundimroth2014_3"
    source := ⟨"turco-braun-dimroth-2014", "(3)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Meneer Rood durft niet te springen. Meneer Blauw is WEL gesprongen want het vuur stond inmiddels ook al in zijn kamer."
    discourseSegments := ["Meneer Rood durft niet te springen.", "Meneer Blauw is WEL gesprongen want het vuur stond inmiddels ook al in zijn kamer."]
    glossedTokens := []
    translation := "Mr Red does not dare to jump. Mr Blue is indeed jumping because there is already fire in his room."
    context := "A house is on fire; a native speaker of Dutch retells the Finite Story film."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("context", "contrast"), ("polarity", "positive"), ("marking", "particle"), ("genre", "monologue")]
    comment := "Accented wel in a monologue marks a polarity contrast between two topic entities without undoing the earlier claim; from the Finite Story data of Dimroth and colleagues."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def vf_negated : LinguisticExample :=
  { id := "turcobraundimroth2014_vf_negated"
    source := ⟨"turco-braun-dimroth-2014", "section 4"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Das Kind HAT nicht geweint."
    discourseSegments := []
    glossedTokens := []
    translation := "The child DID not cry."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("marking", "verumFocus")]
    comment := "Verum focus in a negated sentence: the assertion operator takes effect on a level above polarity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def wel_negated : LinguisticExample :=
  { id := "turcobraundimroth2014_wel_negated"
    source := ⟨"turco-braun-dimroth-2014", "section 4"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Het kind heeft wel niet gehuild."
    discourseSegments := []
    glossedTokens := []
    translation := "The child DID not cry."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("polarity", "negative"), ("marking", "particle")]
    comment := "The affirmative particle cannot occur in a negated sentence: wel and niet are values of the one polarity operator."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1A, ex_1B1, ex_1B2, ex_2A, ex_2B1, ex_2B2, ex_3, vf_negated, wel_negated]

end TurcoBraunDimroth2014.Examples
