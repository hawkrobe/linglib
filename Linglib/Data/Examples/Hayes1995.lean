import Linglib.Data.Examples.Schema

/-!
# `Hayes1995` — typed example data

Auto-generated from `Linglib/Data/Examples/Hayes1995.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hayes1995.Examples`.
-/

namespace Hayes1995.Examples

open Data.Examples

def katabt : LinguisticExample :=
  { id := "hayes1995_katabt"
    source := ⟨"hayes-1995", "(12a)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "katábt"
    discourseSegments := []
    glossedTokens := []
    translation := "I wrote"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "L S"), ("stress", "final"), ("register", "colloquial Cairene"), ("source", "Harrell 1957, 15")]
    comment := "Superheavy final, heavy after Consonant Extrametricality."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def hajjaan : LinguisticExample :=
  { id := "hayes1995_hajjaan"
    source := ⟨"hayes-1995", "(12a)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "hajjá:n"
    discourseSegments := []
    glossedTokens := []
    translation := "pilgrimages"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "H S"), ("stress", "final"), ("register", "Cairene Classical"), ("source", "Mitchell 1975, 77")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def gatoo : LinguisticExample :=
  { id := "hayes1995_gatoo"
    source := ⟨"hayes-1995", "(12a)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "gató:"
    discourseSegments := []
    glossedTokens := []
    translation := "cake"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "L S"), ("stress", "final"), ("register", "colloquial Cairene"), ("source", "Mitchell 1975, 81")]
    comment := "Final CV: counts as heavy in colloquial forms."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def beetak : LinguisticExample :=
  { id := "hayes1995_beetak"
    source := ⟨"hayes-1995", "(12b)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "bé:tak"
    discourseSegments := []
    glossedTokens := []
    translation := "your (m.sg.) house"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "H L"), ("stress", "penult"), ("register", "colloquial Cairene"), ("source", "Harrell 1957, 15")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def katabta : LinguisticExample :=
  { id := "hayes1995_katabta"
    source := ⟨"hayes-1995", "(12b)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "katábta"
    discourseSegments := []
    glossedTokens := []
    translation := "you (m.sg.) wrote"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "L H L"), ("stress", "penult"), ("register", "Cairene Classical"), ("source", "Mitchell 1975, 78")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mudarris : LinguisticExample :=
  { id := "hayes1995_mudarris"
    source := ⟨"hayes-1995", "(12b)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "mudárris"
    discourseSegments := []
    glossedTokens := []
    translation := "teacher"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "L H L"), ("stress", "penult"), ("register", "colloquial Cairene"), ("source", "McCarthy 1979a, 446")]
    comment := "Final CVC demoted to light; (15b), (16b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def haadaani : LinguisticExample :=
  { id := "hayes1995_haadaani"
    source := ⟨"hayes-1995", "(12b)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "ha:ðá:ni"
    discourseSegments := []
    glossedTokens := []
    translation := "these (m.dual)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "H H L"), ("stress", "penult"), ("register", "Cairene Classical"), ("source", "Mitchell 1975, 77")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def qattaala : LinguisticExample :=
  { id := "hayes1995_qattaala"
    source := ⟨"hayes-1995", "(12c.i.A)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "qattála"
    discourseSegments := []
    glossedTokens := []
    translation := "he killed"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "H L L"), ("stress", "penult"), ("register", "Cairene Classical"), ("source", "Mitchell 1975, 77"), ("parity", "even from the preceding heavy")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mudarrisit : LinguisticExample :=
  { id := "hayes1995_mudarrisit"
    source := ⟨"hayes-1995", "(12c.i.A)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "mudarrísit"
    discourseSegments := []
    glossedTokens := []
    translation := "teacher (f. construct)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "L H L L"), ("stress", "penult"), ("register", "colloquial Cairene"), ("source", "McCarthy 1979a, 446"), ("parity", "even from the preceding heavy")]
    comment := "(15c), (16c)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def Padwiyatuhu : LinguisticExample :=
  { id := "hayes1995_Padwiyatuhu"
    source := ⟨"hayes-1995", "(12c.i.A)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "ʔadwiyatúhu"
    discourseSegments := []
    glossedTokens := []
    translation := "his drugs (nom.)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "H L L L L"), ("stress", "penult"), ("register", "Cairene Classical"), ("source", "Mitchell 1975, 79"), ("parity", "even from the preceding heavy")]
    comment := "(15c), (16c)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def fihim : LinguisticExample :=
  { id := "hayes1995_fihim"
    source := ⟨"hayes-1995", "(12c.i.B)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "fíhim"
    discourseSegments := []
    glossedTokens := []
    translation := "he understood"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "L L"), ("stress", "penult"), ("register", "colloquial Cairene"), ("source", "Kenstowicz 1980, 42"), ("parity", "even from the word beginning")]
    comment := "(15c), (16c)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sajaratun : LinguisticExample :=
  { id := "hayes1995_sajaratun"
    source := ⟨"hayes-1995", "(12c.i.B)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "šajarátun"
    discourseSegments := []
    glossedTokens := []
    translation := "tree (nom.)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "L L L L"), ("stress", "penult"), ("register", "Cairene Classical"), ("source", "Mitchell 1975, 78"), ("parity", "even from the word beginning")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def katabitu : LinguisticExample :=
  { id := "hayes1995_katabitu"
    source := ⟨"hayes-1995", "(12c.i.B)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "katabítu"
    discourseSegments := []
    glossedTokens := []
    translation := "she wrote it (m.)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "L L L L"), ("stress", "penult"), ("register", "colloquial Cairene"), ("source", "Harrell 1957, 15"), ("parity", "even from the word beginning")]
    comment := "(15c), (16c)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sajaratuhuma : LinguisticExample :=
  { id := "hayes1995_sajaratuhuma"
    source := ⟨"hayes-1995", "(12c.i.B)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "šajaratuhúma:"
    discourseSegments := []
    glossedTokens := []
    translation := "their (dual) tree (nom.)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "L L L L L L"), ("stress", "penult"), ("register", "Cairene Classical"), ("source", "Mitchell 1975, 79"), ("parity", "even from the word beginning")]
    comment := "Final CV: light by Mora Extrametricality; (15c), (16c)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def Pinkasara : LinguisticExample :=
  { id := "hayes1995_Pinkasara"
    source := ⟨"hayes-1995", "(12c.ii.A)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "ʔinkásara"
    discourseSegments := []
    glossedTokens := []
    translation := "it got broken"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "H L L L"), ("stress", "antepenult"), ("register", "Cairene Classical"), ("source", "Mitchell 1975, 77"), ("parity", "odd from the preceding heavy")]
    comment := "(15d), (16d)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def Padwiyatuhuma : LinguisticExample :=
  { id := "hayes1995_Padwiyatuhuma"
    source := ⟨"hayes-1995", "(12c.ii.A)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "ʔadwiyatúhuma:"
    discourseSegments := []
    glossedTokens := []
    translation := "their (dual) drugs"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "H L L L L L"), ("stress", "antepenult"), ("register", "Cairene Classical"), ("source", "Mitchell 1975, 79"), ("parity", "odd from the preceding heavy")]
    comment := "(15d), (16d)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def kataba : LinguisticExample :=
  { id := "hayes1995_kataba"
    source := ⟨"hayes-1995", "(12c.ii.B)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "kátaba"
    discourseSegments := []
    glossedTokens := []
    translation := "he wrote"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "L L L"), ("stress", "antepenult"), ("register", "Cairene Classical"), ("source", "Mitchell 1975, 77"), ("parity", "odd from the word beginning")]
    comment := "(15d), (16d), (17): the stray final light cannot be promoted."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sajaratuhu : LinguisticExample :=
  { id := "hayes1995_sajaratuhu"
    source := ⟨"hayes-1995", "(12c.ii.B)"⟩
    reportedIn := none
    language := "egyp1253"
    primaryText := "šajarátuhu"
    discourseSegments := []
    glossedTokens := []
    translation := "his tree (nom.)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1.3"), ("weights", "L L L L L"), ("stress", "antepenult"), ("register", "Cairene Classical"), ("source", "Mitchell 1975, 80"), ("parity", "odd from the word beginning")]
    comment := "(15d), (16d)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [katabt, hajjaan, gatoo, beetak, katabta, mudarris, haadaani, qattaala, mudarrisit, Padwiyatuhu, fihim, sajaratun, katabitu, sajaratuhuma, Pinkasara, Padwiyatuhuma, kataba, sajaratuhu]

end Hayes1995.Examples
