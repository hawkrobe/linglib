module

public import Linglib.Data.Examples.Schema

/-!
# `Izvorski1997` — typed example data

Auto-generated from `Linglib/Data/Examples/Izvorski1997.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Izvorski1997.Examples`.
-/

@[expose] public section

namespace Izvorski1997.Examples

open Data.Examples

def s1a : Datum :=
  { id := "izvorski1997_s1a"
    source := ⟨"izvorski-1997", "(1a)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Gel-miş-im."
    glossedTokens := [("Gel", "come"), ("-miş", "PERF"), ("-im", "1SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("reading", "perfect of evidentiality only")] }

def s1b : Datum :=
  { id := "izvorski1997_s1b"
    source := ⟨"izvorski-1997", "(1b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Az săm došăl."
    glossedTokens := [("Az", "I"), ("săm", "be-1SG.PRES"), ("došăl", "come-P.PART")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("reading", "ambiguous: present perfect or perfect of evidentiality")] }

def s1c : Datum :=
  { id := "izvorski1997_s1c"
    source := ⟨"izvorski-1997", "(1c)"⟩
    reportedIn := none
    language := "norw1258"
    primaryText := "Jeg har kommet."
    glossedTokens := [("Jeg", "I"), ("har", "have-1SG.PRES"), ("kommet", "come-P.PART")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("reading", "ambiguous: present perfect or perfect of evidentiality")] }

def s2a : Datum :=
  { id := "izvorski1997_s2a"
    source := ⟨"izvorski-1997", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is an apparent/supposed/alleged/reported thief."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("claim", "lexical evidentials keep their meaning in every configuration")] }

def s2b : Datum :=
  { id := "izvorski1997_s2b"
    source := ⟨"izvorski-1997", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is apparently/supposedly/allegedly/reportedly a thief."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1")] }

def s2c : Datum :=
  { id := "izvorski1997_s2c"
    source := ⟨"izvorski-1997", "(2c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John appears/is supposed/is alleged/is reported to be a thief."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1")] }

def s2d : Datum :=
  { id := "izvorski1997_s2d"
    source := ⟨"izvorski-1997", "(2d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For it to appear that John is a thief one would have to tell a lot of lies."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1")] }

def s3 : Datum :=
  { id := "izvorski1997_s3"
    source := ⟨"izvorski-1997", "(3)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "ol-müş adam"
    glossedTokens := [("ol", "die"), ("-müş", "PERF"), ("adam", "man")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("claim", "no evidential reading of the adjectival participle")] }

def s4 : Datum :=
  { id := "izvorski1997_s4"
    source := ⟨"izvorski-1997", "(4)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Gel-miş-tim."
    glossedTokens := [("Gel", "come"), ("-miş", "PERF"), ("-tim", "1SG.PAST")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("claim", "no evidential reading of the past perfect")] }

def s5 : Datum :=
  { id := "izvorski1997_s5"
    source := ⟨"izvorski-1997", "(5)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Gel-miş ol-acak-ım."
    glossedTokens := [("Gel", "come"), ("-miş", "PERF"), ("ol", "be"), ("-acak", "FUT"), ("-ım", "1SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("claim", "no evidential reading of the future perfect")] }

def s6 : Datum :=
  { id := "izvorski1997_s6"
    source := ⟨"izvorski-1997", "(6)"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Kitap yaz-mış ol-mak büyük bir başarı."
    glossedTokens := [("Kitap", "book"), ("yaz", "write"), ("-mış", "PERF"), ("ol", "be"), ("-mak", "INF"), ("büyük", "big"), ("bir", "a"), ("başarı", "achievement")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "1"), ("claim", "no evidential reading in non-finite clauses")] }

def s7a : Datum :=
  { id := "izvorski1997_s7a"
    source := ⟨"izvorski-1997", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I saw/heard John singing."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("evidence", "direct: visual/auditory")] }

def s7b : Datum :=
  { id := "izvorski1997_s7b"
    source := ⟨"izvorski-1997", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I see/hear (that) John was singing."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("evidence", "indirect: inference/report")] }

def s7c : Datum :=
  { id := "izvorski1997_s7c"
    source := ⟨"izvorski-1997", "(7c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was apparently singing."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("evidence", "indirect: inference or report")] }

def s9a : Datum :=
  { id := "izvorski1997_s9a"
    source := ⟨"izvorski-1997", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She climbed Mount Toby."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("source", "Kratzer 1991")] }

def s9b : Datum :=
  { id := "izvorski1997_s9b"
    source := ⟨"izvorski-1997", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She must have climbed Mount Toby."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("source", "Kratzer 1991"), ("claim", "weaker than (9a): no entailment of p")] }

def s10a : Datum :=
  { id := "izvorski1997_s10a"
    source := ⟨"izvorski-1997", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Knowing how much John likes wine, he must have drunk all the wine yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("claim", "general knowledge justifies must")] }

def s10b : Datum :=
  { id := "izvorski1997_s10b"
    source := ⟨"izvorski-1997", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Knowing how much John likes wine, he apparently drank all the wine yesterday."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("claim", "general knowledge is no indirect evidence")] }

def s11a : Datum :=
  { id := "izvorski1997_s11a"
    source := ⟨"izvorski-1997", "(11a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Znaejki kolko Ivan običa vino, toj trjabva da e izpil vsičkoto vino včera."
    glossedTokens := [("toj", "he"), ("trjabva", "must"), ("da", "to"), ("e", "is"), ("izpil", "drunk"), ("vsičkoto", "all-the"), ("vino", "wine"), ("včera", "yesterday")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3")] }

def s11b : Datum :=
  { id := "izvorski1997_s11b"
    source := ⟨"izvorski-1997", "(11b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Znaejki kolko Ivan običa vino, toj izpil vsičkoto vino včera."
    glossedTokens := [("toj", "he"), ("izpil", "drunk-PE"), ("vsičkoto", "all-the"), ("vino", "wine"), ("včera", "yesterday")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3")] }

def s12 : Datum :=
  { id := "izvorski1997_s12"
    source := ⟨"izvorski-1997", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: John must have drunk all the wine. A': But I have no evidence for that."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("claim", "must does not presuppose evidence")] }

def s13 : Datum :=
  { id := "izvorski1997_s13"
    source := ⟨"izvorski-1997", "(13)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "A: Ivan izpil vsičkoto vino včera. A': But I have no evidence for that."
    glossedTokens := [("Ivan", "Ivan"), ("izpil", "drunk-PE"), ("vsičkoto", "all-the"), ("vino", "wine"), ("včera", "yesterday")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("claim", "the evidential presupposes evidence")] }

def s14 : Datum :=
  { id := "izvorski1997_s14"
    source := ⟨"izvorski-1997", "(14)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "A: Maria celunala Ivan. A': (Actually) I witnessed it."
    glossedTokens := [("Maria", "Maria"), ("celunala", "kiss-PE"), ("Ivan", "Ivan")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("claim", "the evidence must be indirect and cannot be cancelled")] }

def s15a : Datum :=
  { id := "izvorski1997_s15a"
    source := ⟨"izvorski-1997", "(15a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Apparently, Ivan didn't pass the exam."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("claim", "negation targets the proposition, not the evidence")] }

def s15b : Datum :=
  { id := "izvorski1997_s15b"
    source := ⟨"izvorski-1997", "(15b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Ivan ne izkaral izpita."
    glossedTokens := [("Ivan", "Ivan"), ("ne", "not"), ("izkaral", "passed-PE"), ("izpita", "the-exam")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("claim", "negation targets the proposition, not the evidence")] }

def s16 : Datum :=
  { id := "izvorski1997_s16"
    source := ⟨"izvorski-1997", "(16)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "A: Ivan izkaral izpita. B: This isn't true."
    glossedTokens := [("Ivan", "Ivan"), ("izkaral", "passed-PE"), ("izpita", "the-exam")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("claim", "denial targets the proposition")] }

def s20a : Datum :=
  { id := "izvorski1997_s20a"
    source := ⟨"izvorski-1997", "(20a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Te sa došli (??včera)/(??snošti)/(??točno v 3 časa)."
    glossedTokens := [("Te", "they"), ("sa", "are"), ("došli", "come-P.PART")]
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("claim", "the present perfect rejects past-time adverbials")] }

def s20b : Datum :=
  { id := "izvorski1997_s20b"
    source := ⟨"izvorski-1997", "(20b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Te došli včera/snošti/točno v 3 časa."
    glossedTokens := [("Te", "they"), ("došli", "come-PE")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("claim", "the evidential aorist accepts past-time adverbials")] }

def s21a : Datum :=
  { id := "izvorski1997_s21a"
    source := ⟨"izvorski-1997", "(21a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Toj e pisel pismo (*točno sega)/(*točno v tozi moment)."
    glossedTokens := [("Toj", "he"), ("e", "is"), ("pisel", "written-P.PART"), ("pismo", "letter")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("claim", "the present perfect rejects speech-time adverbials")] }

def s21b : Datum :=
  { id := "izvorski1997_s21b"
    source := ⟨"izvorski-1997", "(21b)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Toj pisel pismo točno sega/točno v tozi moment."
    glossedTokens := [("Toj", "he"), ("pisel", "written-PE"), ("pismo", "letter")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("claim", "the evidential present accepts speech-time adverbials")] }

def s22 : Datum :=
  { id := "izvorski1997_s22"
    source := ⟨"izvorski-1997", "(22)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Dve pljus dve (*e) bilo ravno na četiri."
    glossedTokens := [("Dve", "two"), ("pljus", "plus"), ("dve", "two"), ("e", "be-3SG"), ("bilo", "been"), ("ravno", "equal"), ("na", "to"), ("četiri", "four")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("claim", "individual-level predicates take the evidential, not the perfect")] }

def s23a : Datum :=
  { id := "izvorski1997_s23a"
    source := ⟨"izvorski-1997", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Einstein has visited Princeton."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("claim", "current relevance fails with a dead topic")] }

def s23b : Datum :=
  { id := "izvorski1997_s23b"
    source := ⟨"izvorski-1997", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Einstein visited Princeton."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4")] }

def s24 : Datum :=
  { id := "izvorski1997_s24"
    source := ⟨"izvorski-1997", "(24)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Ajnštajn (#e) posetil Prinstăn."
    glossedTokens := [("Ajnštajn", "Einstein"), ("e", "be-3SG"), ("posetil", "visited"), ("Prinstăn", "Princeton")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("claim", "the evidential lacks the temporal interpretation of the present perfect")] }

def s25 : Datum :=
  { id := "izvorski1997_s25"
    source := ⟨"izvorski-1997", "(25)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "(There was a book on the table.) The book was in Russian."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("source", "Klein 1994"), ("claim", "past tense locates the topic time, not the situation")] }

def s27 : Datum :=
  { id := "izvorski1997_s27"
    source := ⟨"izvorski-1997", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The book has been in Russian."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.2"), ("claim", "the present perfect requires the eventuality not to hold at speech time")] }

def all : List Datum := [s1a, s1b, s1c, s2a, s2b, s2c, s2d, s3, s4, s5, s6, s7a, s7b, s7c, s9a, s9b, s10a, s10b, s11a, s11b, s12, s13, s14, s15a, s15b, s16, s20a, s20b, s21a, s21b, s22, s23a, s23b, s24, s25, s27]

end Izvorski1997.Examples
