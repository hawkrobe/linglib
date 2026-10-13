module

public import Linglib.Data.Examples.Schema

/-!
# `VanCraenenbroeck2014` — typed example data

Auto-generated from `Linglib/Data/Examples/VanCraenenbroeck2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VanCraenenbroeck2014.Examples`.
-/

@[expose] public section

namespace VanCraenenbroeck2014.Examples

def ex_10a : Datum :=
  { id := "vancraenenbroeck2014_10a"
    source := ⟨"van-craenenbroeck-2014", "(10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kyle criticized my paper."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "selection"), ("category", "verb")] }

def ex_10b : Datum :=
  { id := "vancraenenbroeck2014_10b"
    source := ⟨"van-craenenbroeck-2014", "(10b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kyle's criticism of my paper."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "selection"), ("category", "noun")] }

def ex_11 : Datum :=
  { id := "vancraenenbroeck2014_11"
    source := ⟨"van-craenenbroeck-2014", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kyle criticized my paper and Rajesh did {the same/likewise} to my book."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "pronominalization"), ("category", "verb"), ("proform", "the same/likewise"), ("argument", "stranded")] }

def ex_13 : Datum :=
  { id := "vancraenenbroeck2014_13"
    source := ⟨"van-craenenbroeck-2014", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kyle criticized my paper and Rajesh did {the same/likewise}."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "pronominalization"), ("category", "verb"), ("proform", "the same/likewise"), ("argument", "included")] }

def ex_15a : Datum :=
  { id := "vancraenenbroeck2014_15a"
    source := ⟨"van-craenenbroeck-2014", "(15a)"⟩
    reportedIn := none
    language := "west2354"
    primaryText := "Jitske besprekt syn roman."
    glossedTokens := [("Jitske", "Jitske"), ("besprekt", "reviews"), ("syn", "his"), ("roman.", "novel")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "selection"), ("category", "verb")] }

def ex_15b : Datum :=
  { id := "vancraenenbroeck2014_15b"
    source := ⟨"van-craenenbroeck-2014", "(15b)"⟩
    reportedIn := none
    language := "west2354"
    primaryText := "in besprek fan syn roman"
    glossedTokens := [("in", "a"), ("besprek", "review"), ("fan", "of"), ("syn", "his"), ("roman", "novel")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "selection"), ("category", "noun")] }

def ex_16 : Datum :=
  { id := "vancraenenbroeck2014_16"
    source := ⟨"van-craenenbroeck-2014", "(16)"⟩
    reportedIn := none
    language := "west2354"
    primaryText := "Jan hie in witte auto en Geart in swarten ien."
    glossedTokens := [("Jan", "Jan"), ("hie", "has"), ("in", "a"), ("witte", "white"), ("auto", "car"), ("en", "and"), ("Geart", "Geart"), ("in", "a"), ("swarten", "black"), ("ien.", "one")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "npEllipsis"), ("proform", "ien")] }

def ex_17a : Datum :=
  { id := "vancraenenbroeck2014_17a"
    source := ⟨"van-craenenbroeck-2014", "(17a)"⟩
    reportedIn := none
    language := "west2354"
    primaryText := "Jitse wiisde him op in posityf besprek fan syn roman en Jitske op in negativen ien fan syn samle fersen."
    glossedTokens := [("Jitse", "Jitse"), ("wiisde", "pointed"), ("him", "him"), ("op", "on"), ("in", "a"), ("posityf", "positive"), ("besprek", "review"), ("fan", "of"), ("syn", "his"), ("roman", "novel"), ("en", "and"), ("Jitske", "Jitske"), ("op", "on"), ("in", "a"), ("negativen", "negative"), ("ien", "one"), ("fan", "of"), ("syn", "his"), ("samle", "collected"), ("fersen.", "poems")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "pronominalization"), ("category", "noun"), ("proform", "ien"), ("argument", "stranded")] }

def ex_17b : Datum :=
  { id := "vancraenenbroeck2014_17b"
    source := ⟨"van-craenenbroeck-2014", "(17b)"⟩
    reportedIn := none
    language := "west2354"
    primaryText := "Jitse wiisde him op in posityf besprek fan syn roman en Jitske op in negativen ien."
    glossedTokens := [("Jitse", "Jitse"), ("wiisde", "pointed"), ("him", "him"), ("op", "on"), ("in", "a"), ("posityf", "positive"), ("besprek", "review"), ("fan", "of"), ("syn", "his"), ("roman", "novel"), ("en", "and"), ("Jitske", "Jitske"), ("op", "on"), ("in", "a"), ("negativen", "negative"), ("ien.", "one")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2"), ("construction", "pronominalization"), ("category", "noun"), ("proform", "ien"), ("argument", "included")] }

def ex_18a : Datum :=
  { id := "vancraenenbroeck2014_18a"
    source := ⟨"van-craenenbroeck-2014", "(18a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Ze geeft hem de bons."
    glossedTokens := [("Ze", "she"), ("geeft", "gives"), ("hem", "him"), ("de", "the"), ("bons.", "knock")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "bons"), ("form", "active")] }

def ex_18b : Datum :=
  { id := "vancraenenbroeck2014_18b"
    source := ⟨"van-craenenbroeck-2014", "(18b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "het geven van de bons (aan hem)"
    glossedTokens := [("het", "the"), ("geven", "give.INF"), ("van", "of"), ("de", "the"), ("bons", "knock"), ("(aan", "to"), ("hem)", "him")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "bons"), ("form", "nominalizedInfinitive")] }

def ex_18c : Datum :=
  { id := "vancraenenbroeck2014_18c"
    source := ⟨"van-craenenbroeck-2014", "(18c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De bons wordt hem door haar gegeven."
    glossedTokens := [("De", "the"), ("bons", "knock"), ("wordt", "becomes"), ("hem", "him"), ("door", "by"), ("haar", "her"), ("gegeven.", "given")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "bons"), ("form", "passive")] }

def ex_19a : Datum :=
  { id := "vancraenenbroeck2014_19a"
    source := ⟨"van-craenenbroeck-2014", "(19a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Dat doet hem de das om."
    glossedTokens := [("Dat", "that"), ("doet", "puts"), ("hem", "him"), ("de", "the"), ("das", "tie"), ("om.", "on")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "das"), ("form", "active")] }

def ex_19b : Datum :=
  { id := "vancraenenbroeck2014_19b"
    source := ⟨"van-craenenbroeck-2014", "(19b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Hem wordt de das omgedaan."
    glossedTokens := [("Hem", "him"), ("wordt", "becomes"), ("de", "the"), ("das", "tie"), ("omgedaan.", "put.on")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "das"), ("form", "passive")] }

def ex_19c : Datum :=
  { id := "vancraenenbroeck2014_19c"
    source := ⟨"van-craenenbroeck-2014", "(19c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "het hem omdoen van de das"
    glossedTokens := [("het", "the"), ("hem", "him"), ("omdoen", "on.put.INF"), ("van", "of"), ("de", "the"), ("das", "tie")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "das"), ("form", "nominalizedInfinitive")] }

def ex_20a : Datum :=
  { id := "vancraenenbroeck2014_20a"
    source := ⟨"van-craenenbroeck-2014", "(20a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Hij begraaft de strijdbijl."
    glossedTokens := [("Hij", "he"), ("begraaft", "buries"), ("de", "the"), ("strijdbijl.", "hatchet")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "strijdbijl"), ("form", "active")] }

def ex_20b : Datum :=
  { id := "vancraenenbroeck2014_20b"
    source := ⟨"van-craenenbroeck-2014", "(20b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "het begraven van de strijdbijl"
    glossedTokens := [("het", "the"), ("begraven", "bury.INF"), ("van", "of"), ("de", "the"), ("strijdbijl", "hatchet")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "strijdbijl"), ("form", "nominalizedInfinitive")] }

def ex_20c : Datum :=
  { id := "vancraenenbroeck2014_20c"
    source := ⟨"van-craenenbroeck-2014", "(20c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "De strijdbijl wordt begraven."
    glossedTokens := [("De", "the"), ("strijdbijl", "hatchet"), ("wordt", "becomes"), ("begraven.", "buried")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "strijdbijl"), ("form", "passive")] }

def ex_21a : Datum :=
  { id := "vancraenenbroeck2014_21a"
    source := ⟨"van-craenenbroeck-2014", "(21a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Hij breekt het ijs."
    glossedTokens := [("Hij", "he"), ("breekt", "breaks"), ("het", "the"), ("ijs.", "ice")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "ijs"), ("form", "active")] }

def ex_21b : Datum :=
  { id := "vancraenenbroeck2014_21b"
    source := ⟨"van-craenenbroeck-2014", "(21b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "het breken van het ijs"
    glossedTokens := [("het", "the"), ("breken", "break.INF"), ("van", "of"), ("het", "the"), ("ijs", "ice")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "ijs"), ("form", "nominalizedInfinitive")] }

def ex_21c : Datum :=
  { id := "vancraenenbroeck2014_21c"
    source := ⟨"van-craenenbroeck-2014", "(21c)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "Het ijs is gebroken."
    glossedTokens := [("Het", "the"), ("ijs", "ice"), ("is", "is"), ("gebroken.", "broken")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "ijs"), ("form", "passive")] }

def ex_22a : Datum :=
  { id := "vancraenenbroeck2014_22a"
    source := ⟨"van-craenenbroeck-2014", "(22a)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "de begraving van de strijdbijl"
    glossedTokens := [("de", "the"), ("begraving", "bury.NOMINALIZER"), ("van", "of"), ("de", "the"), ("strijdbijl", "hatchet")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "strijdbijl"), ("form", "nominalization")] }

def ex_22b : Datum :=
  { id := "vancraenenbroeck2014_22b"
    source := ⟨"van-craenenbroeck-2014", "(22b)"⟩
    reportedIn := none
    language := "dutc1256"
    primaryText := "de breking van het ijs"
    glossedTokens := [("de", "the"), ("breking", "break.NOMINALIZER"), ("van", "of"), ("het", "the"), ("ijs", "ice")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("construction", "idiom"), ("idiom", "ijs"), ("form", "nominalization")] }

def all : List Datum := [ex_10a, ex_10b, ex_11, ex_13, ex_15a, ex_15b, ex_16, ex_17a, ex_17b, ex_18a, ex_18b, ex_18c, ex_19a, ex_19b, ex_19c, ex_20a, ex_20b, ex_20c, ex_21a, ex_21b, ex_21c, ex_22a, ex_22b]

end VanCraenenbroeck2014.Examples
