module

public import Linglib.Data.Examples.Schema

/-!
# `IatridouEtAl2001` — typed example data

Auto-generated from `Linglib/Data/Examples/IatridouEtAl2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace IatridouEtAl2001.Examples`.
-/

@[expose] public section

namespace IatridouEtAl2001.Examples

open Data.Examples

def iai2001_ex1 : Datum :=
  { id := "iai2001_ex1"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Petros has visited Thailand."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.1"), ("reading", "anteriority")] }

def iai2001_ex2a : Datum :=
  { id := "iai2001_ex2a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have been sick since 1990."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("reading", "universal"), ("adverbial", "since"), ("predicate", "stative")] }

def iai2001_ex3a : Datum :=
  { id := "iai2001_ex3a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have read Principia Mathematica five times."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("reading", "experiential")] }

def iai2001_ex4 : Datum :=
  { id := "iai2001_ex4"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have lost my glasses."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("reading", "perfect of result")] }

def iai2001_ex5 : Datum :=
  { id := "iai2001_ex5"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He has just graduated from college."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2.2"), ("reading", "perfect of recent past")] }

def iai2001_ex6a : Datum :=
  { id := "iai2001_ex6a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She has been sick at least since 1990 but she is fine now."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("reading", "universal"), ("point", "RB included by assertion")] }

def iai2001_ex6b : Datum :=
  { id := "iai2001_ex6b"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She has always lived here but she doesn't anymore."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("reading", "universal"), ("point", "RB included by assertion")] }

def iai2001_ex7 : Datum :=
  { id := "iai2001_ex7"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary visited Peter last week. A strange bug had bitten him a week before and he had been very sick since then. Mary will visit Peter again in two weeks. At that point, he will have been sick for a month."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.1"), ("reading", "universal"), ("tense", "past and future perfect"), ("point", "RB set by tense")] }

def iai2001_ex8 : Datum :=
  { id := "iai2001_ex8"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He has had brown eyes since he was born."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("He has had brown eyes.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3.2.1"), ("predicate", "individual-level stative"), ("adverbial", "required")] }

def iai2001_ex9 : Datum :=
  { id := "iai2001_ex9"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary has been sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("predicate", "stage-level stative"), ("reading", "not universal")] }

def iai2001_ex11 : Datum :=
  { id := "iai2001_ex11"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She has been sick lately."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("reading", "perfect of recent past")] }

def iai2001_ex13B : Datum :=
  { id := "iai2001_ex13B"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(13B)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Tja e bila bolna."
    glossedTokens := [("Tja", "she"), ("e", "is"), ("bila", "been"), ("bolna", "sick")]
    context := "A: I haven't seen Mary in a while. Where is she?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("reading", "no perfect of recent past")] }

def iai2001_ex14a : Datum :=
  { id := "iai2001_ex14a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(14a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She has been sick lately."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("She was sick lately.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3.2.1"), ("adverbial", "lately takes the present perfect")] }

def iai2001_ex14d : Datum :=
  { id := "iai2001_ex14d"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(14d)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Tja beshe bolna naposleduk."
    glossedTokens := [("Tja", "she"), ("beshe", "was"), ("bolna", "sick"), ("naposleduk", "lately")]
    context := ""
    judgment := .acceptable
    alternatives := [("Tja e bila bolna naposleduk.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3.2.1"), ("adverbial", "lately takes the past in Bulgarian")] }

def iai2001_ex15 : Datum :=
  { id := "iai2001_ex15"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have been cooking."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.1"), ("predicate", "progressive"), ("reading", "not universal")] }

def iai2001_ex17a : Datum :=
  { id := "iai2001_ex17a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have been sick since yesterday."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("I am sick since yesterday.", .ungrammatical), ("I was sick since 1990.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3.2.2"), ("adverbial", "since is perfect-level")] }

def iai2001_ex18a : Datum :=
  { id := "iai2001_ex18a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Since 1990 I have been sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("adverbial", "since"), ("readings", "universal and existential")] }

def iai2001_ex19a : Datum :=
  { id := "iai2001_ex19a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Since 1990, I have read The Book of Sand five times."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("adverbial", "since"), ("readings", "existential only")] }

def iai2001_ex20a : Datum :=
  { id := "iai2001_ex20a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have been sick for five days."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("adverbial", "for, sentence-final"), ("readings", "universal and existential")] }

def iai2001_ex20b : Datum :=
  { id := "iai2001_ex20b"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For five days, I have been sick."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("adverbial", "for, sentence-initial"), ("readings", "universal only")] }

def iai2001_ex21a : Datum :=
  { id := "iai2001_ex21a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(21a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Since 1970, I have been sick for five days."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("adverbial", "eventuality-level for under perfect-level since"), ("reading", "existential")] }

def iai2001_ex22a : Datum :=
  { id := "iai2001_ex22a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have lived in Thessaloniki for ten years."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("adverbial", "for"), ("readings", "universal if perfect-level, existential if eventuality-level")] }

def iai2001_ex23a : Datum :=
  { id := "iai2001_ex23a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has been in Boston for two weeks."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("adverbial", "for, sentence-final"), ("readings", "ambiguous")] }

def iai2001_ex23b : Datum :=
  { id := "iai2001_ex23b"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For two weeks, John has been in Boston."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("adverbial", "for, sentence-initial"), ("readings", "universal only")] }

def iai2001_ex24 : Datum :=
  { id := "iai2001_ex24"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Since 1990, I have read The Book of Sand five times."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("adverbial", "since, sentence-initial"), ("reading", "existential")] }

def iai2001_ex25a : Datum :=
  { id := "iai2001_ex25a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emma has always been tall."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Emma is always tall.", .ungrammatical), ("Emma was always tall.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3.2.2"), ("adverbial", "perfect-level always"), ("predicate", "individual-level")] }

def iai2001_ex26 : Datum :=
  { id := "iai2001_ex26"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Since 1990, I have always been tall."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("adverbial", "always with since"), ("predicate", "individual-level")] }

def iai2001_ex27c : Datum :=
  { id := "iai2001_ex27c"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(27c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Since 1990, I have always been sick when he has visited me."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.2.2"), ("adverbial", "eventuality-level always"), ("predicate", "stage-level")] }

def iai2001_ex28 : Datum :=
  { id := "iai2001_ex28"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Since 1991, I have been to Cape Cod only once, namely, in the fall of 1993."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("point", "PTS is not the E-R interval"), ("LB", "1991"), ("event", "fall 1993")] }

def iai2001_ex30 : Datum :=
  { id := "iai2001_ex30"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(30)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Exo panta zisi stin Athina."
    glossedTokens := [("Exo", "have.1SG"), ("panta", "always"), ("zisi", "lived"), ("stin", "in.the"), ("Athina", "Athens")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4"), ("reading", "universal unavailable"), ("participle", "perfective")] }

def iai2001_ex31 : Datum :=
  { id := "iai2001_ex31"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(31)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Extisa ena spiti mesa se ena xrono."
    glossedTokens := [("Extisa", "build.PST.PFV.1SG"), ("ena", "a"), ("spiti", "house"), ("mesa", "in"), ("se", "in"), ("ena", "one"), ("xrono", "year")]
    context := ""
    judgment := .acceptable
    alternatives := [("Extisa ena spiti ya ena xrono.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3.4"), ("aspect", "perfective, bounded")] }

def iai2001_ex32 : Datum :=
  { id := "iai2001_ex32"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(32)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Extiza to spiti ya ena xrono."
    glossedTokens := [("Extiza", "build.PST.IPFV.1SG"), ("to", "the"), ("spiti", "house"), ("ya", "for"), ("ena", "one"), ("xrono", "year")]
    context := ""
    judgment := .acceptable
    alternatives := [("Extiza to spiti mesa se ena xrono.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3.4"), ("aspect", "imperfective, unbounded")] }

def iai2001_ex33 : Datum :=
  { id := "iai2001_ex33"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(33)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Yiannis ayapise tin Maria to 1981."
    glossedTokens := [("O", "the"), ("Yiannis", "Yiannis"), ("ayapise", "love.PST.PFV.3SG"), ("tin", "the"), ("Maria", "Maria"), ("to", "in"), ("1981", "1981")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.1"), ("aspect", "perfective on a stative is inchoative")] }

def iai2001_ex34 : Datum :=
  { id := "iai2001_ex34"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(34)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "O Yiannis exi ayapisi tin Maria."
    glossedTokens := [("O", "the"), ("Yiannis", "Yiannis"), ("exi", "has.3SG"), ("ayapisi", "loved"), ("tin", "the"), ("Maria", "Maria")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.1"), ("reading", "existential only"), ("participle", "perfective")] }

def iai2001_ex35 : Datum :=
  { id := "iai2001_ex35"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(35)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Marija e obiknala Ivan."
    glossedTokens := [("Marija", "Maria"), ("e", "is"), ("obiknala", "love.PFV.PTCP"), ("Ivan", "Ivan")]
    context := ""
    judgment := .acceptable
    alternatives := [("Marija vinagi e obiknala Ivan.", .ungrammatical), ("Marija e obiknala Ivan ot 1980 nasam.", .ungrammatical)]
    readings := []
    paperFeatures := [("section", "3.4.2"), ("reading", "existential only"), ("participle", "perfective")] }

def iai2001_ex36 : Datum :=
  { id := "iai2001_ex36"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(36)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Marija vinagi e obicala Ivan."
    glossedTokens := [("Marija", "Maria"), ("vinagi", "always"), ("e", "is"), ("obicala", "love.IPFV.PTCP"), ("Ivan", "Ivan")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.2"), ("reading", "universal"), ("participle", "imperfective")] }

def iai2001_ex39 : Datum :=
  { id := "iai2001_ex39"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(39)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Az sum pila vinoto ot sutrinta nasam."
    glossedTokens := [("Az", "I"), ("sum", "am"), ("pila", "drink.NEUT.PTCP"), ("vinoto", "the.wine"), ("ot", "from"), ("sutrinta", "this.morning"), ("nasam", "towards.now")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.2"), ("reading", "universal"), ("participle", "neutral")] }

def iai2001_ex40 : Datum :=
  { id := "iai2001_ex40"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He has read the book but he didn't finish it."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("aspect", "the English perfect of a telic is bounded")] }

def iai2001_ex41a : Datum :=
  { id := "iai2001_ex41a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(41a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He has danced ever since this morning."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("predicate", "activity, nonprogressive"), ("reading", "universal unavailable")] }

def iai2001_ex41b : Datum :=
  { id := "iai2001_ex41b"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(41b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He has drawn a circle ever since this morning."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.3"), ("predicate", "telic, nonprogressive"), ("reading", "universal unavailable")] }

def iai2001_ex45 : Datum :=
  { id := "iai2001_ex45"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(45)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "Exi kivernisi apo to 1990 mexri tora."
    glossedTokens := [("Exi", "has.3SG"), ("kivernisi", "governed"), ("apo", "from"), ("to", "the"), ("1990", "1990"), ("mexri", "until"), ("tora", "now")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.4.4"), ("reading", "throughout with a bounded activity ending at RB")] }

def iai2001_ex47 : Datum :=
  { id := "iai2001_ex47"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was asleep when I arrived."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("test", "Vlach's stativity test"), ("feature", "unbounded")] }

def iai2001_ex48 : Datum :=
  { id := "iai2001_ex48"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John was lifting weights when I arrived."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4"), ("test", "Vlach's stativity test passed by a progressive"), ("feature", "unbounded")] }

def iai2001_ex49a : Datum :=
  { id := "iai2001_ex49a"
    source := ⟨"iatridou-anagnostopoulou-izvorski-2001", "(49a)"⟩
    reportedIn := none
    language := "bulg1262"
    primaryText := "Ivan pisa pismoto kogato Maria vleze v stajata."
    glossedTokens := [("Ivan", "Ivan"), ("pisa", "write.NEUT.PST"), ("pismoto", "the.letter"), ("kogato", "when"), ("Maria", "Maria"), ("vleze", "entered"), ("v", "in"), ("stajata", "the.room")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("Ivan pisheshe pismoto kogato Maria vleze v stajata.", .acceptable)]
    readings := []
    paperFeatures := [("section", "4"), ("test", "the neutral fails Vlach's test"), ("feature", "unbounded")] }

def all : List Datum := [iai2001_ex1, iai2001_ex2a, iai2001_ex3a, iai2001_ex4, iai2001_ex5, iai2001_ex6a, iai2001_ex6b, iai2001_ex7, iai2001_ex8, iai2001_ex9, iai2001_ex11, iai2001_ex13B, iai2001_ex14a, iai2001_ex14d, iai2001_ex15, iai2001_ex17a, iai2001_ex18a, iai2001_ex19a, iai2001_ex20a, iai2001_ex20b, iai2001_ex21a, iai2001_ex22a, iai2001_ex23a, iai2001_ex23b, iai2001_ex24, iai2001_ex25a, iai2001_ex26, iai2001_ex27c, iai2001_ex28, iai2001_ex30, iai2001_ex31, iai2001_ex32, iai2001_ex33, iai2001_ex34, iai2001_ex35, iai2001_ex36, iai2001_ex39, iai2001_ex40, iai2001_ex41a, iai2001_ex41b, iai2001_ex45, iai2001_ex47, iai2001_ex48, iai2001_ex49a]

end IatridouEtAl2001.Examples
