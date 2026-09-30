module

public import Linglib.Data.Examples.Schema

/-!
# `Storment2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Storment2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Storment2026.Examples`.
-/

@[expose] public section

namespace Storment2026.Examples

def ex1a : Datum :=
  { id := "storment2026_ex1a"
    source := ⟨"storment-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Peace!’ said Saruman."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi")] }

def ex4 : Datum :=
  { id := "storment2026_ex4"
    source := ⟨"storment-2026", "(4)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Le kae? ga botsa Seabelo."
    glossedTokens := [("Le kae?", "and where?"), ("ga", "SM17.PST"), ("botsa", "ask"), ("Seabelo", "Seabelo")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi")] }

def ex7 : Datum :=
  { id := "storment2026_ex7"
    source := ⟨"storment-2026", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Sméagol has to take what’s given to him,’ Gollum answered."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "preposedQuote")] }

def ex10 : Datum :=
  { id := "storment2026_ex10"
    source := ⟨"storment-2026", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘D’oh!’ said the man drunk."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "afterAgent")] }

def ex12 : Datum :=
  { id := "storment2026_ex12"
    source := ⟨"storment-2026", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘D’oh!’ said drunk the man."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "beforeAgent")] }

def ex14 : Datum :=
  { id := "storment2026_ex14"
    source := ⟨"storment-2026", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘D’oh!’ shouted drunk the man I’ve never met before."
    glossedTokens := []
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("heavyNPShift", "yes")] }

def ex15 : Datum :=
  { id := "storment2026_ex15"
    source := ⟨"storment-2026", "(15)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Fire!’ cried Cecil to get the crowd’s attention."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "afterAgent")] }

def ex16 : Datum :=
  { id := "storment2026_ex16"
    source := ⟨"storment-2026", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Fire!’ cried to get the crowd’s attention Cecil."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "beforeAgent")] }

def ex19 : Datum :=
  { id := "storment2026_ex19"
    source := ⟨"storment-2026", "(19)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Nothing, nothing,’ said Gollum softly."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "afterAgent")] }

def ex20 : Datum :=
  { id := "storment2026_ex20"
    source := ⟨"storment-2026", "(20)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Nothing, nothing,’ said softly Gollum."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "beforeAgent")] }

def ex25a : Datum :=
  { id := "storment2026_ex25a"
    source := ⟨"storment-2026", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Nothing, nothing,’ said Gollum, muttering all about."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "afterAgent")] }

def ex25b : Datum :=
  { id := "storment2026_ex25b"
    source := ⟨"storment-2026", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Nothing, nothing,’ said muttering all about Gollum."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "beforeAgent")] }

def ex26a : Datum :=
  { id := "storment2026_ex26a"
    source := ⟨"storment-2026", "(26a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Help!’ tried to yell Alex."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpComplement"), ("position", "beforeAgent")] }

def ex26b : Datum :=
  { id := "storment2026_ex26b"
    source := ⟨"storment-2026", "(26b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Help!’ tried Alex to yell."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpComplement"), ("position", "afterAgent")] }

def ex29a : Datum :=
  { id := "storment2026_ex29a"
    source := ⟨"storment-2026", "(29a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Where are you going?’ called out John."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpComplement"), ("position", "beforeAgent")] }

def ex29b : Datum :=
  { id := "storment2026_ex29b"
    source := ⟨"storment-2026", "(29b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Where are you going?’ called John out."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpComplement"), ("position", "afterAgent")] }

def ex11 : Datum :=
  { id := "storment2026_ex11"
    source := ⟨"storment-2026", "(11)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Dumela! go bua Seabelo a tagilwe."
    glossedTokens := [("Dumela!", "hello!"), ("go", "SM17"), ("bua", "said"), ("Seabelo", "Seabelo"), ("a", "SM1"), ("tagilwe", "drunk")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "afterAgent")] }

def ex13 : Datum :=
  { id := "storment2026_ex13"
    source := ⟨"storment-2026", "(13)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Dumela! go bua a tagilwe Seabelo."
    glossedTokens := [("Dumela!", "hello!"), ("go", "SM17"), ("bua", "said"), ("a", "SM1"), ("tagilwe", "drunk"), ("Seabelo", "Seabelo")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "beforeAgent")] }

def ex17 : Datum :=
  { id := "storment2026_ex17"
    source := ⟨"storment-2026", "(17)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Molelo! go go-ile Seabelo go kopa thuso."
    glossedTokens := [("Molelo!", "fire!"), ("go", "SM17"), ("go-ile", "yell-PRF"), ("Seabelo", "Seabelo"), ("go", "SM17"), ("kopa", "plead"), ("thuso", "help")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "afterAgent")] }

def ex18 : Datum :=
  { id := "storment2026_ex18"
    source := ⟨"storment-2026", "(18)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Molelo! go go-ile go kopa thuso Seabelo."
    glossedTokens := [("Molelo!", "fire!"), ("go", "SM17"), ("go-ile", "yell-PRF"), ("go", "SM17"), ("kopa", "plead"), ("thuso", "help"), ("Seabelo", "Seabelo")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "beforeAgent")] }

def ex21 : Datum :=
  { id := "storment2026_ex21"
    source := ⟨"storment-2026", "(21)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Titi o molato, go bua kgosi kapela."
    glossedTokens := [("Titi", "Titi"), ("o", "SM.3SG"), ("molato", "guilty"), ("go", "SM17"), ("bua", "say"), ("kgosi", "chief"), ("kapela", "quick")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "afterAgent")] }

def ex22 : Datum :=
  { id := "storment2026_ex22"
    source := ⟨"storment-2026", "(22)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Titi o molato, go bua kapela kgosi."
    glossedTokens := [("Titi", "Titi"), ("o", "SM.3SG"), ("molato", "guilty"), ("go", "SM17"), ("bua", "say"), ("kapela", "quick"), ("kgosi", "chief")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpAdjunct"), ("position", "beforeAgent")] }

def ex27 : Datum :=
  { id := "storment2026_ex27"
    source := ⟨"storment-2026", "(27)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Ke a go rata, go batla go bua Seabelo."
    glossedTokens := [("Ke", "1SG"), ("a", "DISJ"), ("go", "2SG"), ("rata", "like"), ("go", "SM17"), ("batla", "want"), ("go", "SM17"), ("bua", "say"), ("Seabelo", "Seabelo")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpComplement"), ("position", "beforeAgent")] }

def ex28 : Datum :=
  { id := "storment2026_ex28"
    source := ⟨"storment-2026", "(28)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Ke a go rata, go batla Seabelo go bua."
    glossedTokens := [("Ke", "1SG"), ("a", "DISJ"), ("go", "2SG"), ("rata", "like"), ("go", "SM17"), ("batla", "want"), ("Seabelo", "Seabelo"), ("go", "SM17"), ("bua", "say")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("material", "vpComplement"), ("position", "afterAgent")] }

def ex36 : Datum :=
  { id := "storment2026_ex36"
    source := ⟨"storment-2026", "(36)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Mmuu, go bua dikgomo."
    glossedTokens := [("Mmuu", "moo"), ("go", "SM17"), ("bua", "say"), ("dikgomo", "cows")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "agreement"), ("subjectMarker", "SM17")] }

def ex36_sm10 : Datum :=
  { id := "storment2026_ex36_sm10"
    source := ⟨"storment-2026", "(36)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Mmuu, di bua dikgomo."
    glossedTokens := [("Mmuu", "moo"), ("di", "SM10"), ("bua", "say"), ("dikgomo", "cows")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "agreement"), ("subjectMarker", "SM10")] }

def ex38 : Datum :=
  { id := "storment2026_ex38"
    source := ⟨"storment-2026", "(38)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Dumela, go bua nna."
    glossedTokens := [("Dumela", "hello"), ("go", "SM17"), ("bua", "say"), ("nna", "I")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "agreement"), ("subjectMarker", "SM17")] }

def ex38_ke : Datum :=
  { id := "storment2026_ex38_ke"
    source := ⟨"storment-2026", "(38)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Dumela, ke bua nna."
    glossedTokens := [("Dumela", "hello"), ("ke", "SM.1SG"), ("bua", "say"), ("nna", "I")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "agreement"), ("subjectMarker", "SM.1SG")] }

def ex40 : Datum :=
  { id := "storment2026_ex40"
    source := ⟨"storment-2026", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Avoid beef,’ advise all the New Age dieticians."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "agreement"), ("agreement", "plural")] }

def ex40_sg : Datum :=
  { id := "storment2026_ex40_sg"
    source := ⟨"storment-2026", "(40)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Avoid beef,’ advises all the New Age dieticians."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "agreement"), ("agreement", "singular")] }

def ex62a : Datum :=
  { id := "storment2026_ex62a"
    source := ⟨"storment-2026", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘We should leave,’ thought Max without actually saying __."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "parasiticGap")] }

def ex62b : Datum :=
  { id := "storment2026_ex62b"
    source := ⟨"storment-2026", "(62b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘We should leave,’ Max thought without actually saying __."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "preposedQuote"), ("diagnostic", "parasiticGap")] }

def ex64 : Datum :=
  { id := "storment2026_ex64"
    source := ⟨"storment-2026", "(64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Sméagol has to take what’s given to him,’ the Hobbits answer."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "preposedQuote"), ("diagnostic", "agreement"), ("agreement", "plural")] }

def ex64_sg : Datum :=
  { id := "storment2026_ex64_sg"
    source := ⟨"storment-2026", "(64)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Sméagol has to take what’s given to him,’ the Hobbits answers."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "preposedQuote"), ("diagnostic", "agreement"), ("agreement", "singular")] }

def ex65 : Datum :=
  { id := "storment2026_ex65"
    source := ⟨"storment-2026", "(65)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Le kae? Seabelo a botsa."
    glossedTokens := [("Le kae?", "and where?"), ("Seabelo", "Seabelo"), ("a", "SM.3SG.PST"), ("botsa", "ask")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "preposedQuote"), ("diagnostic", "agreement"), ("subjectMarker", "SM.3SG.PST")] }

def ex65_ga : Datum :=
  { id := "storment2026_ex65_ga"
    source := ⟨"storment-2026", "(65)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Le kae? Seabelo ga botsa."
    glossedTokens := [("Le kae?", "and where?"), ("Seabelo", "Seabelo"), ("ga", "SM17.PST"), ("botsa", "ask")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "preposedQuote"), ("diagnostic", "agreement"), ("subjectMarker", "SM17.PST")] }

def ex67a : Datum :=
  { id := "storment2026_ex67a"
    source := ⟨"storment-2026", "(67a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Where did the wheat go?’ seemed to say the heron."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "raising")] }

def ex69a : Datum :=
  { id := "storment2026_ex69a"
    source := ⟨"storment-2026", "(69a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Where did the wheat go?’ seemed the heron to say."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "preposedQuote"), ("diagnostic", "raising")] }

def ex77 : Datum :=
  { id := "storment2026_ex77"
    source := ⟨"storment-2026", "(77)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Dumela, go nna go bua nna."
    glossedTokens := [("Dumela", "hello"), ("go", "SM17"), ("nna", "stay"), ("go", "SM17"), ("bua", "say"), ("nna", "I")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "raising"), ("subjectMarker", "SM17")] }

def ex87 : Datum :=
  { id := "storment2026_ex87"
    source := ⟨"storment-2026", "(87)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Dumela, go bua Seabelo."
    glossedTokens := [("Dumela", "hello"), ("go", "SM17"), ("bua", "say"), ("Seabelo", "Seabelo")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "conjointDisjoint"), ("verbForm", "conjoint")] }

def ex87_disj : Datum :=
  { id := "storment2026_ex87_disj"
    source := ⟨"storment-2026", "(87)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Dumela, go a bua Seabelo."
    glossedTokens := [("Dumela", "hello"), ("go", "SM17"), ("a", "DISJ"), ("bua", "say"), ("Seabelo", "Seabelo")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "conjointDisjoint"), ("verbForm", "disjoint")] }

def ex88 : Datum :=
  { id := "storment2026_ex88"
    source := ⟨"storment-2026", "(88)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Said the night wind to the little lamb, ‘Do you hear what I hear?’"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "quoteCategory")] }

def ex89 : Datum :=
  { id := "storment2026_ex89"
    source := ⟨"storment-2026", "(89)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Ga botsa Seabelo, Le kae?"
    glossedTokens := [("Ga", "SM17.PST"), ("botsa", "ask"), ("Seabelo", "Seabelo"), ("Le kae?", "and where?")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "quoteCategory")] }

def ex90 : Datum :=
  { id := "storment2026_ex90"
    source := ⟨"storment-2026", "(90)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘But,’ said Frodo, ‘That is a long way off.’"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "quoteCategory")] }

def ex92 : Datum :=
  { id := "storment2026_ex92"
    source := ⟨"storment-2026", "(92)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘I think that you…’ said Mary, ‘…should go to the store tomorrow.’"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "quoteCategory")] }

def ex93a : Datum :=
  { id := "storment2026_ex93a"
    source := ⟨"storment-2026", "(93a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Walked John into the room."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "li"), ("diagnostic", "quoteCategory")] }

def ex96a : Datum :=
  { id := "storment2026_ex96a"
    source := ⟨"storment-2026", "(96a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Pop!’ goes the weasel."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "quoteCategory")] }

def ex97a : Datum :=
  { id := "storment2026_ex97a"
    source := ⟨"storment-2026", "(97a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘Who did a picture of hang on the wall?’ said the professor of linguistics."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("diagnostic", "quoteCategory")] }

def ex123 : Datum :=
  { id := "storment2026_ex123"
    source := ⟨"storment-2026", "(123)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John warned Mary, ‘There is danger ahead.’"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "canonical")] }

def ex125 : Datum :=
  { id := "storment2026_ex125"
    source := ⟨"storment-2026", "(125)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘There is danger ahead,’ warned Mary John."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("smuggledDPs", "2")] }

def ex127 : Datum :=
  { id := "storment2026_ex127"
    source := ⟨"storment-2026", "(127)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘There is danger ahead,’ warned John Mary."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("smuggledDPs", "2")] }

def ex129 : Datum :=
  { id := "storment2026_ex129"
    source := ⟨"storment-2026", "(129)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "‘There is danger ahead,’ warned John to Mary."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("smuggledDPs", "1")] }

def ex126 : Datum :=
  { id := "storment2026_ex126"
    source := ⟨"storment-2026", "(126)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Go na le mathaithai kwa pele, go tlhagisitse Neo Thabo."
    glossedTokens := [("Go na le mathaithai kwa pele", "SM17 be with puzzles 17LOC ahead"), ("go", "SM17"), ("tlhagisitse", "warn"), ("Neo", "Neo"), ("Thabo", "Thabo")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("smuggledDPs", "2")] }

def ex130 : Datum :=
  { id := "storment2026_ex130"
    source := ⟨"storment-2026", "(130)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Go na le mathaithai kwa pele, go tlhagisitse Thabo a tlhagisa Neo."
    glossedTokens := [("Go na le mathaithai kwa pele", "SM17 be with puzzles 17LOC ahead"), ("go", "SM17"), ("tlhagisitse", "warn"), ("Thabo", "Thabo"), ("a", "SM.3SG.PST"), ("tlhagisa", "warn"), ("Neo", "Neo")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "qi"), ("smuggledDPs", "1")] }

def ex134a : Datum :=
  { id := "storment2026_ex134a"
    source := ⟨"storment-2026", "(134a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Into the room walked Mary her dog."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "li"), ("smuggledDPs", "2")] }

def ex135 : Datum :=
  { id := "storment2026_ex135"
    source := ⟨"storment-2026", "(135)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Go et-ela basimane koko."
    glossedTokens := [("Go", "SM17"), ("et-ela", "visit-APPL"), ("basimane", "boys"), ("koko", "grandmother")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "li"), ("smuggledDPs", "2")] }

def ex55 : Datum :=
  { id := "storment2026_ex55"
    source := ⟨"storment-2026", "(55)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Kwa maemelong a diterena ga goroga terena."
    glossedTokens := [("Kwa", "17LOC"), ("maemelong", "station"), ("a", "of"), ("diterena", "trains"), ("ga", "SM17.PST"), ("goroga", "arrive"), ("terena", "train")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "li")] }

def ex136a : Datum :=
  { id := "storment2026_ex136a"
    source := ⟨"storment-2026", "(136a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Down from the wall leapt Gimli."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "li")] }

def ex138 : Datum :=
  { id := "storment2026_ex138"
    source := ⟨"storment-2026", "(138)"⟩
    reportedIn := none
    language := "tswa1253"
    primaryText := "Mo kamoreng go setse go tsene Seabelo."
    glossedTokens := [("Mo", "18LOC"), ("kamoreng", "room-LOC"), ("go", "SM17"), ("setse", "already"), ("go", "SM17"), ("tsene", "walk"), ("Seabelo", "Seabelo")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "li"), ("diagnostic", "raising"), ("subjectMarker", "SM17")] }

def all : List Datum := [ex1a, ex4, ex7, ex10, ex12, ex14, ex15, ex16, ex19, ex20, ex25a, ex25b, ex26a, ex26b, ex29a, ex29b, ex11, ex13, ex17, ex18, ex21, ex22, ex27, ex28, ex36, ex36_sm10, ex38, ex38_ke, ex40, ex40_sg, ex62a, ex62b, ex64, ex64_sg, ex65, ex65_ga, ex67a, ex69a, ex77, ex87, ex87_disj, ex88, ex89, ex90, ex92, ex93a, ex96a, ex97a, ex123, ex125, ex127, ex129, ex126, ex130, ex134a, ex135, ex55, ex136a, ex138]

end Storment2026.Examples
