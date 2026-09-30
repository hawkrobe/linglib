module

public import Linglib.Data.Examples.Schema

/-!
# `Krifka2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Krifka2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Krifka2013.Examples`.
-/

@[expose] public section

namespace Krifka2013.Examples

open Data.Examples

def ex1a : LinguisticExample :=
  { id := "krifka2013_ex1a"
    source := ⟨"krifka-2013", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Madrigals are polyphonic."
    glossedTokens := []
    context := "A bare plural with a defining property."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "barePlural"), ("reading", "definitional")] }

def ex1b : LinguisticExample :=
  { id := "krifka2013_ex1b"
    source := ⟨"krifka-2013", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A madrigal is polyphonic."
    glossedTokens := []
    context := "An indefinite singular with a defining property."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "definitional")] }

def ex2a : LinguisticExample :=
  { id := "krifka2013_ex2a"
    source := ⟨"krifka-2013", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Madrigals are popular."
    glossedTokens := []
    context := "A bare plural with an accidental property."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "barePlural"), ("reading", "descriptive")] }

def ex2b : LinguisticExample :=
  { id := "krifka2013_ex2b"
    source := ⟨"krifka-2013", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A madrigal is popular."
    glossedTokens := []
    context := "An indefinite singular with an accidental property: being popular cannot be a definitional criterion for madrigals."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "descriptive")] }

def ex3a : LinguisticExample :=
  { id := "krifka2013_ex3a"
    source := ⟨"krifka-2013", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A kangaroo is a marsupial."
    glossedTokens := []
    context := "Burton-Roberts's analytic indefinite-singular generic, equivalent to *To be a kangaroo is to be a marsupial*."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "definitional")] }

def ex4a : LinguisticExample :=
  { id := "krifka2013_ex4a"
    source := ⟨"krifka-2013", "(4a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A tiger climbs trees."
    glossedTokens := []
    context := "Bolinger's intuition, reported by Burton-Roberts: true, though *To be a tiger is to climb trees* is false."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "descriptive")] }

def ex5 : LinguisticExample :=
  { id := "krifka2013_ex5"
    source := ⟨"krifka-2013", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "An electron has a negative electric charge."
    glossedTokens := []
    context := "A physical rule."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "definitional"), ("rule", "physical")] }

def ex6 : LinguisticExample :=
  { id := "krifka2013_ex6"
    source := ⟨"krifka-2013", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A gentleman opens doors for ladies."
    glossedTokens := []
    context := "A moral rule; *gentleman* names a social kind."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "definitional"), ("rule", "moral")] }

def ex7 : LinguisticExample :=
  { id := "krifka2013_ex7"
    source := ⟨"krifka-2013", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A bishop moves diagonally."
    glossedTokens := []
    context := "A legal rule of chess."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "definitional"), ("rule", "legal")] }

def ex8 : LinguisticExample :=
  { id := "krifka2013_ex8"
    source := ⟨"krifka-2013", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A pomegranate apple costs 49 cents."
    glossedTokens := []
    context := "A legal rule, the price set by the shop manager."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "definitional"), ("rule", "legal")] }

def ex13 : LinguisticExample :=
  { id := "krifka2013_ex13"
    source := ⟨"krifka-2013", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Boys don't cry."
    glossedTokens := []
    context := "Read descriptively, a generalization about boys under a shared interpretation; read definitionally, a proposal to restrict the interpretation of *boys*."
    judgment := .acceptable
    alternatives := []
    readings := [("descriptive", .acceptable), ("definitional", .acceptable)]
    paperFeatures := [("subject", "barePlural")] }

def ex29 : LinguisticExample :=
  { id := "krifka2013_ex29"
    source := ⟨"krifka-2013", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A donkey has 62 chromosomes."
    glossedTokens := []
    context := "An empirical finding that reads as definitional: the chromosome number runs in the species."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "definitional")] }

def ex37 : LinguisticExample :=
  { id := "krifka2013_ex37"
    source := ⟨"krifka-2013", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "An animal in this cage has 62 chromosomes."
    glossedTokens := []
    context := "The subject does not pick out a natural kind on which a species-based generalization could rest."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "definitional")] }

def ex38 : LinguisticExample :=
  { id := "krifka2013_ex38"
    source := ⟨"krifka-2013", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A duck lays eggs."
    glossedTokens := []
    context := "Universal in the definitional reconstruction, the property being suppressed in immature and male ducks."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "definitional")] }

def ex39 : LinguisticExample :=
  { id := "krifka2013_ex39"
    source := ⟨"krifka-2013", "(39)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A shark attacks bathers."
    glossedTokens := []
    context := "A minority but striking property."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular")] }

def ex42a : LinguisticExample :=
  { id := "krifka2013_ex42a"
    source := ⟨"krifka-2013", "(42a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A king is generous."
    glossedTokens := []
    context := "An unmodified indefinite singular with an accidental property."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "descriptive")] }

def ex42b : LinguisticExample :=
  { id := "krifka2013_ex42b"
    source := ⟨"krifka-2013", "(42b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A good king is generous."
    glossedTokens := []
    context := "A partial definition of what makes a king good."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "definitional")] }

def ex43 : LinguisticExample :=
  { id := "krifka2013_ex43"
    source := ⟨"krifka-2013", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A banana that has been sat on by a rhinoceros is flat."
    glossedTokens := []
    context := "A descriptive generalization with an indefinite-singular subject."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "descriptive")] }

def ex44a : LinguisticExample :=
  { id := "krifka2013_ex44a"
    source := ⟨"krifka-2013", "(44a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A trout can be caught by many different methods."
    glossedTokens := []
    context := "A descriptive generalization with an indefinite-singular subject; the methods do not run in the species."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "descriptive")] }

def ex44b : LinguisticExample :=
  { id := "krifka2013_ex44b"
    source := ⟨"krifka-2013", "(44b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A hedgehog makes a good pet."
    glossedTokens := []
    context := "A generalization in which single animals matter."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "descriptive")] }

def ex45a : LinguisticExample :=
  { id := "krifka2013_ex45a"
    source := ⟨"krifka-2013", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Guppies make good pets."
    glossedTokens := []
    context := "An animal typically held in larger quantities."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "barePlural"), ("reading", "descriptive")] }

def ex45b : LinguisticExample :=
  { id := "krifka2013_ex45b"
    source := ⟨"krifka-2013", "(45b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A guppy makes a good pet."
    glossedTokens := []
    context := "An animal typically held in larger quantities."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "indefiniteSingular"), ("reading", "descriptive")] }

def all : List LinguisticExample := [ex1a, ex1b, ex2a, ex2b, ex3a, ex4a, ex5, ex6, ex7, ex8, ex13, ex29, ex37, ex38, ex39, ex42a, ex42b, ex43, ex44a, ex44b, ex45a, ex45b]

end Krifka2013.Examples
