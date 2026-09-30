module

public import Linglib.Data.Examples.Schema

/-!
# `GoldbergJackendoff2004` — typed example data

Auto-generated from `Linglib/Data/Examples/GoldbergJackendoff2004.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GoldbergJackendoff2004.Examples`.
-/

@[expose] public section

namespace GoldbergJackendoff2004.Examples

open Data.Examples

def gj2004_5a : LinguisticExample :=
  { id := "gj2004_5a"
    source := ⟨"goldberg-jackendoff-2004", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Herman hammered the metal flat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hammer"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("selection", "selected")] }

def gj2004_5b : LinguisticExample :=
  { id := "gj2004_5b"
    source := ⟨"goldberg-jackendoff-2004", "(5b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The critics laughed the play off the stage."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "laugh"), ("subconstruction", "causative path"), ("rpCat", "PP"), ("selection", "unselected")] }

def gj2004_6a : LinguisticExample :=
  { id := "gj2004_6a"
    source := ⟨"goldberg-jackendoff-2004", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The pond froze solid."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "freeze"), ("subconstruction", "noncausative property"), ("rpCat", "AP")] }

def gj2004_6b : LinguisticExample :=
  { id := "gj2004_6b"
    source := ⟨"goldberg-jackendoff-2004", "(6b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill rolled out of the room."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "roll"), ("subconstruction", "noncausative path"), ("rpCat", "PP")] }

def gj2004_7a : LinguisticExample :=
  { id := "gj2004_7a"
    source := ⟨"goldberg-jackendoff-2004", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The gardener watered the flowers flat."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "water"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("selection", "selected")] }

def gj2004_7b : LinguisticExample :=
  { id := "gj2004_7b"
    source := ⟨"goldberg-jackendoff-2004", "(7b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill broke the bathtub into pieces."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "break"), ("subconstruction", "causative property"), ("rpCat", "PP"), ("selection", "selected")] }

def gj2004_8a : LinguisticExample :=
  { id := "gj2004_8a"
    source := ⟨"goldberg-jackendoff-2004", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They drank the pub dry."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("*They drank the pub.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "drink"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("selection", "unselected")] }

def gj2004_8b : LinguisticExample :=
  { id := "gj2004_8b"
    source := ⟨"goldberg-jackendoff-2004", "(8b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The professor talked us into a stupor."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("*The professor talked us.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "talk"), ("subconstruction", "causative property"), ("rpCat", "PP"), ("selection", "unselected")] }

def gj2004_9a : LinguisticExample :=
  { id := "gj2004_9a"
    source := ⟨"goldberg-jackendoff-2004", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We yelled ourselves hoarse."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("*We yelled ourselves.", .ungrammatical), ("*We yelled Harry hoarse.", .ungrammatical)]
    readings := []
    paperFeatures := [("verb", "yell"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("selection", "fake reflexive")] }

def gj2004_23a : LinguisticExample :=
  { id := "gj2004_23a"
    source := ⟨"goldberg-jackendoff-2004", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For hours, Bill heated the mixture hotter and hotter."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "heat"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("endBounded", "false")] }

def gj2004_23b : LinguisticExample :=
  { id := "gj2004_23b"
    source := ⟨"goldberg-jackendoff-2004", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For hours, Bill hammered the metal ever flatter."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "hammer"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("endBounded", "false")] }

def gj2004_23c : LinguisticExample :=
  { id := "gj2004_23c"
    source := ⟨"goldberg-jackendoff-2004", "(23c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "For years, Penelope wove the shawl longer and longer."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "weave"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("endBounded", "false")] }

def gj2004_24a : LinguisticExample :=
  { id := "gj2004_24a"
    source := ⟨"goldberg-jackendoff-2004", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*Bill floated into the cave for hours."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "float"), ("subconstruction", "noncausative path"), ("rpCat", "PP"), ("endBounded", "true")] }

def gj2004_24b : LinguisticExample :=
  { id := "gj2004_24b"
    source := ⟨"goldberg-jackendoff-2004", "(24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*Bill pushed Harry off the sofa for hours."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "push"), ("subconstruction", "causative path"), ("rpCat", "PP"), ("endBounded", "true")] }

def gj2004_24c : LinguisticExample :=
  { id := "gj2004_24c"
    source := ⟨"goldberg-jackendoff-2004", "(24c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill floated down the river for hours."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "float"), ("subconstruction", "noncausative path"), ("rpCat", "PP"), ("endBounded", "false")] }

def gj2004_24d : LinguisticExample :=
  { id := "gj2004_24d"
    source := ⟨"goldberg-jackendoff-2004", "(24d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill pushed Harry along the trail for hours."
    glossedTokens := []
    context := "Nonrepetitive reading."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "push"), ("subconstruction", "causative path"), ("rpCat", "PP"), ("endBounded", "false")] }

def gj2004_45a : LinguisticExample :=
  { id := "gj2004_45a"
    source := ⟨"goldberg-jackendoff-2004", "(45a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*She yelled hoarse."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "yell"), ("subconstruction", "noncausative property"), ("rpCat", "AP"), ("subjectRole", "agent")] }

def gj2004_45b : LinguisticExample :=
  { id := "gj2004_45b"
    source := ⟨"goldberg-jackendoff-2004", "(45b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*Ted cried to sleep."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cry"), ("subconstruction", "noncausative property"), ("rpCat", "PP"), ("subjectRole", "agent")] }

def gj2004_45c : LinguisticExample :=
  { id := "gj2004_45c"
    source := ⟨"goldberg-jackendoff-2004", "(45c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The tiger bled to death."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "bleed"), ("subconstruction", "noncausative property"), ("rpCat", "PP"), ("subjectRole", "patient")] }

def gj2004_46a : LinguisticExample :=
  { id := "gj2004_46a"
    source := ⟨"goldberg-jackendoff-2004", "(46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He coughed awake and we were all overjoyed, especially Sierra."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cough"), ("subconstruction", "noncausative property"), ("rpCat", "AP"), ("subjectRole", "agent or patient")] }

def gj2004_47a : LinguisticExample :=
  { id := "gj2004_47a"
    source := ⟨"goldberg-jackendoff-2004", "(47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Patamon coughed himself awake on the bank of the lake where he and Gomammon had their play."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "cough"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("selection", "fake reflexive"), ("subjectRole", "agent or patient")] }

def gj2004_48a : LinguisticExample :=
  { id := "gj2004_48a"
    source := ⟨"goldberg-jackendoff-2004", "(48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The worm wriggled onto the carpet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "wriggle"), ("subconstruction", "noncausative path"), ("rpCat", "PP"), ("subjectRole", "agent")] }

def gj2004_48b : LinguisticExample :=
  { id := "gj2004_48b"
    source := ⟨"goldberg-jackendoff-2004", "(48b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The chocolate melted onto the carpet."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "melt"), ("subconstruction", "noncausative path"), ("rpCat", "PP"), ("subjectRole", "patient")] }

def gj2004_49a : LinguisticExample :=
  { id := "gj2004_49a"
    source := ⟨"goldberg-jackendoff-2004", "(49a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill wiggled himself loose."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "wiggle"), ("subconstruction", "causative path"), ("rpCat", "AP"), ("subjectRole", "agent")] }

def gj2004_49b : LinguisticExample :=
  { id := "gj2004_49b"
    source := ⟨"goldberg-jackendoff-2004", "(49b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Aliza wiggled her tooth loose."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "wiggle"), ("subconstruction", "causative path"), ("rpCat", "AP"), ("subjectRole", "agent")] }

def gj2004_49c : LinguisticExample :=
  { id := "gj2004_49c"
    source := ⟨"goldberg-jackendoff-2004", "(49c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The mechanical doll wiggled itself loose."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "wiggle"), ("subconstruction", "causative path"), ("rpCat", "AP"), ("subjectRole", "agent")] }

def gj2004_49e : LinguisticExample :=
  { id := "gj2004_49e"
    source := ⟨"goldberg-jackendoff-2004", "(49e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "*The ball wiggled itself loose."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb", "wiggle"), ("subconstruction", "causative path"), ("rpCat", "AP"), ("subjectRole", "patient")] }

def gj2004_wipe : LinguisticExample :=
  { id := "gj2004_wipe"
    source := ⟨"goldberg-jackendoff-2004", "§6.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She wiped the table clean."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "wipe"), ("subconstruction", "causative property"), ("rpCat", "AP"), ("selection", "selected"), ("objectRole", "patient")] }

def gj2004_97c : LinguisticExample :=
  { id := "gj2004_97c"
    source := ⟨"goldberg-jackendoff-2004", "(97c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The truck rumbled into the station."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "rumble"), ("subconstruction", "noncausative path"), ("rpCat", "PP"), ("subeventRelation", "result")] }

def all : List LinguisticExample := [gj2004_5a, gj2004_5b, gj2004_6a, gj2004_6b, gj2004_7a, gj2004_7b, gj2004_8a, gj2004_8b, gj2004_9a, gj2004_23a, gj2004_23b, gj2004_23c, gj2004_24a, gj2004_24b, gj2004_24c, gj2004_24d, gj2004_45a, gj2004_45b, gj2004_45c, gj2004_46a, gj2004_47a, gj2004_48a, gj2004_48b, gj2004_49a, gj2004_49b, gj2004_49c, gj2004_49e, gj2004_wipe, gj2004_97c]

end GoldbergJackendoff2004.Examples
