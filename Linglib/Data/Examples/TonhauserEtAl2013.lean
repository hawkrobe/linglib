module

public import Linglib.Data.Examples.Schema

/-!
# `TonhauserEtAl2013` — typed example data

Auto-generated from `Linglib/Data/Examples/TonhauserEtAl2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TonhauserEtAl2013.Examples`.
-/

@[expose] public section

namespace TonhauserEtAl2013.Examples

def ex_1a : Datum :=
  { id := "tonhauseretal2013_1a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The present queen of France lives in Ithaca."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "atomic"), ("trigger", "definite"), ("content", "existence of a unique queen of France")] }

def ex_1b : Datum :=
  { id := "tonhauseretal2013_1b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It is not the case that the present queen of France lives in Ithaca."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "negation"), ("trigger", "definite"), ("content", "existence of a unique queen of France")] }

def ex_1c : Datum :=
  { id := "tonhauseretal2013_1c"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(1c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Does the present queen of France live in Ithaca?"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "question"), ("trigger", "definite"), ("content", "existence of a unique queen of France")] }

def ex_1d : Datum :=
  { id := "tonhauseretal2013_1d"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(1d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If the present queen of France lives in Ithaca, she has probably met Nelly."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "conditional antecedent"), ("trigger", "definite"), ("content", "existence of a unique queen of France")] }

def ex_13 : Datum :=
  { id := "tonhauseretal2013_13"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(13)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Pe aña memby Márko ko'ãga oipota amba'apo iñhermáno karniseríape."
    glossedTokens := []
    context := "Julia and Maria work in a bakery; their boss Marko is strict but fair. He calls Julia into his office; when she emerges she says this to Maria."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "expressive"), ("content", "negative evaluation"), ("context", "m-neutral"), ("diagnostic", "strong contextual felicity"), ("scf", "no")] }

def ex_14a : Datum :=
  { id := "tonhauseretal2013_14a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(14a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Simon, chekichihakue, oñe'ẽ Aleman."
    glossedTokens := []
    context := "Raul is new in town. His neighbour Simon invites him to a party and introduces him to Maria; when Simon has walked away, Maria tells Raul."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "appositive"), ("content", "descriptive content"), ("context", "m-neutral"), ("diagnostic", "strong contextual felicity"), ("scf", "no")] }

def ex_14b : Datum :=
  { id := "tonhauseretal2013_14b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(14b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Papa Benedícto 16, onasẽva'ekue Alemániape, oiko Rómape."
    glossedTokens := []
    context := "The children in a history class give presentations about famous people; Malena has to talk about the pope and starts with this."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "NRRC"), ("content", "descriptive content"), ("context", "m-neutral"), ("diagnostic", "strong contextual felicity"), ("scf", "no")] }

def ex_15a : Datum :=
  { id := "tonhauseretal2013_15a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(15a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Maléna hasy ra'e. Aimete ogue'ẽ."
    glossedTokens := []
    context := "A mother goes upstairs to check on her daughter, who did not come down for dinner, and reports to her husband."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "aimete 'almost'"), ("content", "polar implication"), ("context", "m-neutral"), ("diagnostic", "strong contextual felicity"), ("scf", "no")] }

def ex_15b : Datum :=
  { id := "tonhauseretal2013_15b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(15b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Chénte amopotĩ ñanderóga!"
    glossedTokens := []
    context := "Carla, a mother of three teenage daughters, has been in hospital for a week when her daughters visit for the first time; asked how they are doing, the youngest blurts this out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "-nte 'only'"), ("content", "prejacent"), ("context", "m-neutral"), ("diagnostic", "strong contextual felicity"), ("scf", "no")] }

def ex_16a : Datum :=
  { id := "tonhauseretal2013_16a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(16a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Pe kuimba'e nderu."
    glossedTokens := []
    context := "You and Maria walk across a meadow and both see something lying in the grass that neither can identify; with better vision, you recognize it as you approach and tell Maria."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "descriptive content"), ("context", "m-neutral, n-positive"), ("diagnostic", "strong contextual felicity"), ("scf", "no")] }

def ex_16b : Datum :=
  { id := "tonhauseretal2013_16b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(16b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ha'e peteĩ kuimba'e."
    glossedTokens := []
    context := "As for (16a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "ha'e '3rd'"), ("content", "human referent"), ("context", "m-neutral, n-positive"), ("diagnostic", "strong contextual felicity"), ("scf", "no")] }

def ex_17a : Datum :=
  { id := "tonhauseretal2013_17a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(17a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ñandechofeur okaru empanáda avei."
    glossedTokens := []
    context := "Malena is eating a hamburger on the bus into town; a woman she does not know sits down next to her and says this."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "avei 'too'"), ("content", "existence of an alternative"), ("context", "m-neutral"), ("diagnostic", "strong contextual felicity"), ("scf", "yes")] }

def ex_22a : Datum :=
  { id := "tonhauseretal2013_22a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(22a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ko mburuvicha Fransiagua oiko Lóndrepe."
    glossedTokens := []
    context := "Out of context."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "indication"), ("context", "m-neutral"), ("diagnostic", "projection")] }

def ex_30a : Datum :=
  { id := "tonhauseretal2013_30a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(30a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ñandechofeur okaru empanáda avei."
    glossedTokens := []
    context := "As for (17a): Malena is eating a hamburger."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "atomic"), ("trigger", "avei 'too'"), ("content", "existence of an alternative"), ("context", "m-neutral"), ("diagnostic", "projection"), ("projective", "yes")] }

def ex_30b : Datum :=
  { id := "tonhauseretal2013_30b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(30b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ikatu okaru empanáda avei ñandechofeur."
    glossedTokens := []
    context := "As for (30a)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "epistemic modal"), ("trigger", "avei 'too'"), ("content", "existence of an alternative"), ("context", "m-neutral"), ("diagnostic", "projection"), ("projective", "yes")] }

def ex_30c : Datum :=
  { id := "tonhauseretal2013_30c"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(30c)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Okarúramo empanáda avei ñandechofeur, asẽta kolektívogui."
    glossedTokens := []
    context := "As for (30a)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "conditional antecedent"), ("trigger", "avei 'too'"), ("content", "existence of an alternative"), ("context", "m-neutral"), ("diagnostic", "projection"), ("projective", "yes")] }

def ex_30d : Datum :=
  { id := "tonhauseretal2013_30d"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(30d)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Okarúpa empanada avei ñandechofeur?"
    glossedTokens := []
    context := "As for (30a)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "question"), ("trigger", "avei 'too'"), ("content", "existence of an alternative"), ("context", "m-neutral"), ("diagnostic", "projection"), ("projective", "yes")] }

def ex_38a : Datum :=
  { id := "tonhauseretal2013_38a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane believes that Bill has stopped smoking (although he's actually never been a smoker)."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "stop"), ("content", "prestate"), ("diagnostic", "obligatory local effect"), ("localEffect", "yes")] }

def ex_38b : Datum :=
  { id := "tonhauseretal2013_38b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Joan believes that her chip, which she had installed last month, has a twelve year guarantee."
    glossedTokens := []
    context := "Joan is hallucinating that Silicon Valley geniuses have installed a brain chip in her left temporal lobe that lets her speak languages she has never studied."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "NRRC"), ("content", "descriptive content"), ("diagnostic", "obligatory local effect"), ("localEffect", "yes")] }

def ex_39a : Datum :=
  { id := "tonhauseretal2013_39a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(39a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane believes that Bill has stopped smoking and that he has never been a smoker."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "stop"), ("content", "prestate"), ("diagnostic", "obligatory local effect"), ("ole", "yes")] }

def ex_39b : Datum :=
  { id := "tonhauseretal2013_39b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(39b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane believes that Bill, who is Sue's cousin, is Sue's brother."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "NRRC"), ("content", "descriptive content"), ("diagnostic", "obligatory local effect"), ("ole", "no")] }

def ex_46a : Datum :=
  { id := "tonhauseretal2013_46a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(46a)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Raul ova Buénos Áirespe, hákatu Juan ndoikuáai. Ha'e oimo'ã Maléna avei ovaha Buénos Áirespe."
    glossedTokens := []
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "avei 'too'"), ("content", "existence of an alternative"), ("context", "globally m-positive, locally m-neutral"), ("diagnostic", "obligatory local effect"), ("ole", "yes")] }

def ex_46b : Datum :=
  { id := "tonhauseretal2013_46b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(46b)"⟩
    reportedIn := none
    language := "para1311"
    primaryText := "Ema'ẽmi! Upépe oĩ peteĩ kuimba'e. Maléna ndohecháni. Ha'e oimo'ã ha'e hasyha."
    glossedTokens := []
    context := "The speaker, Ricardo and Malena are lost in an unfamiliar city; the speaker, a bit ahead of Malena with Ricardo, says this."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "ha'e '3rd'"), ("content", "existence of referent"), ("context", "globally m-positive, locally m-neutral"), ("diagnostic", "obligatory local effect"), ("ole", "yes")] }

def ex_54a : Datum :=
  { id := "tonhauseretal2013_54a"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(54a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Wilma likes that car."
    glossedTokens := []
    context := "Barney and Fred walk down the street without having discussed cars; Barney does not point to or otherwise indicate any of the parked cars."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "indication"), ("context", "m-neutral"), ("diagnostic", "strong contextual felicity"), ("scf", "yes")] }

def ex_54b : Datum :=
  { id := "tonhauseretal2013_54b"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(54b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Wilma likes that car, she has good taste."
    glossedTokens := []
    context := "As for (54a)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("environment", "conditional antecedent"), ("trigger", "demonstrative NP"), ("content", "indication"), ("context", "m-neutral"), ("diagnostic", "projection"), ("projective", "yes")] }

def ex_54c : Datum :=
  { id := "tonhauseretal2013_54c"
    source := ⟨"tonhauser-beaver-roberts-simons-2013", "(54c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Pebbles thinks Wilma likes that car, but of course Pebbles has no idea that I'm pointing to it."
    glossedTokens := []
    context := "Barney points at a car and says this."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("trigger", "demonstrative NP"), ("content", "indication"), ("context", "globally m-positive, locally m-neutral"), ("diagnostic", "obligatory local effect"), ("ole", "no")] }

def all : List Datum := [ex_1a, ex_1b, ex_1c, ex_1d, ex_13, ex_14a, ex_14b, ex_15a, ex_15b, ex_16a, ex_16b, ex_17a, ex_22a, ex_30a, ex_30b, ex_30c, ex_30d, ex_38a, ex_38b, ex_39a, ex_39b, ex_46a, ex_46b, ex_54a, ex_54b, ex_54c]

end TonhauserEtAl2013.Examples
