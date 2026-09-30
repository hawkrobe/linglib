module

public import Linglib.Data.Examples.Schema

/-!
# `YuAusensiSmith2023` — typed example data

Auto-generated from `Linglib/Data/Examples/YuAusensiSmith2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace YuAusensiSmith2023.Examples`.
-/

@[expose] public section

namespace YuAusensiSmith2023.Examples

def ex_23 : Datum :=
  { id := "yuausensismith2023_23"
    source := ⟨"yu-ausensi-smith-2023", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John opened the door again."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("restitutive", .acceptable), ("repetitive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "property concept")] }

def ex_24a : Datum :=
  { id := "yuausensismith2023_24a"
    source := ⟨"yu-ausensi-smith-2023", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sharpened the knife again."
    glossedTokens := []
    context := "John buys a knife that was forged in such a way that it was already sharp. John uses it until it becomes blunt. He uses a whetting stone to make it sharp once more."
    judgment := .acceptable
    alternatives := []
    readings := [("restitutive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "property concept")] }

def ex_25a : Datum :=
  { id := "yuausensismith2023_25a"
    source := ⟨"yu-ausensi-smith-2023", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John broke the plate again."
    glossedTokens := []
    context := "Mary requested a potter to make a plate in separate pieces so she can practice her pottery-mending skills. She took a day to put the pieces together. John snatched the mended plate and broke it."
    judgment := .unacceptable
    alternatives := []
    readings := [("restitutive", .unacceptable), ("repetitive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "change of state")] }

def ex_25b : Datum :=
  { id := "yuausensismith2023_25b"
    source := ⟨"yu-ausensi-smith-2023", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leah thawed the meat again."
    glossedTokens := []
    context := "Leah kills a rabbit, takes it home and skins and butchers it and then puts the fresh meat in the freezer for three days. She then takes it out and puts it on the table to thaw."
    judgment := .unacceptable
    alternatives := []
    readings := [("restitutive", .unacceptable), ("repetitive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "change of state")] }

def ex_25c : Datum :=
  { id := "yuausensismith2023_25c"
    source := ⟨"yu-ausensi-smith-2023", "(25c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim melted the ice cream again."
    glossedTokens := []
    context := "An ice cream factory manufactures ice cream from a package of ingredients by adding water and then freezing the result. After adding the contents of the package to water and freezing it, Kim lets it melt into a liquid state."
    judgment := .unacceptable
    alternatives := []
    readings := [("restitutive", .unacceptable), ("repetitive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "change of state")] }

def ex_26 : Datum :=
  { id := "yuausensismith2023_26"
    source := ⟨"yu-ausensi-smith-2023", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan opened the door for two hours."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("durative", .acceptable), ("internal", .acceptable)]
    paperFeatures := [("diagnostic", "for-phrase"), ("root class", "property concept")] }

def ex_27 : Datum :=
  { id := "yuausensismith2023_27"
    source := ⟨"yu-ausensi-smith-2023", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan broke the vase for 5 minutes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("durative", .acceptable), ("internal", .unacceptable)]
    paperFeatures := [("diagnostic", "for-phrase"), ("root class", "change of state")] }

def ex_28 : Datum :=
  { id := "yuausensismith2023_28"
    source := ⟨"yu-ausensi-smith-2023", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jill thawed the meat for 30 minutes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("durative", .acceptable), ("internal", .unacceptable)]
    paperFeatures := [("diagnostic", "for-phrase"), ("root class", "change of state")] }

def ex_29 : Datum :=
  { id := "yuausensismith2023_29"
    source := ⟨"yu-ausensi-smith-2023", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Johannes melted the cheese for 10 minutes."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("durative", .acceptable), ("internal", .unacceptable)]
    paperFeatures := [("diagnostic", "for-phrase"), ("root class", "change of state")] }

def ex_30 : Datum :=
  { id := "yuausensismith2023_30"
    source := ⟨"yu-ausensi-smith-2023", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim opened the door into the garden."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")] }

def ex_31a : Datum :=
  { id := "yuausensismith2023_31a"
    source := ⟨"yu-ausensi-smith-2023", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The citizens darkened the city invisible."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")] }

def ex_31b : Datum :=
  { id := "yuausensismith2023_31b"
    source := ⟨"yu-ausensi-smith-2023", "(31b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The dentist whitened his teeth clean."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")] }

def ex_35b : Datum :=
  { id := "yuausensismith2023_35b"
    source := ⟨"yu-ausensi-smith-2023", "(35b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A couple of monks broke the corpse loose from the deck."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state")] }

def ex_35c : Datum :=
  { id := "yuausensismith2023_35c"
    source := ⟨"yu-ausensi-smith-2023", "(35c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Scientists just melted a hole through 3,500 feet of ice."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state")] }

def all : List Datum := [ex_23, ex_24a, ex_25a, ex_25b, ex_25c, ex_26, ex_27, ex_28, ex_29, ex_30, ex_31a, ex_31b, ex_35b, ex_35c]

end YuAusensiSmith2023.Examples
