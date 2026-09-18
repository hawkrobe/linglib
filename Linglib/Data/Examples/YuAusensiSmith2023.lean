import Linglib.Data.Examples.Schema

/-!
# `YuAusensiSmith2023` — typed example data

Auto-generated from `Linglib/Data/Examples/YuAusensiSmith2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace YuAusensiSmith2023.Examples`.
-/

namespace YuAusensiSmith2023.Examples

open Data.Examples

def ex_23 : LinguisticExample :=
  { id := "yuausensismith2023_23"
    source := ⟨"yu-ausensi-smith-2023", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John opened the door again."
    discourseSegments := []
    glossedTokens := []
    translation := "John opened the door again."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("restitutive", .acceptable), ("repetitive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "property concept")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24a : LinguisticExample :=
  { id := "yuausensismith2023_24a"
    source := ⟨"yu-ausensi-smith-2023", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sharpened the knife again."
    discourseSegments := []
    glossedTokens := []
    translation := "John sharpened the knife again."
    context := "John buys a knife that was forged in such a way that it was already sharp. John uses it until it becomes blunt. He uses a whetting stone to make it sharp once more."
    judgment := .acceptable
    alternatives := []
    readings := [("restitutive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "property concept")]
    comment := "One sharpening suffices. The paper attributes the example to Beavers and Koontz-Garboden 2020."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25a : LinguisticExample :=
  { id := "yuausensismith2023_25a"
    source := ⟨"yu-ausensi-smith-2023", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John broke the plate again."
    discourseSegments := []
    glossedTokens := []
    translation := "John broke the plate again."
    context := "Mary requested a potter to make a plate in separate pieces so she can practice her pottery-mending skills. She took a day to put the pieces together. John snatched the mended plate and broke it."
    judgment := .unacceptable
    alternatives := []
    readings := [("restitutive", .unacceptable), ("repetitive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "change of state")]
    comment := "Necessarily two breakings."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25b : LinguisticExample :=
  { id := "yuausensismith2023_25b"
    source := ⟨"yu-ausensi-smith-2023", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leah thawed the meat again."
    discourseSegments := []
    glossedTokens := []
    translation := "Leah thawed the meat again."
    context := "Leah kills a rabbit, takes it home and skins and butchers it and then puts the fresh meat in the freezer for three days. She then takes it out and puts it on the table to thaw."
    judgment := .unacceptable
    alternatives := []
    readings := [("restitutive", .unacceptable), ("repetitive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "change of state")]
    comment := "Necessarily two defrostings."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_25c : LinguisticExample :=
  { id := "yuausensismith2023_25c"
    source := ⟨"yu-ausensi-smith-2023", "(25c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim melted the ice cream again."
    discourseSegments := []
    glossedTokens := []
    translation := "Kim melted the ice cream again."
    context := "An ice cream factory manufactures ice cream from a package of ingredients by adding water and then freezing the result. After adding the contents of the package to water and freezing it, Kim lets it melt into a liquid state."
    judgment := .unacceptable
    alternatives := []
    readings := [("restitutive", .unacceptable), ("repetitive", .acceptable)]
    paperFeatures := [("diagnostic", "again"), ("root class", "change of state")]
    comment := "Necessarily two meltings."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_26 : LinguisticExample :=
  { id := "yuausensismith2023_26"
    source := ⟨"yu-ausensi-smith-2023", "(26)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan opened the door for two hours."
    discourseSegments := []
    glossedTokens := []
    translation := "Susan opened the door for two hours."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("durative", .acceptable), ("internal", .acceptable)]
    paperFeatures := [("diagnostic", "for-phrase"), ("root class", "property concept")]
    comment := "Internal reading: the door remained open for two hours."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_27 : LinguisticExample :=
  { id := "yuausensismith2023_27"
    source := ⟨"yu-ausensi-smith-2023", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Susan broke the vase for 5 minutes."
    discourseSegments := []
    glossedTokens := []
    translation := "Susan broke the vase for 5 minutes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("durative", .acceptable), ("internal", .unacceptable)]
    paperFeatures := [("diagnostic", "for-phrase"), ("root class", "change of state")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_28 : LinguisticExample :=
  { id := "yuausensismith2023_28"
    source := ⟨"yu-ausensi-smith-2023", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jill thawed the meat for 30 minutes."
    discourseSegments := []
    glossedTokens := []
    translation := "Jill thawed the meat for 30 minutes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("durative", .acceptable), ("internal", .unacceptable)]
    paperFeatures := [("diagnostic", "for-phrase"), ("root class", "change of state")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_29 : LinguisticExample :=
  { id := "yuausensismith2023_29"
    source := ⟨"yu-ausensi-smith-2023", "(29)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Johannes melted the cheese for 10 minutes."
    discourseSegments := []
    glossedTokens := []
    translation := "Johannes melted the cheese for 10 minutes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("durative", .acceptable), ("internal", .unacceptable)]
    paperFeatures := [("diagnostic", "for-phrase"), ("root class", "change of state")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_30 : LinguisticExample :=
  { id := "yuausensismith2023_30"
    source := ⟨"yu-ausensi-smith-2023", "(30)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Kim opened the door into the garden."
    discourseSegments := []
    glossedTokens := []
    translation := "Kim opened the door into the garden."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")]
    comment := "Intended: Kim caused the door to go into the garden by opening."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_31a : LinguisticExample :=
  { id := "yuausensismith2023_31a"
    source := ⟨"yu-ausensi-smith-2023", "(31a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The citizens darkened the city invisible."
    discourseSegments := []
    glossedTokens := []
    translation := "The citizens darkened the city invisible."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")]
    comment := "Cannot mean that the citizens caused the city to become invisible by darkening."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_31b : LinguisticExample :=
  { id := "yuausensismith2023_31b"
    source := ⟨"yu-ausensi-smith-2023", "(31b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The dentist whitened his teeth clean."
    discourseSegments := []
    glossedTokens := []
    translation := "The dentist whitened his teeth clean."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "property concept")]
    comment := "Cannot mean that the dentist caused the teeth to become clean by whitening."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_35b : LinguisticExample :=
  { id := "yuausensismith2023_35b"
    source := ⟨"yu-ausensi-smith-2023", "(35b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A couple of monks broke the corpse loose from the deck."
    discourseSegments := []
    glossedTokens := []
    translation := "A couple of monks broke the corpse loose from the deck."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state")]
    comment := "Corpus example with an unselected object: it is the deck, not the corpse, that breaks."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_35c : LinguisticExample :=
  { id := "yuausensismith2023_35c"
    source := ⟨"yu-ausensi-smith-2023", "(35c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Scientists just melted a hole through 3,500 feet of ice."
    discourseSegments := []
    glossedTokens := []
    translation := "Scientists just melted a hole through 3,500 feet of ice."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "resultative modifier"), ("root class", "change of state")]
    comment := "Web example with an unselected object."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_23, ex_24a, ex_25a, ex_25b, ex_25c, ex_26, ex_27, ex_28, ex_29, ex_30, ex_31a, ex_31b, ex_35b, ex_35c]

end YuAusensiSmith2023.Examples
