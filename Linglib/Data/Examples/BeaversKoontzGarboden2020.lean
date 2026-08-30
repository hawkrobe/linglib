import Linglib.Data.Examples.Schema

/-!
# `BeaversKoontzGarboden2020` — typed example data

Auto-generated from `Linglib/Data/Examples/BeaversKoontzGarboden2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeaversKoontzGarboden2020.Examples`.
-/

namespace BeaversKoontzGarboden2020.Examples

open Data.Examples

def bkg2020_25a : LinguisticExample :=
  { id := "bkg2020_25a"
    source := ⟨"beavers-koontz-garboden-2020", "(25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary flattened the rug again, and it had been flat before."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary flattened the rug again, and it had been flat before."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("restitutive: again scopes over the root state", .acceptable)]
    paperFeatures := [("diagnostic", "sublexical again"), ("attachment", "root")]
    comment := "Lowest of the three attachment sites in (27)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bkg2020_25b : LinguisticExample :=
  { id := "bkg2020_25b"
    source := ⟨"beavers-koontz-garboden-2020", "(25b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary flattened the rug again, and it had flattened before."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary flattened the rug again, and it had flattened before."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("repetitive over the change: again scopes over v_become", .acceptable)]
    paperFeatures := [("diagnostic", "sublexical again"), ("attachment", "v_become")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bkg2020_25c : LinguisticExample :=
  { id := "bkg2020_25c"
    source := ⟨"beavers-koontz-garboden-2020", "(25c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary flattened the rug again, and Mary had flattened it before."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary flattened the rug again, and Mary had flattened it before."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("repetitive over the causation: again scopes over v_cause", .acceptable)]
    paperFeatures := [("diagnostic", "sublexical again"), ("attachment", "v_cause")]
    comment := "(25c) entails (25b) entails (25a) — the reading hierarchy."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bkg2020_ch2_46a : LinguisticExample :=
  { id := "bkg2020_ch2_46a"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 2 (46a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sharpened the knife again."
    discourseSegments := []
    glossedTokens := []
    translation := "John sharpened the knife again."
    context := "John buys a knife forged already sharp, uses it until it becomes blunt, and sharpens it with a whetting stone."
    judgment := .acceptable
    alternatives := []
    readings := [("restitutive: could be just one sharpening", .acceptable)]
    paperFeatures := [("root class", "property concept"), ("diagnostic", "restitutive again")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bkg2020_ch2_47a : LinguisticExample :=
  { id := "bkg2020_ch2_47a"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 2 (47a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sandy returned the shirt again."
    discourseSegments := []
    glossedTokens := []
    translation := "Sandy returned the shirt again."
    context := "A boutique store makes their shirts in the back. Sandy buys one, decides she does not want it, and exchanges it."
    judgment := .unacceptable
    alternatives := []
    readings := [("repetitive: necessarily two returnings", .acceptable)]
    paperFeatures := [("root class", "result"), ("diagnostic", "restitutive again")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bkg2020_ch2_47b : LinguisticExample :=
  { id := "bkg2020_ch2_47b"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 2 (47b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Leah thawed the meat again."
    discourseSegments := []
    glossedTokens := []
    translation := "Leah thawed the meat again."
    context := "Leah kills a rabbit, butchers it, freezes the fresh meat for three days, then puts it out to thaw."
    judgment := .unacceptable
    alternatives := []
    readings := [("repetitive: necessarily two defrostings", .acceptable)]
    paperFeatures := [("root class", "result"), ("diagnostic", "restitutive again")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bkg2020_ch2_48 : LinguisticExample :=
  { id := "bkg2020_ch2_48"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 2 (48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John fried the fruit again."
    discourseSegments := []
    glossedTokens := []
    translation := "John fried the fruit again."
    context := "John finds a fruit that naturally has brown, fatty edges, trims off the edges, refrigerates it, and later fries it."
    judgment := .unacceptable
    alternatives := []
    readings := [("repetitive: necessarily two fryings", .acceptable)]
    paperFeatures := [("root class", "result"), ("diagnostic", "restitutive again")]
    comment := "Even granting a prototypical fried state, no restitutive reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bkg2020_ch3_10a : LinguisticExample :=
  { id := "bkg2020_ch3_10a"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 3 (10a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary gave John a ring, but he never got it."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary gave John a ring, but he never got it."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("root class", "true possession"), ("diagnostic", "result denial")]
    comment := "Possession is non-cancelable with giving verbs (give, hand, pass)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bkg2020_ch3_11a : LinguisticExample :=
  { id := "bkg2020_ch3_11a"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 3 (11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary sent John a letter, but it got lost in the mail and he never got it."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary sent John a letter, but it got lost in the mail and he never got it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root class", "release"), ("diagnostic", "result denial")]
    comment := "Sending verbs cancel the possession inference: prospective rather than actual having."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bkg2020_ch3_48a : LinguisticExample :=
  { id := "bkg2020_ch3_48a"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 3 (48a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary handed John the book, but it never came to be on his person."
    discourseSegments := []
    glossedTokens := []
    translation := "Mary handed John the book, but it never came to be on his person."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("root class", "transfer of possession by motion"), ("diagnostic", "result denial")]
    comment := "The hand root entails change along a possession-by-motion scale in both templates."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bkg2020_ch4_25a : LinguisticExample :=
  { id := "bkg2020_ch4_25a"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 4 (25a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane just drowned Joe, but nothing is different about him."
    discourseSegments := []
    glossedTokens := []
    translation := "Jane just drowned Joe, but nothing is different about him."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb class", "manner of killing"), ("diagnostic", "result denial")]
    comment := "Manner-of-killing verbs pattern with result verbs: the result is entailed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bkg2020_ch4_26c : LinguisticExample :=
  { id := "bkg2020_ch4_26c"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 4 (26c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "All last night, Shane drowned."
    discourseSegments := []
    glossedTokens := []
    translation := "All last night, Shane drowned."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("verb class", "manner of killing"), ("diagnostic", "object deletion")]
    comment := "On the transitive-killing reading: result verbs disallow object deletion."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bkg2020_ch4_32b : LinguisticExample :=
  { id := "bkg2020_ch4_32b"
    source := ⟨"beavers-koontz-garboden-2020", "ch. 4 (32b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The governor drowned the prisoner, but didn't move a muscle — rather, during the execution she just sat there, tacitly refusing to order a halt!"
    discourseSegments := []
    glossedTokens := []
    translation := "The governor drowned the prisoner, but didn't move a muscle — rather, during the execution she just sat there, tacitly refusing to order a halt!"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb class", "manner of killing"), ("diagnostic", "action denial")]
    comment := "Actor-oriented manner is entailed alongside the result: manner+result in one root."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [bkg2020_25a, bkg2020_25b, bkg2020_25c, bkg2020_ch2_46a, bkg2020_ch2_47a, bkg2020_ch2_47b, bkg2020_ch2_48, bkg2020_ch3_10a, bkg2020_ch3_11a, bkg2020_ch3_48a, bkg2020_ch4_25a, bkg2020_ch4_26c, bkg2020_ch4_32b]

end BeaversKoontzGarboden2020.Examples
