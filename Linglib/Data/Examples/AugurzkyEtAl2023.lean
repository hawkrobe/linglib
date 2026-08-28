import Linglib.Data.Examples.Schema

/-!
# `AugurzkyEtAl2023` — typed example data

Auto-generated from `Linglib/Data/Examples/AugurzkyEtAl2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AugurzkyEtAl2023.Examples`.
-/

namespace AugurzkyEtAl2023.Examples

open Data.Examples

def exp1_every_exi : LinguisticExample :=
  { id := "augurzkyetal2023_exp1_every_exi"
    source := ⟨"augurzky-etal-2023", "Exp. 1, (14), EXISTENTIAL, mixed"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every boy opened his presents."
    discourseSegments := []
    glossedTokens := [("Every", "every"), ("boy", "boy"), ("opened", "open.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := "Every boy opened his presents."
    context := "The boys were told to wait for their grandparents before opening any presents; two of the four boys opened all nine of their presents and two opened some but not all."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "every"), ("experiment", "1"), ("condition", "GAP"), ("qud", "existential"), ("rating", "high")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_every_uni : LinguisticExample :=
  { id := "augurzkyetal2023_exp1_every_uni"
    source := ⟨"augurzky-etal-2023", "Exp. 1, (14), UNIVERSAL, mixed"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every boy opened his presents."
    discourseSegments := []
    glossedTokens := [("Every", "every"), ("boy", "boy"), ("opened", "open.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := "Every boy opened his presents."
    context := "The boys were told to open all their presents before the neighbours arrived; two of the four boys opened all nine of their presents and two opened some but not all."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "every"), ("experiment", "1"), ("condition", "GAP"), ("qud", "universal"), ("rating", "low")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_no_exi : LinguisticExample :=
  { id := "augurzkyetal2023_exp1_no_exi"
    source := ⟨"augurzky-etal-2023", "Exp. 1, (15), EXISTENTIAL, mixed"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No boy opened his presents."
    discourseSegments := []
    glossedTokens := [("No", "no"), ("boy", "boy"), ("opened", "open.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := "No boy opened his presents."
    context := "The boys were told to wait for their grandparents before opening any presents; two of the four boys opened none of their presents and two opened some but not all."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "no"), ("experiment", "1"), ("condition", "GAP"), ("qud", "existential"), ("rating", "low")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_no_uni : LinguisticExample :=
  { id := "augurzkyetal2023_exp1_no_uni"
    source := ⟨"augurzky-etal-2023", "Exp. 1, (15), UNIVERSAL, mixed"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "No boy opened his presents."
    discourseSegments := []
    glossedTokens := [("No", "no"), ("boy", "boy"), ("opened", "open.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := "No boy opened his presents."
    context := "The boys were told to open all their presents before the neighbours arrived; two of the four boys opened none of their presents and two opened some but not all."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "no"), ("experiment", "1"), ("condition", "GAP"), ("qud", "universal"), ("rating", "low")]
    comment := "Rated low in both contexts, though higher in the universal one: the context effect is much smaller than for every."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp2_every_exi : LinguisticExample :=
  { id := "augurzkyetal2023_exp2_every_exi"
    source := ⟨"augurzky-etal-2023", "Exp. 2, (14), EXISTENTIAL, mixed"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every boy opened his presents."
    discourseSegments := []
    glossedTokens := [("Every", "every"), ("boy", "boy"), ("opened", "open.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := "Every boy opened his presents."
    context := "The boys were told to wait for their grandparents before opening any presents; the mixed picture shared with the not-every sentences."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "every"), ("experiment", "2"), ("condition", "GAP"), ("qud", "existential"), ("rating", "high")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp2_every_uni : LinguisticExample :=
  { id := "augurzkyetal2023_exp2_every_uni"
    source := ⟨"augurzky-etal-2023", "Exp. 2, (14), UNIVERSAL, mixed"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Every boy opened his presents."
    discourseSegments := []
    glossedTokens := [("Every", "every"), ("boy", "boy"), ("opened", "open.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := "Every boy opened his presents."
    context := "The boys were told to open all their presents before the neighbours arrived; the mixed picture shared with the not-every sentences."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "every"), ("experiment", "2"), ("condition", "GAP"), ("qud", "universal"), ("rating", "low")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp2_notevery_exi : LinguisticExample :=
  { id := "augurzkyetal2023_exp2_notevery_exi"
    source := ⟨"augurzky-etal-2023", "Exp. 2, not every, EXISTENTIAL, mixed"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not every boy opened his presents."
    discourseSegments := []
    glossedTokens := [("Not", "not"), ("every", "every"), ("boy", "boy"), ("opened", "open.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := "Not every boy opened his presents."
    context := "The boys were told to wait for their grandparents before opening any presents; the mixed picture shared with the every sentences."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "notEvery"), ("experiment", "2"), ("condition", "GAP"), ("qud", "existential"), ("rating", "low")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp2_notevery_uni : LinguisticExample :=
  { id := "augurzkyetal2023_exp2_notevery_uni"
    source := ⟨"augurzky-etal-2023", "Exp. 2, not every, UNIVERSAL, mixed"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Not every boy opened his presents."
    discourseSegments := []
    glossedTokens := [("Not", "not"), ("every", "every"), ("boy", "boy"), ("opened", "open.PST"), ("his", "3SG.M.POSS"), ("presents", "present.PL")]
    translation := "Not every boy opened his presents."
    context := "The boys were told to open all their presents before the neighbours arrived; the mixed picture shared with the every sentences."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("operator", "notEvery"), ("experiment", "2"), ("condition", "GAP"), ("qud", "universal"), ("rating", "high")]
    comment := "The context effect is as large as for every."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [exp1_every_exi, exp1_every_uni, exp1_no_exi, exp1_no_uni, exp2_every_exi, exp2_every_uni, exp2_notevery_exi, exp2_notevery_uni]

end AugurzkyEtAl2023.Examples
