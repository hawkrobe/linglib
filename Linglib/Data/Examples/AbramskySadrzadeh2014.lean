import Linglib.Data.Examples.Schema

/-!
# `AbramskySadrzadeh2014` — typed example data

Auto-generated from `Linglib/Data/Examples/AbramskySadrzadeh2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AbramskySadrzadeh2014.Examples`.
-/

namespace AbramskySadrzadeh2014.Examples

open Data.Examples

def donkey : LinguisticExample :=
  { id := "abramskysadrzadeh2014_donkey"
    source := ⟨"geach-1962", "donkey sentence"⟩
    reportedIn := some ⟨"abramsky-sadrzadeh-2014", "§1"⟩
    language := "stan1293"
    primaryText := "If a farmer owns a donkey, he beats it."
    discourseSegments := []
    glossedTokens := []
    translation := "If a farmer owns a donkey, he beats it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "donkey anaphora")]
    comment := "Cited as the case where the usual Montague-style translation fails and DRT was first to succeed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def drt_resolved : LinguisticExample :=
  { id := "abramskysadrzadeh2014_drt_resolved"
    source := ⟨"abramsky-sadrzadeh-2014", "§3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John owns a donkey. He beats it."
    discourseSegments := ["John owns a donkey.", "He beats it."]
    glossedTokens := []
    translation := "John owns a donkey. He beats it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("resolution", "full"), ("unification", "v = x, w = y")]
    comment := "The merge of the two DRS is followed by unification of the accessible, agreeing referents."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def drt_partial : LinguisticExample :=
  { id := "abramskysadrzadeh2014_drt_partial"
    source := ⟨"abramsky-sadrzadeh-2014", "§3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John does not own a donkey. He beats it."
    discourseSegments := ["John does not own a donkey.", "He beats it."]
    glossedTokens := []
    translation := "John does not own a donkey. He beats it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("it = the donkey", .unacceptable)]
    paperFeatures := [("resolution", "partial"), ("unification", "v = x")]
    comment := "The donkey referent sits in a negated sub-DRS and is inaccessible to `it`."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex1 : LinguisticExample :=
  { id := "abramskysadrzadeh2014_ex1"
    source := ⟨"abramsky-sadrzadeh-2014", "example 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John sleeps. He snores."
    discourseSegments := ["John sleeps.", "He snores."]
    glossedTokens := []
    translation := "John sleeps. He snores."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cover", "x ↦ z ↤ y"), ("gluing", "{John(z), sleeps(z), snores(z)}")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2 : LinguisticExample :=
  { id := "abramskysadrzadeh2014_ex2"
    source := ⟨"abramsky-sadrzadeh-2014", "example 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John beats his donkey."
    discourseSegments := []
    glossedTokens := []
    translation := "John beats his donkey."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("cover", "x ↦ a, y ↦ b, u ↦ a, v ↦ b"), ("gluing", "{John(a), donkey(b), owns(a, b), beats(a, b)}")]
    comment := "Anaphor and antecedent in one sentence; three local sections for John, the donkey, and owning/beating."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex3 : LinguisticExample :=
  { id := "abramskysadrzadeh2014_ex3"
    source := ⟨"abramsky-sadrzadeh-2014", "example 3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John owns a donkey. It is grey."
    discourseSegments := ["John owns a donkey.", "It is grey."]
    glossedTokens := []
    translation := "John owns a donkey. It is grey."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("it = the donkey", .acceptable), ("it = John", .unacceptable)]
    paperFeatures := [("resolution", "agreement"), ("cover", "x ↦ a, y ↦ b, z ↦ b")]
    comment := "Agreement is encoded by the negative literal ¬Man(y); merging `it` with John violates consistency."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4 : LinguisticExample :=
  { id := "abramskysadrzadeh2014_ex4"
    source := ⟨"abramsky-sadrzadeh-2014", "example 4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John put the cup on the plate. He broke it."
    discourseSegments := ["John put the cup on the plate.", "He broke it."]
    glossedTokens := []
    translation := "John put the cup on the plate. He broke it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("it = the cup", .acceptable), ("it = the plate", .acceptable)]
    paperFeatures := [("resolution", "ambiguous"), ("covers", "v ↦ y; v ↦ z")]
    comment := "Two plausible covers; the paper defers their ranking to the probabilistic setting."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def brother_happy : LinguisticExample :=
  { id := "abramskysadrzadeh2014_brother_happy"
    source := ⟨"abramsky-sadrzadeh-2014", "§5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has a brother. He is happy."
    discourseSegments := ["John has a brother.", "He is happy."]
    glossedTokens := []
    translation := "John has a brother. He is happy."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("he = John", .acceptable), ("he = the brother", .acceptable)]
    paperFeatures := [("resolution", "preferential"), ("preferred", "he = John")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def brother_nice : LinguisticExample :=
  { id := "abramskysadrzadeh2014_brother_nice"
    source := ⟨"abramsky-sadrzadeh-2014", "§5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John has a brother. He is nice."
    discourseSegments := ["John has a brother.", "He is nice."]
    glossedTokens := []
    translation := "John has a brother. He is nice."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("he = John", .acceptable), ("he = the brother", .acceptable)]
    paperFeatures := [("resolution", "preferential"), ("preferred", "he = the brother")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def cd : LinguisticExample :=
  { id := "abramskysadrzadeh2014_cd"
    source := ⟨"abramsky-sadrzadeh-2014", "§5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John put a cd in the computer and copied it."
    discourseSegments := []
    glossedTokens := []
    translation := "John put a cd in the computer and copied it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("resolution", "preferential")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def jim : LinguisticExample :=
  { id := "abramskysadrzadeh2014_jim"
    source := ⟨"abramsky-sadrzadeh-2014", "§5"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John gave a donkey to Jim. James also gave him a dog."
    discourseSegments := ["John gave a donkey to Jim.", "James also gave him a dog."]
    glossedTokens := []
    translation := "John gave a donkey to Jim. James also gave him a dog."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("resolution", "preferential")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bananas : LinguisticExample :=
  { id := "abramskysadrzadeh2014_bananas"
    source := ⟨"abramsky-sadrzadeh-2014", "§5 example"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John gave the bananas to the monkeys. They were ripe. They were cheeky."
    discourseSegments := ["John gave the bananas to the monkeys.", "They were ripe.", "They were cheeky."]
    glossedTokens := []
    translation := "John gave the bananas to the monkeys. They were ripe. They were cheeky."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("ripe bananas, cheeky bananas", .acceptable), ("ripe bananas, cheeky monkeys", .acceptable), ("ripe monkeys, cheeky bananas", .acceptable), ("ripe monkeys, cheeky monkeys", .acceptable)]
    paperFeatures := [("resolution", "preferential"), ("corpus", "British News, 200 million words"), ("selected", "ripe bananas, cheeky monkeys")]
    comment := "Four candidate coverings weighted by adjective–noun pattern frequencies (ripe banana 14, ripe monkey 0, cheeky banana 0, cheeky monkey 10); the covering u ↦ y, v ↦ z has probability 1/2."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [donkey, drt_resolved, drt_partial, ex1, ex2, ex3, ex4, brother_happy, brother_nice, cd, jim, bananas]

end AbramskySadrzadeh2014.Examples
