import Linglib.Data.Examples.Schema

/-!
# `VonFintel1999` — typed example data

Auto-generated from `Linglib/Data/Examples/VonFintel1999.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace VonFintel1999.Examples`.
-/

namespace VonFintel1999.Examples

open Data.Examples

def ex10 : LinguisticExample :=
  { id := "vonfintel1999_ex10"
    source := ⟨"von-fintel-1999", "ex. 10, p. 101"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Only John ever ate any kale for breakfast."
    discourseSegments := []
    glossedTokens := []
    translation := "Only John ever ate any kale for breakfast."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "only John"), ("npi", "ever, any")]
    comment := "The §2 licensing datum: 'only John' licenses NPIs in its immediate scope despite not being classically DE (ex. 11); formalized as ex11_only_not_DE / ex18_only_strawsonDE."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex21 : LinguisticExample :=
  { id := "vonfintel1999_ex21"
    source := ⟨"von-fintel-1999", "ex. 21, p. 107"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's been five years since I saw any bird of prey in this area."
    discourseSegments := []
    glossedTokens := []
    translation := "It's been five years since I saw any bird of prey in this area."
    context := "Iatridou (p.c.) example relayed by von Fintel."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "since"), ("npi", "any")]
    comment := "'since' licenses NPIs in its complement while failing classical DE (ex. 20); formalized as ex22_since_strawsonDE."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex28a : LinguisticExample :=
  { id := "vonfintel1999_ex28a"
    source := ⟨"von-fintel-1999", "ex. 28a, p. 111"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sandy is amazed that Robin ever ate kale."
    discourseSegments := []
    glossedTokens := []
    translation := "Sandy is amazed that Robin ever ate kale."
    context := ""
    judgment := .acceptable
    alternatives := [("Sandy is surprised that Robin ever ate kale.", .acceptable)]
    readings := []
    paperFeatures := [("licenser", "amazed/surprised"), ("npi", "ever")]
    comment := "Adversative attitude licensing datum; complement position is not classically DE (ex. 29)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex28b : LinguisticExample :=
  { id := "vonfintel1999_ex28b"
    source := ⟨"von-fintel-1999", "ex. 28b, p. 111"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sandy is sorry that Robin bought any car."
    discourseSegments := []
    glossedTokens := []
    translation := "Sandy is sorry that Robin bought any car."
    context := ""
    judgment := .acceptable
    alternatives := [("Sandy regrets that Robin bought any car.", .acceptable)]
    readings := []
    paperFeatures := [("licenser", "sorry/regret"), ("npi", "any")]
    comment := "The explanandum for ex28b_sorry_strawsonDE: 'sorry' licenses NPIs despite the complement not being classically DE (ex. 30)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def glad_any : LinguisticExample :=
  { id := "vonfintel1999_glad_any"
    source := ⟨"von-fintel-1999", "§3.3 discussion"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sandy is glad that Robin bought any car."
    discourseSegments := []
    glossedTokens := []
    translation := "Sandy is glad that Robin bought any car."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "glad (non-licenser)"), ("npi", "any")]
    comment := "The sorry/glad asymmetry datum behind ex50_gladKL_isUE / ex52_gladVF_isUE: 'glad' is UE in its complement, so NPIs are not licensed. Settle-for-less rescues are recorded in KadmonLandman1993 / Lahiri1998 (see bridge_lahiri_glad_settle_overgeneration)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex70a : LinguisticExample :=
  { id := "vonfintel1999_ex70a"
    source := ⟨"von-fintel-1999", "ex. 70a, p. 135"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If John subscribes to any newspaper, he is probably well informed."
    discourseSegments := []
    glossedTokens := []
    translation := "If John subscribes to any newspaper, he is probably well informed."
    context := ""
    judgment := .acceptable
    alternatives := [("If he has ever told a lie, he must go to confession.", .acceptable), ("If you had left any later, you would have missed the plane.", .acceptable)]
    readings := []
    paperFeatures := [("licenser", "conditional antecedent"), ("npi", "any, ever")]
    comment := "Ex. 70a-c bundled: conditional antecedents license NPIs; DE status depends on the conditional analysis (restrictor vs Stalnaker-Lewis) — formalized as ex72_conditional_antecedent_DE."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex75 : LinguisticExample :=
  { id := "vonfintel1999_ex75"
    source := ⟨"von-fintel-1999", "ex. 75, p. 138"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Emma is the tallest girl to ever win the dance contest."
    discourseSegments := []
    glossedTokens := []
    translation := "Emma is the tallest girl to ever win the dance contest."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("licenser", "superlative"), ("npi", "ever")]
    comment := "Superlative licensing datum; the restriction position fails classical DE (ex. 76) but is Strawson-DE (ex. 77) — formalized as ex77_superlative_strawsonDE."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex10, ex21, ex28a, ex28b, glad_any, ex70a, ex75]

end VonFintel1999.Examples
