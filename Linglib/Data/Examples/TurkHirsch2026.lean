import Linglib.Data.Examples.Schema

/-!
# `TurkHirsch2026` — typed example data

Auto-generated from `Linglib/Data/Examples/TurkHirsch2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace TurkHirsch2026.Examples`.
-/

namespace TurkHirsch2026.Examples

open Data.Examples

def polar_yes : LinguisticExample :=
  { id := "turkhirsch2026_polar_yes"
    source := ⟨"turk-hirsch-2026", "mI polar question with particle answer evet"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ali uyuyor mu? — Evet."
    discourseSegments := ["Ali uyuyor mu?", "Evet."]
    glossedTokens := []
    translation := "Does Ali sleep? — Yes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("question_type", "polar"), ("answer_type", "particle")]
    comment := "Migrated from Phenomena/Questions/PolarAnswers.lean turkishPolar_yes. The particle answer 'Evet' (yes) is a felicitous exhaustive answer to the Turkish polar question formed with the particle mI."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def polar_no : LinguisticExample :=
  { id := "turkhirsch2026_polar_no"
    source := ⟨"turk-hirsch-2026", "mI polar question with particle answer hayır"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ali uyuyor mu? — Hayır."
    discourseSegments := ["Ali uyuyor mu?", "Hayır."]
    glossedTokens := []
    translation := "Does Ali sleep? — No."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("question_type", "polar"), ("answer_type", "particle")]
    comment := "Migrated from Phenomena/Questions/PolarAnswers.lean turkishPolar_no. The particle answer 'Hayır' (no) is a felicitous exhaustive answer to the Turkish polar question formed with the particle mI."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def polar_must : LinguisticExample :=
  { id := "turkhirsch2026_polar_must"
    source := ⟨"turk-hirsch-2026", "deontic modal answer to a mI polar question"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ali uyuyor mu? — Ali uyumalı."
    discourseSegments := ["Ali uyuyor mu?", "Ali uyumalı."]
    glossedTokens := []
    translation := "Does Ali sleep? — Ali must sleep."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("question_type", "polar"), ("answer_type", "modal")]
    comment := "Migrated from Phenomena/Questions/PolarAnswers.lean turkishPolar_must. The deontic modal answer 'Ali uyumalı' (Ali must sleep) does not address the polar question and is infelicitous. Per the prior Lean file's commentary: this is unexpected under Rooth-style type-theoretic alternative computation, where the modalized proposition has the same type as the prejacent and should be an alternative; [fox-katzir-2011]-style category match explains the gap — mI is a particle (PART) while modals are auxiliaries (AUX), so category match excludes the modal answer from the alternative set."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [polar_yes, polar_no, polar_must]

end TurkHirsch2026.Examples
