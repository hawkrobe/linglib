import Linglib.Data.Examples.Schema

/-!
# `Saab2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Saab2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Saab2026.Examples`.
-/

namespace Saab2026.Examples

open Data.Examples

def ex_6a_grupo : LinguisticExample :=
  { id := "saab2026_6a_grupo"
    source := ⟨"saab-2026", "(6a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "un grupo de estudiantes"
    discourseSegments := []
    glossedTokens := [("un", "a"), ("grupo", "group"), ("de", "of"), ("estudiantes", "student.PL")]
    translation := "a group of students"
    context := "Pseudo-partitive binominal: NP-ellipsis of the de-complement is licensed, and the verb agrees with the plural embedded noun."
    judgment := .acceptable
    alternatives := [("un grupo", .acceptable)]
    readings := []
    paperFeatures := [("binominal_type", "pseudo_partitive"), ("npe_grammatical", "true"), ("verb_agreement", "plural")]
    comment := "UNVERIFIED paperLabel: ex. (6a) carried from Phenomena/Ellipsis/NPEllipsis.lean grupoDeEstudiantes ('Saab 2026, (6a)'), not checked against the published paper. The NP-ellipsis form 'un grupo' in alternatives is the Lean ellipsisForm field. Gloss 'group' from Fragments/Spanish/Binominals.lean."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_7a_monton : LinguisticExample :=
  { id := "saab2026_7a_monton"
    source := ⟨"saab-2026", "(7a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "un montón de estudiantes"
    discourseSegments := []
    glossedTokens := [("un", "a"), ("montón", "heap/lot"), ("de", "of"), ("estudiantes", "student.PL")]
    translation := "a lot of students"
    context := "Quantificational binominal: NP-ellipsis of the de-complement is licensed, and the verb agrees with the plural embedded noun."
    judgment := .acceptable
    alternatives := [("un montón", .acceptable)]
    readings := []
    paperFeatures := [("binominal_type", "quantificational"), ("npe_grammatical", "true"), ("verb_agreement", "plural")]
    comment := "UNVERIFIED paperLabel: ex. (7a) carried from Phenomena/Ellipsis/NPEllipsis.lean montonDeEstudiantes ('Saab 2026, (7a)'), not checked against the published paper. The NP-ellipsis form 'un montón' in alternatives is the Lean ellipsisForm field. Gloss 'heap/lot' from Fragments/Spanish/Binominals.lean."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_9_mierda : LinguisticExample :=
  { id := "saab2026_9_mierda"
    source := ⟨"saab-2026", "(9)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "una mierda de departamento"
    discourseSegments := []
    glossedTokens := [("una", "a.F"), ("mierda", "shit"), ("de", "of"), ("departamento", "apartment")]
    translation := "a shit of apartment"
    context := "Qualitative binominal: NP-ellipsis of the de-complement is blocked (with the intended referent reading), and the verb agrees with the singular expressive noun."
    judgment := .acceptable
    alternatives := [("una mierda", .ungrammatical)]
    readings := []
    paperFeatures := [("binominal_type", "qualitative"), ("npe_grammatical", "false"), ("verb_agreement", "singular")]
    comment := "UNVERIFIED paperLabel: ex. (9) carried from Phenomena/Ellipsis/NPEllipsis.lean mierdaDeDepartamento ('Saab 2026, (9)'), not checked against the published paper. The starred NP-ellipsis form '*una mierda' in alternatives is the Lean ellipsisForm field; the file's docstring notes the star holds for the intended referent reading. Gloss 'shit' from Fragments/Spanish/Binominals.lean."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex_6a_grupo, ex_7a_monton, ex_9_mierda]

end Saab2026.Examples
