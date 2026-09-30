module

public import Linglib.Data.Examples.Schema

/-!
# `Saab2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Saab2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Saab2026.Examples`.
-/

@[expose] public section

namespace Saab2026.Examples

open Data.Examples

def ex1a : LinguisticExample :=
  { id := "saab2026_ex1a"
    source := ⟨"saab-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "un grupo de estudiantes"
    glossedTokens := [("un", "a"), ("grupo", "group"), ("de", "of"), ("estudiantes", "students")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo")] }

def ex1b : LinguisticExample :=
  { id := "saab2026_ex1b"
    source := ⟨"saab-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "un montón de estudiantes"
    glossedTokens := [("un", "a"), ("montón", "lot"), ("de", "of"), ("estudiantes", "students")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón")] }

def ex1c : LinguisticExample :=
  { id := "saab2026_ex1c"
    source := ⟨"saab-2026", "(1c)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "una mierda de departamento"
    glossedTokens := [("una", "a"), ("mierda", "shit"), ("de", "of"), ("departamento", "apartment")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda")] }

def ex2a : LinguisticExample :=
  { id := "saab2026_ex2a"
    source := ⟨"saab-2026", "(2a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Vinieron un grupo de estudiantes."
    glossedTokens := [("Vinieron", "came.3PL"), ("un", "a"), ("grupo", "group.SG"), ("de", "of"), ("estudiantes", "students")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo"), ("agreement", "plural"), ("codaNumber", "plural")] }

def ex2b : LinguisticExample :=
  { id := "saab2026_ex2b"
    source := ⟨"saab-2026", "(2b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Vinieron un montón de estudiantes."
    glossedTokens := [("Vinieron", "came.3PL"), ("un", "a"), ("montón", "lot"), ("de", "of"), ("estudiantes", "students")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("agreement", "plural"), ("codaNumber", "plural")] }

def ex2c : LinguisticExample :=
  { id := "saab2026_ex2c"
    source := ⟨"saab-2026", "(2c)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Se derrumbaron una mierda de departamentos."
    glossedTokens := [("Se", "se"), ("derrumbaron", "demolish.3PL"), ("una", "a"), ("mierda", "shit.SG"), ("de", "of"), ("departamentos", "apartments")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda"), ("agreement", "plural"), ("codaNumber", "plural")] }

def ex5_bocha : LinguisticExample :=
  { id := "saab2026_ex5_bocha"
    source := ⟨"saab-2026", "(5)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Vinieron muchos estudiantes? B: Una bocha."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "bocha"), ("elided", "coda")] }

def ex5_grupo : LinguisticExample :=
  { id := "saab2026_ex5_grupo"
    source := ⟨"saab-2026", "(5)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Vinieron muchos estudiantes? B: Un grupo."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo"), ("elided", "coda")] }

def ex6 : LinguisticExample :=
  { id := "saab2026_ex6"
    source := ⟨"saab-2026", "(6)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "una mierda de departamento en San Telmo y una mierda en La Boca"
    glossedTokens := [("una", "a"), ("mierda", "shit"), ("de", "of"), ("departamento", "apartment"), ("en", "in"), ("San Telmo", "San Telmo"), ("y", "and"), ("una", "a"), ("mierda", "shit"), ("en", "in"), ("La Boca", "La Boca")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("ellipsis", .unacceptable)]
    paperFeatures := [("noun", "mierda"), ("elided", "coda")] }

def ex43 : LinguisticExample :=
  { id := "saab2026_ex43"
    source := ⟨"saab-2026", "(43)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Hay muchos estudiantes de física? B: No, pero de química hay una bocha."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "bocha"), ("elided", "coda"), ("diagnostic", "subextraction")] }

def ex45 : LinguisticExample :=
  { id := "saab2026_ex45"
    source := ⟨"saab-2026", "(45)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Hubo un montón de envíos de libros a Ecuador. B: A COLOMBIA, hubo un montón."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("elided", "coda"), ("diagnostic", "subextraction")] }

def ex52a : LinguisticExample :=
  { id := "saab2026_ex52a"
    source := ⟨"saab-2026", "(52a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "un profesor de química y una mierda de física"
    glossedTokens := [("un", "a"), ("profesor", "professor"), ("de", "of"), ("química", "chemistry"), ("y", "and"), ("una", "a"), ("mierda", "shit"), ("de", "of"), ("física", "physics")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda"), ("elided", "coda"), ("diagnostic", "argumentStructure")] }

def ex52b : LinguisticExample :=
  { id := "saab2026_ex52b"
    source := ⟨"saab-2026", "(52b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "una mierda de profesor de química y una mierda de física"
    glossedTokens := [("una", "a"), ("mierda", "shit"), ("de", "of"), ("profesor", "professor"), ("de", "of"), ("química", "chemistry"), ("y", "and"), ("una", "a"), ("mierda", "shit"), ("de", "of"), ("física", "physics")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda"), ("elided", "coda"), ("diagnostic", "argumentStructure")] }

def ex53a : LinguisticExample :=
  { id := "saab2026_ex53a"
    source := ⟨"saab-2026", "(53a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "algunos profesores de química y un montón de física"
    glossedTokens := [("algunos", "some"), ("profesores", "professors"), ("de", "of"), ("química", "chemistry"), ("y", "and"), ("un", "a"), ("montón", "lot"), ("de", "of"), ("física", "physics")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("elided", "coda"), ("diagnostic", "argumentStructure")] }

def ex53b : LinguisticExample :=
  { id := "saab2026_ex53b"
    source := ⟨"saab-2026", "(53b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "un montón de profesores de química y un montón de física"
    glossedTokens := [("un", "a"), ("montón", "lot"), ("de", "of"), ("profesores", "professors"), ("de", "of"), ("química", "chemistry"), ("y", "and"), ("un", "a"), ("montón", "lot"), ("de", "of"), ("física", "physics")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("elided", "coda"), ("diagnostic", "argumentStructure")] }

def ex54 : LinguisticExample :=
  { id := "saab2026_ex54"
    source := ⟨"saab-2026", "(54)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Contrataron a algún profesor? B: Sí, a una mierda."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("ellipsis", .unacceptable)]
    paperFeatures := [("noun", "mierda"), ("elided", "coda")] }

def ex48 : LinguisticExample :=
  { id := "saab2026_ex48"
    source := ⟨"saab-2026", "(48)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Qué mierda!"
    glossedTokens := [("Qué", "what"), ("mierda", "shit.F.SG")]
    context := "Said after watching a bad movie."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda"), ("diagnostic", "contextResolved")] }

def ex62a : LinguisticExample :=
  { id := "saab2026_ex62a"
    source := ⟨"saab-2026", "(62a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Un grupo de senadores votó a favor de la ley, pero uno de diputados votó en contra."
    glossedTokens := [("Un", "a"), ("grupo", "group"), ("de", "of"), ("senadores", "senators"), ("votó", "voted.3SG"), ("a", "to"), ("favor", "favor"), ("de", "of"), ("la", "the"), ("ley", "law"), ("pero", "but"), ("uno", "a"), ("de", "of"), ("diputados", "delegates"), ("votó", "voted.3SG"), ("en", "in"), ("contra", "against")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo"), ("reading", "descriptive"), ("elided", "first"), ("agreement", "singular"), ("codaNumber", "plural")] }

def ex62b : LinguisticExample :=
  { id := "saab2026_ex62b"
    source := ⟨"saab-2026", "(62b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Un grupo de senadores votaron a favor de la ley, pero uno de diputados votaron en contra."
    glossedTokens := [("Un", "a"), ("grupo", "group"), ("de", "of"), ("senadores", "senators"), ("votaron", "voted.3PL"), ("a", "to"), ("favor", "favor"), ("de", "of"), ("la", "the"), ("ley", "law"), ("pero", "but"), ("uno", "a"), ("de", "of"), ("diputados", "delegates"), ("votaron", "voted.3PL"), ("en", "in"), ("contra", "against")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo"), ("reading", "quantificational"), ("elided", "first"), ("agreement", "plural"), ("codaNumber", "plural")] }

def ex63 : LinguisticExample :=
  { id := "saab2026_ex63"
    source := ⟨"saab-2026", "(63)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Se me cayó un montón de libros. B: Y, a mí, se me cayó uno de revistas."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("reading", "descriptive"), ("elided", "first"), ("agreement", "singular"), ("codaNumber", "plural")] }

def ex64 : LinguisticExample :=
  { id := "saab2026_ex64"
    source := ⟨"saab-2026", "(64)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Se me cayeron un montón de libros. B: Y, a mí, se me cayeron uno de revistas."
    glossedTokens := []
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("reading", "quantificational"), ("elided", "first"), ("agreement", "plural"), ("codaNumber", "plural")] }

def all : List LinguisticExample := [ex1a, ex1b, ex1c, ex2a, ex2b, ex2c, ex5_bocha, ex5_grupo, ex6, ex43, ex45, ex52a, ex52b, ex53a, ex53b, ex54, ex48, ex62a, ex62b, ex63, ex64]

end Saab2026.Examples
