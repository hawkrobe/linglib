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
    discourseSegments := []
    glossedTokens := [("un", "a"), ("grupo", "group"), ("de", "of"), ("estudiantes", "students")]
    translation := "a group of students"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo")]
    comment := "Pseudo-partitive binominal." }

def ex1b : LinguisticExample :=
  { id := "saab2026_ex1b"
    source := ⟨"saab-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "un montón de estudiantes"
    discourseSegments := []
    glossedTokens := [("un", "a"), ("montón", "lot"), ("de", "of"), ("estudiantes", "students")]
    translation := "a lot of students"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón")]
    comment := "Quantificational binominal." }

def ex1c : LinguisticExample :=
  { id := "saab2026_ex1c"
    source := ⟨"saab-2026", "(1c)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "una mierda de departamento"
    discourseSegments := []
    glossedTokens := [("una", "a"), ("mierda", "shit"), ("de", "of"), ("departamento", "apartment")]
    translation := "a shit of an apartment"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda")]
    comment := "Qualitative binominal." }

def ex2a : LinguisticExample :=
  { id := "saab2026_ex2a"
    source := ⟨"saab-2026", "(2a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Vinieron un grupo de estudiantes."
    discourseSegments := []
    glossedTokens := [("Vinieron", "came.3PL"), ("un", "a"), ("grupo", "group.SG"), ("de", "of"), ("estudiantes", "students")]
    translation := "A group of students came."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo"), ("agreement", "plural"), ("codaNumber", "plural")]
    comment := "The verb is plural although the first noun is singular." }

def ex2b : LinguisticExample :=
  { id := "saab2026_ex2b"
    source := ⟨"saab-2026", "(2b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Vinieron un montón de estudiantes."
    discourseSegments := []
    glossedTokens := [("Vinieron", "came.3PL"), ("un", "a"), ("montón", "lot"), ("de", "of"), ("estudiantes", "students")]
    translation := "Lot of students came."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("agreement", "plural"), ("codaNumber", "plural")]
    comment := "The verb is plural although the first noun is singular." }

def ex2c : LinguisticExample :=
  { id := "saab2026_ex2c"
    source := ⟨"saab-2026", "(2c)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Se derrumbaron una mierda de departamentos."
    discourseSegments := []
    glossedTokens := [("Se", "se"), ("derrumbaron", "demolish.3PL"), ("una", "a"), ("mierda", "shit.SG"), ("de", "of"), ("departamentos", "apartments")]
    translation := "Some shitty apartments were demolished."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda"), ("agreement", "plural"), ("codaNumber", "plural")]
    comment := "The verb is plural although the expressive noun is singular." }

def ex5_bocha : LinguisticExample :=
  { id := "saab2026_ex5_bocha"
    source := ⟨"saab-2026", "(5)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Vinieron muchos estudiantes? B: Una bocha."
    discourseSegments := ["A: Vinieron muchos estudiantes?", "B: Una bocha."]
    glossedTokens := []
    translation := "A: Did many students come? — B: A lot/group."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "bocha"), ("elided", "coda")]
    comment := "The genitive coda de estudiantes is elided after the quantificational noun. The paper prints Una bocha / un grupo < de estudiantes > in one example." }

def ex5_grupo : LinguisticExample :=
  { id := "saab2026_ex5_grupo"
    source := ⟨"saab-2026", "(5)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Vinieron muchos estudiantes? B: Un grupo."
    discourseSegments := ["A: Vinieron muchos estudiantes?", "B: Un grupo."]
    glossedTokens := []
    translation := "A: Did many students come? — B: A lot/group."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo"), ("elided", "coda")]
    comment := "The genitive coda de estudiantes is elided after the pseudo-partitive noun. The paper prints Una bocha / un grupo < de estudiantes > in one example." }

def ex6 : LinguisticExample :=
  { id := "saab2026_ex6"
    source := ⟨"saab-2026", "(6)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "una mierda de departamento en San Telmo y una mierda en La Boca"
    discourseSegments := []
    glossedTokens := [("una", "a"), ("mierda", "shit"), ("de", "of"), ("departamento", "apartment"), ("en", "in"), ("San Telmo", "San Telmo"), ("y", "and"), ("una", "a"), ("mierda", "shit"), ("en", "in"), ("La Boca", "La Boca")]
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("ellipsis", .unacceptable)]
    paperFeatures := [("noun", "mierda"), ("elided", "coda")]
    comment := "The second conjunct cannot mean a shit of an apartment in La Boca; only a shitty thing in La Boca. Repeated as (46). The paper gives no translation, only 'Impossible interpretation: 'a shit of an apartment in San Telmo and a shit (of apartment) in La Boca''." }

def ex43 : LinguisticExample :=
  { id := "saab2026_ex43"
    source := ⟨"saab-2026", "(43)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Hay muchos estudiantes de física? B: No, pero de química hay una bocha."
    discourseSegments := ["A: Hay muchos estudiantes de física?", "B: No, pero de química hay una bocha."]
    glossedTokens := []
    translation := "Are there many students of physics? — No, but there are a lot of chemistry."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "bocha"), ("elided", "coda"), ("diagnostic", "subextraction")]
    comment := "The complement de química is sub-extracted from the ellipsis site. The paper underlines the sub-extracted de química." }

def ex45 : LinguisticExample :=
  { id := "saab2026_ex45"
    source := ⟨"saab-2026", "(45)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Hubo un montón de envíos de libros a Ecuador. B: A COLOMBIA, hubo un montón."
    discourseSegments := ["A: Hubo un montón de envíos de libros a Ecuador.", "B: A COLOMBIA, hubo un montón."]
    glossedTokens := []
    translation := "A: There were a lot of book shipments to Ecuador. — B: TO COLOMBIA, there were a lot."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("elided", "coda"), ("diagnostic", "subextraction")]
    comment := "The focused locative with its preposition is sub-extracted from the ellipsis site." }

def ex52a : LinguisticExample :=
  { id := "saab2026_ex52a"
    source := ⟨"saab-2026", "(52a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "un profesor de química y una mierda de física"
    discourseSegments := []
    glossedTokens := [("un", "a"), ("profesor", "professor"), ("de", "of"), ("química", "chemistry"), ("y", "and"), ("una", "a"), ("mierda", "shit"), ("de", "of"), ("física", "physics")]
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda"), ("elided", "coda"), ("diagnostic", "argumentStructure")]
    comment := "The complement de física has no noun to attach to: neither ellipsis nor an indexical empty noun. The paper gives no translation." }

def ex52b : LinguisticExample :=
  { id := "saab2026_ex52b"
    source := ⟨"saab-2026", "(52b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "una mierda de profesor de química y una mierda de física"
    discourseSegments := []
    glossedTokens := [("una", "a"), ("mierda", "shit"), ("de", "of"), ("profesor", "professor"), ("de", "of"), ("química", "chemistry"), ("y", "and"), ("una", "a"), ("mierda", "shit"), ("de", "of"), ("física", "physics")]
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda"), ("elided", "coda"), ("diagnostic", "argumentStructure")]
    comment := "Same with a genitive antecedent. The paper gives no translation." }

def ex53a : LinguisticExample :=
  { id := "saab2026_ex53a"
    source := ⟨"saab-2026", "(53a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "algunos profesores de química y un montón de física"
    discourseSegments := []
    glossedTokens := [("algunos", "some"), ("profesores", "professors"), ("de", "of"), ("química", "chemistry"), ("y", "and"), ("un", "a"), ("montón", "lot"), ("de", "of"), ("física", "physics")]
    translation := "some professors of chemistry and a lot (of professors) of physics"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("elided", "coda"), ("diagnostic", "argumentStructure")]
    comment := "The elided coda de profesores still hosts the complement de física." }

def ex53b : LinguisticExample :=
  { id := "saab2026_ex53b"
    source := ⟨"saab-2026", "(53b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "un montón de profesores de química y un montón de física"
    discourseSegments := []
    glossedTokens := [("un", "a"), ("montón", "lot"), ("de", "of"), ("profesores", "professors"), ("de", "of"), ("química", "chemistry"), ("y", "and"), ("un", "a"), ("montón", "lot"), ("de", "of"), ("física", "physics")]
    translation := "a lot of professors of chemistry and a lot (of professors) of physics"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("elided", "coda"), ("diagnostic", "argumentStructure")]
    comment := "Same with a genitive antecedent." }

def ex54 : LinguisticExample :=
  { id := "saab2026_ex54"
    source := ⟨"saab-2026", "(54)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Contrataron a algún profesor? B: Sí, a una mierda."
    discourseSegments := ["A: Contrataron a algún profesor?", "B: Sí, a una mierda."]
    glossedTokens := []
    translation := "A: Did they hire some professor? — B: Yes, a shit (of a professor)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("ellipsis", .unacceptable)]
    paperFeatures := [("noun", "mierda"), ("elided", "coda")]
    comment := "Fine with the indexical empty noun, not as ellipsis of de profesor. The paper prints B: *Sí, a una mierda < de profesor >, starred on the ellipsis reading and '[ok under an indexical empty noun reading]'." }

def ex48 : LinguisticExample :=
  { id := "saab2026_ex48"
    source := ⟨"saab-2026", "(48)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Qué mierda!"
    discourseSegments := []
    glossedTokens := [("Qué", "what"), ("mierda", "shit.F.SG")]
    translation := "What a shit!"
    context := "Said after watching a bad movie."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "mierda"), ("diagnostic", "contextResolved")]
    comment := "The hearer resolves the expressive to the movie without any linguistic antecedent." }

def ex62a : LinguisticExample :=
  { id := "saab2026_ex62a"
    source := ⟨"saab-2026", "(62a)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Un grupo de senadores votó a favor de la ley, pero uno de diputados votó en contra."
    discourseSegments := []
    glossedTokens := [("Un", "a"), ("grupo", "group"), ("de", "of"), ("senadores", "senators"), ("votó", "voted.3SG"), ("a", "to"), ("favor", "favor"), ("de", "of"), ("la", "the"), ("ley", "law"), ("pero", "but"), ("uno", "a"), ("de", "of"), ("diputados", "delegates"), ("votó", "voted.3SG"), ("en", "in"), ("contra", "against")]
    translation := "One group of senators voted in favor of the law and one of delegates voted against."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo"), ("reading", "descriptive"), ("elided", "first"), ("agreement", "singular"), ("codaNumber", "plural")]
    comment := "Under singular agreement the group reading is salient and grupo itself is elided. The paper prints the elided noun, uno <grupo> de diputados, and one translation for (62)." }

def ex62b : LinguisticExample :=
  { id := "saab2026_ex62b"
    source := ⟨"saab-2026", "(62b)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "Un grupo de senadores votaron a favor de la ley, pero uno de diputados votaron en contra."
    discourseSegments := []
    glossedTokens := [("Un", "a"), ("grupo", "group"), ("de", "of"), ("senadores", "senators"), ("votaron", "voted.3PL"), ("a", "to"), ("favor", "favor"), ("de", "of"), ("la", "the"), ("ley", "law"), ("pero", "but"), ("uno", "a"), ("de", "of"), ("diputados", "delegates"), ("votaron", "voted.3PL"), ("en", "in"), ("contra", "against")]
    translation := ""
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "grupo"), ("reading", "quantificational"), ("elided", "first"), ("agreement", "plural"), ("codaNumber", "plural")]
    comment := "Under plural agreement grupo cannot be elided. The paper prints the elided noun, uno <grupo> de diputados; its one translation, after (62b), goes with (62a)." }

def ex63 : LinguisticExample :=
  { id := "saab2026_ex63"
    source := ⟨"saab-2026", "(63)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Se me cayó un montón de libros. B: Y, a mí, se me cayó uno de revistas."
    discourseSegments := ["A: Se me cayó un montón de libros.", "B: Y, a mí, se me cayó uno de revistas."]
    glossedTokens := []
    translation := "I dropped a bunch of books. — And I dropped one (bunch) of magazines."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("reading", "descriptive"), ("elided", "first"), ("agreement", "singular"), ("codaNumber", "plural")]
    comment := "Descriptive reading with singular agreement: montón is elided. The paper prints the elided noun, uno <montón> de revistas." }

def ex64 : LinguisticExample :=
  { id := "saab2026_ex64"
    source := ⟨"saab-2026", "(64)"⟩
    reportedIn := none
    language := "stan1288"
    primaryText := "A: Se me cayeron un montón de libros. B: Y, a mí, se me cayeron uno de revistas."
    discourseSegments := ["A: Se me cayeron un montón de libros.", "B: Y, a mí, se me cayeron uno de revistas."]
    glossedTokens := []
    translation := "I dropped lot of books. — And I dropped lot of magazines."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("noun", "montón"), ("reading", "quantificational"), ("elided", "first"), ("agreement", "plural"), ("codaNumber", "plural")]
    comment := "Quantificational reading with plural agreement: montón cannot be elided. The paper prints the elided noun, uno <montón> de revistas, and stars B." }

def all : List LinguisticExample := [ex1a, ex1b, ex1c, ex2a, ex2b, ex2c, ex5_bocha, ex5_grupo, ex6, ex43, ex45, ex52a, ex52b, ex53a, ex53b, ex54, ex48, ex62a, ex62b, ex63, ex64]

end Saab2026.Examples
