import Linglib.Data.Examples.Schema

/-!
# `Major2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Major2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Major2024.Examples`.
-/

namespace Major2024.Examples

open Data.Examples

def ex_2 : LinguisticExample :=
  { id := "major2024_2"
    source := ⟨"major-2024", "ex. (2)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-(ni) göshnan-ni et-t-i de-p oyla-y-du."
    discourseSegments := []
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-(ni)", "Tursun-ACC"), ("göshnan-ni", "meatbread-ACC"), ("et-t-i", "make-PST-3"), ("de-p", "say-CNV"), ("oyla-y-du", "think-NONPST-3")]
    translation := "Mahinur thinks that Tursun made meatbread."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "dep-clause"), ("matrixVerb", "oyla- 'think'")]
    comment := "Baseline dep complement. Paper adds the literal translation 'Mahinur thinks (something), saying Tursun made meatbread.' The parenthesized -(ni) marks the optional accusative on the embedded subject."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_38 : LinguisticExample :=
  { id := "major2024_38"
    source := ⟨"major-2024", "ex. (38)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ni ket-t-i de-p warqiri-d-i."
    discourseSegments := []
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ni", "Tursun-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("warqiri-d-i", "scream-PST-3")]
    translation := "Mahinur screamed, saying that Tursun left."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "dep-clause"), ("matrixVerb", "warqira- 'scream'")]
    comment := "The dep clause modifies unergative 'scream' and coerces it into a verb of speech: the matrix clause is simply 'Mahinur screamed', the dep clause adds the communicative content. Bracketing dropped from primaryText."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_39a : LinguisticExample :=
  { id := "major2024_39a"
    source := ⟨"major-2024", "ex. (39a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur birnémi-ler-ni dé-d-i."
    discourseSegments := []
    glossedTokens := [("Mahinur", "Mahinur"), ("birnémi-ler-ni", "one.what-PL-ACC"), ("dé-d-i", "say-PST-3")]
    translation := "Mahinur said something."
    context := ""
    judgment := .acceptable
    alternatives := [("Mahinur dé-d-i.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "de- 'say'")]
    comment := "Paper prints '*(birnémi-ler-ni)': omitting the DP is ungrammatical (expanded into alternatives) — main-verb 'say' obligatorily introduces a DP complement."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_39b : LinguisticExample :=
  { id := "major2024_39b"
    source := ⟨"major-2024", "ex. (39b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur warqiri-di."
    discourseSegments := []
    glossedTokens := [("Mahinur", "Mahinur"), ("warqiri-di", "scream-PST-3")]
    translation := "Mahinur screamed (*something)."
    context := ""
    judgment := .acceptable
    alternatives := [("Mahinur birnémi-ler-ni warqiri-di.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "warqira- 'scream'")]
    comment := "Paper prints '(*birnémi-ler-ni)': adding the DP is ungrammatical (expanded into alternatives) — 'scream' is incompatible with a complement."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_40a : LinguisticExample :=
  { id := "major2024_40a"
    source := ⟨"major-2024", "ex. (40a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ning ket-ken-lik-i-ni dé-d-i."
    discourseSegments := []
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ning", "Tursun-GEN"), ("ket-ken-lik-i-ni", "leave-PTPL-COMP-3POSS-ACC"), ("dé-d-i", "say-PST-3")]
    translation := "Mahinur said that Tursun left."
    context := ""
    judgment := .acceptable
    alternatives := [("Mahinur dé-d-i.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "de- 'say'")]
    comment := "Paper prints '*(Tursun-ning ket-ken-lik-i-ni)': omission is ungrammatical (expanded into alternatives) — 'say' obligatorily takes a (here participial) complement."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_40b : LinguisticExample :=
  { id := "major2024_40b"
    source := ⟨"major-2024", "ex. (40b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur warqiri-di."
    discourseSegments := []
    glossedTokens := [("Mahinur", "Mahinur"), ("warqiri-di", "scream-PST-3")]
    translation := "Mahinur screamed (*that Tursun left)."
    context := ""
    judgment := .acceptable
    alternatives := [("Mahinur Tursun-ning ket-ken-lik-i-ni warqiri-di.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "warqira- 'scream'")]
    comment := "Paper prints '(*Tursun-ning ket-ken-lik-i-ni)': adding the participial clause is ungrammatical (expanded into alternatives) — 'scream' rejects a clausal complement."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_41a : LinguisticExample :=
  { id := "major2024_41a"
    source := ⟨"major-2024", "ex. (41a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur birnémi-ler-ni de-p warqiri-di."
    discourseSegments := []
    glossedTokens := [("Mahinur", "Mahinur"), ("birnémi-ler-ni", "one.what-PL-ACC"), ("de-p", "say-CNV"), ("warqiri-di", "scream-PST-3")]
    translation := "Mahinur screamed, saying *(something)."
    context := ""
    judgment := .acceptable
    alternatives := [("Mahinur de-p warqiri-di.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "subcategorization-persistence"), ("construction", "dep + scream")]
    comment := "Paper prints '*(birnémi-ler-ni)': the subcategorization requirement of de- 'say' persists inside the adjoined dep clause — 'say' obligatorily introduces an internal argument even under 'scream'."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_41b : LinguisticExample :=
  { id := "major2024_41b"
    source := ⟨"major-2024", "ex. (41b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ning ket-ken-lik-i-ni de-p warqiri-di."
    discourseSegments := []
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ning", "Tursun-GEN"), ("ket-ken-lik-i-ni", "leave-PTPL-COMP-3POSS-ACC"), ("de-p", "say-CNV"), ("warqiri-di", "scream-PST-3")]
    translation := "Mahinur screamed, saying *(that Tursun left)."
    context := ""
    judgment := .acceptable
    alternatives := [("Mahinur de-p warqiri-di.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "subcategorization-persistence"), ("construction", "dep + scream")]
    comment := "Paper prints '*(Tursun-ning ket-ken-lik-i-ni)': same persistence as (41a) with a clausal DP complement of 'say' inside the dep clause."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_49a : LinguisticExample :=
  { id := "major2024_49a"
    source := ⟨"major-2024", "ex. (49a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Tursun-ning ket-ken-lik (xewir)-i méni hayran qal-dur-d-i."
    discourseSegments := []
    glossedTokens := [("Tursun-ning", "Tursun-GEN"), ("ket-ken-lik", "leave-PTPL.PST-COMP"), ("(xewir)-i", "(news)-3POSS"), ("méni", "1SG.ACC"), ("hayran", "surprise"), ("qal-dur-d-i", "remain-CAUS-PST-3")]
    translation := "(The news) that Tursun left surprised me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subject-position"), ("clauseType", "participial")]
    comment := "The participial clause can serve as the grammatical subject (with nominative case) of the psych predicate 'make surprised', unlike dep clauses (49b)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_49b : LinguisticExample :=
  { id := "major2024_49b"
    source := ⟨"major-2024", "ex. (49b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Tursun-(ni) ket-t-i de-p (xewer) méni hayran qal-dur-d-i."
    discourseSegments := []
    glossedTokens := [("Tursun-(ni)", "Tursun-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("(xewer)", "news"), ("méni", "1SG.ACC"), ("hayran", "surprise"), ("qal-dur-d-i", "remain-CAUS-PST-3")]
    translation := "(The news) that Tursun left surprised me."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subject-position"), ("clauseType", "dep")]
    comment := "Translation marked 'Intended:' in the paper — dep clauses cannot function as grammatical subjects. Fn. 18: grammatical only under a pro-dropped-subject parse ('S/he surprised me, saying that Tursun left')."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [ex_2, ex_38, ex_39a, ex_39b, ex_40a, ex_40b, ex_41a, ex_41b, ex_49a, ex_49b]

end Major2024.Examples
