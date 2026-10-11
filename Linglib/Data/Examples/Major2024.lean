module

public import Linglib.Data.Examples.Schema

/-!
# `Major2024` — typed example data

Auto-generated from `Linglib/Data/Examples/Major2024.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Major2024.Examples`.
-/

@[expose] public section

namespace Major2024.Examples

def ex_2 : Datum :=
  { id := "major2024_2"
    source := ⟨"major-2024", "ex. (2)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ni göshnan-ni et-t-i de-p oyla-y-du."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ni", "Tursun-ACC"), ("göshnan-ni", "meatbread-ACC"), ("et-t-i", "make-PST-3"), ("de-p", "say-CNV"), ("oyla-y-du", "think-NONPST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "dep"), ("matrixVerb", "oyla")] }

def ex_18a : Datum :=
  { id := "major2024_18a"
    source := ⟨"major-2024", "ex. (18a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Ahmat métal-ni ur-up tüzli-wet-t-i, men=mu shundaq tüzli-wet-t-im."
    glossedTokens := [("Ahmat", "Ahmat"), ("métal-ni", "metal-ACC"), ("ur-up", "hit-CNV"), ("tüzli-wet-t-i", "flatten-COMPL-PST-3"), ("men=mu", "1SG=ADD"), ("shundaq", "like.this"), ("tüzli-wet-t-im", "flatten-COMPL-PST-1SG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "proform"), ("clause", "converb"), ("height", "VP")] }

def ex_18b : Datum :=
  { id := "major2024_18b"
    source := ⟨"major-2024", "ex. (18b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Tursun polu ét-ip yé-d-i, men=mu shundaq yé-d-im."
    glossedTokens := [("Tursun", "Tursun"), ("polu", "pilaf"), ("ét-ip", "make-CNV"), ("yé-d-i", "eat-PST-3"), ("men=mu", "1SG=ADD"), ("shundaq", "like.this"), ("yé-d-im", "eat-PST-1SG")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "proform"), ("clause", "converb"), ("height", "TP")] }

def ex_23a : Datum :=
  { id := "major2024_23a"
    source := ⟨"major-2024", "ex. (23a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur héchnémi-ni ét-ip yérim-i-ni yé-mi-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("héchnémi-ni", "no.what-ACC"), ("ét-ip", "make-CNV"), ("yérim-i-ni", "half-3POSS-ACC"), ("yé-mi-d-i", "eat-NEG-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "nci"), ("clause", "converb"), ("height", "TP")] }

def ex_26b : Datum :=
  { id := "major2024_26b"
    source := ⟨"major-2024", "ex. (26b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Biz héchkim-ge dora bér-ip uxla-t-mi-d-uq."
    glossedTokens := [("Biz", "1PL"), ("héchkim-ge", "no.who-DAT"), ("dora", "drug"), ("bér-ip", "give-CNV"), ("uxla-t-mi-d-uq", "sleep-CAUS-NEG-PST-1PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "nci"), ("clause", "converb"), ("height", "VP")] }

def ex_38 : Datum :=
  { id := "major2024_38"
    source := ⟨"major-2024", "ex. (38)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ni ket-t-i de-p warqiri-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ni", "Tursun-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("warqiri-d-i", "scream-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "dep"), ("matrixVerb", "warqira")] }

def ex_39a : Datum :=
  { id := "major2024_39a"
    source := ⟨"major-2024", "ex. (39a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur birnémi-ler-ni dé-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("birnémi-ler-ni", "one.what-PL-ACC"), ("dé-d-i", "say-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "de"), ("complement", "dp"), ("verbForm", "finite")] }

def ex_39a_bare : Datum :=
  { id := "major2024_39a_bare"
    source := ⟨"major-2024", "ex. (39a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur dé-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("dé-d-i", "say-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "de"), ("complement", "none"), ("verbForm", "finite")] }

def ex_39b : Datum :=
  { id := "major2024_39b"
    source := ⟨"major-2024", "ex. (39b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur warqiri-di."
    glossedTokens := [("Mahinur", "Mahinur"), ("warqiri-di", "scream-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "warqira"), ("complement", "none"), ("verbForm", "finite")] }

def ex_39b_dp : Datum :=
  { id := "major2024_39b_dp"
    source := ⟨"major-2024", "ex. (39b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur birnémi-ler-ni warqiri-di."
    glossedTokens := [("Mahinur", "Mahinur"), ("birnémi-ler-ni", "one.what-PL-ACC"), ("warqiri-di", "scream-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "warqira"), ("complement", "dp"), ("verbForm", "finite")] }

def ex_40a : Datum :=
  { id := "major2024_40a"
    source := ⟨"major-2024", "ex. (40a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ning ket-ken-lik-i-ni dé-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ning", "Tursun-GEN"), ("ket-ken-lik-i-ni", "leave-PTPL-COMP-3POSS-ACC"), ("dé-d-i", "say-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "de"), ("complement", "participial"), ("verbForm", "finite")] }

def ex_40b_participial : Datum :=
  { id := "major2024_40b_participial"
    source := ⟨"major-2024", "ex. (40b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ning ket-ken-lik-i-ni warqiri-di."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ning", "Tursun-GEN"), ("ket-ken-lik-i-ni", "leave-PTPL-COMP-3POSS-ACC"), ("warqiri-di", "scream-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "warqira"), ("complement", "participial"), ("verbForm", "finite")] }

def ex_41a : Datum :=
  { id := "major2024_41a"
    source := ⟨"major-2024", "ex. (41a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur birnémi-ler-ni de-p warqiri-di."
    glossedTokens := [("Mahinur", "Mahinur"), ("birnémi-ler-ni", "one.what-PL-ACC"), ("de-p", "say-CNV"), ("warqiri-di", "scream-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "de"), ("complement", "dp"), ("verbForm", "converb")] }

def ex_41a_bare : Datum :=
  { id := "major2024_41a_bare"
    source := ⟨"major-2024", "ex. (41a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur de-p warqiri-di."
    glossedTokens := [("Mahinur", "Mahinur"), ("de-p", "say-CNV"), ("warqiri-di", "scream-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "de"), ("complement", "none"), ("verbForm", "converb")] }

def ex_41b : Datum :=
  { id := "major2024_41b"
    source := ⟨"major-2024", "ex. (41b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ning ket-ken-lik-i-ni de-p warqiri-di."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ning", "Tursun-GEN"), ("ket-ken-lik-i-ni", "leave-PTPL-COMP-3POSS-ACC"), ("de-p", "say-CNV"), ("warqiri-di", "scream-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "de"), ("complement", "participial"), ("verbForm", "converb")] }

def ex_42a : Datum :=
  { id := "major2024_42a"
    source := ⟨"major-2024", "ex. (42a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur birnémi-ler-ni oyla-p warqiri-di."
    glossedTokens := [("Mahinur", "Mahinur"), ("birnémi-ler-ni", "one.what-PL-ACC"), ("oyla-p", "think-CNV"), ("warqiri-di", "scream-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "oyla"), ("complement", "dp"), ("verbForm", "converb")] }

def ex_42a_bare : Datum :=
  { id := "major2024_42a_bare"
    source := ⟨"major-2024", "ex. (42a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur oyla-p warqiri-di."
    glossedTokens := [("Mahinur", "Mahinur"), ("oyla-p", "think-CNV"), ("warqiri-di", "scream-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "oyla"), ("complement", "none"), ("verbForm", "converb")] }

def ex_42b : Datum :=
  { id := "major2024_42b"
    source := ⟨"major-2024", "ex. (42b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ning ket-ken-lik-i-ni oyla-p warqiri-di."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ning", "Tursun-GEN"), ("ket-ken-lik-i-ni", "leave-PTPL-COMP-3POSS-ACC"), ("oyla-p", "think-CNV"), ("warqiri-di", "scream-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "subcategorization"), ("verb", "oyla"), ("complement", "participial"), ("verbForm", "converb")] }

def ex_49a : Datum :=
  { id := "major2024_49a"
    source := ⟨"major-2024", "ex. (49a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Tursun-ning ket-ken-lik xewir-i méni hayran qal-dur-d-i."
    glossedTokens := [("Tursun-ning", "Tursun-GEN"), ("ket-ken-lik", "leave-PTPL.PST-COMP"), ("xewir-i", "news-3POSS"), ("méni", "1SG.ACC"), ("hayran", "surprise"), ("qal-dur-d-i", "remain-CAUS-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := [("Tursun-ning ket-ken-lik-i méni hayran qal-dur-d-i.", .acceptable)]
    readings := []
    paperFeatures := [("diagnostic", "subject"), ("clause", "participial")] }

def ex_49b : Datum :=
  { id := "major2024_49b"
    source := ⟨"major-2024", "ex. (49b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Tursun-ni ket-t-i de-p xewer méni hayran qal-dur-d-i."
    glossedTokens := [("Tursun-ni", "Tursun-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("xewer", "news"), ("méni", "1SG.ACC"), ("hayran", "surprise"), ("qal-dur-d-i", "remain-CAUS-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := [("Tursun-ni ket-t-i de-p méni hayran qal-dur-d-i.", .ungrammatical)]
    readings := []
    paperFeatures := [("diagnostic", "subject"), ("clause", "dep")] }

def ex_54a : Datum :=
  { id := "major2024_54a"
    source := ⟨"major-2024", "ex. (54a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur héchkim-ni ket-t-i de-p warqiri-mi-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("héchkim-ni", "no.who-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("warqiri-mi-d-i", "scream-NEG-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "nci"), ("clause", "dep"), ("height", "VP"), ("matrixVerb", "warqira")] }

def ex_54b : Datum :=
  { id := "major2024_54b"
    source := ⟨"major-2024", "ex. (54b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur héchkim-ni kel-i-du de-p ket-mi-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("héchkim-ni", "no.who-ACC"), ("kel-i-du", "come-NONPST-3"), ("de-p", "say-CNV"), ("ket-mi-d-i", "leave-NEG-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "nci"), ("clause", "dep"), ("height", "TP"), ("matrixVerb", "ket")] }

def ex_55a : Datum :=
  { id := "major2024_55a"
    source := ⟨"major-2024", "ex. (55a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ni ket-t-i de-p oyli-d-i, biraq men undaq oyli-mi-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ni", "Tursun-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("oyli-d-i", "think-PST-3"), ("biraq", "but"), ("men", "1SG"), ("undaq", "like.that"), ("oyli-mi-d-i", "think-NEG-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "proform"), ("clause", "dep"), ("height", "VP"), ("matrixVerb", "oyla")] }

def ex_55b : Datum :=
  { id := "major2024_55b"
    source := ⟨"major-2024", "ex. (55b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ni kel-i-du de-p ket-t-i, biraq men undaq ket-mi-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ni", "Tursun-ACC"), ("kel-i-du", "come-NONPST-3"), ("de-p", "say-CNV"), ("ket-t-i", "leave-PST-3"), ("biraq", "but"), ("men", "1SG"), ("undaq", "like.that"), ("ket-mi-d-i", "leave-NEG-PST-3")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "proform"), ("clause", "dep"), ("height", "TP"), ("matrixVerb", "ket")] }

def ex_61a : Datum :=
  { id := "major2024_61a"
    source := ⟨"major-2024", "ex. (61a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ning ket-ken-lik-i-ni bil-i-du, biraq u ket-mi-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ning", "Tursun-GEN"), ("ket-ken-lik-i-ni", "leave-PTPL-COMP-3POSS-ACC"), ("bil-i-du", "know-NONPST-3"), ("biraq", "but"), ("u", "he"), ("ket-mi-d-i", "leave-NEG-PST-3")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "denial"), ("clause", "participial"), ("matrixVerb", "bil")] }

def ex_61b : Datum :=
  { id := "major2024_61b"
    source := ⟨"major-2024", "ex. (61b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ni ket-t-i de-p bil-i-du, biraq u ket-mi-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ni", "Tursun-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("bil-i-du", "know-NONPST-3"), ("biraq", "but"), ("u", "he"), ("ket-mi-d-i", "leave-NEG-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "denial"), ("clause", "dep"), ("matrixVerb", "bil")] }

def ex_65a : Datum :=
  { id := "major2024_65a"
    source := ⟨"major-2024", "ex. (65a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ning ket-ken-lik-i-ni unut-t-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ning", "Tursun-GEN"), ("ket-ken-lik-i-ni", "leave-PTCP.PST-COMP-3POSS-ACC"), ("unut-t-i", "forget-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("forgot that", .acceptable)]
    paperFeatures := [("clause", "participial"), ("matrixVerb", "unut")] }

def ex_65b : Datum :=
  { id := "major2024_65b"
    source := ⟨"major-2024", "ex. (65b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ni ket-t-i de-p unut-t-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ni", "Tursun-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("unut-t-i", "forget-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("forgot that", .unacceptable), ("forgot something, saying", .acceptable)]
    paperFeatures := [("clause", "dep"), ("matrixVerb", "unut")] }

def ex_84a : Datum :=
  { id := "major2024_84a"
    source := ⟨"major-2024", "ex. (84a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur téz polu ye-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("téz", "quickly"), ("polu", "pilaf"), ("ye-d-i", "eat-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "object"), ("verb", "ye"), ("case", "bare"), ("objectPosition", "afterAdverb")] }

def ex_84a_acc : Datum :=
  { id := "major2024_84a_acc"
    source := ⟨"major-2024", "ex. (84a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur téz polu-ni ye-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("téz", "quickly"), ("polu-ni", "pilaf-ACC"), ("ye-d-i", "eat-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "object"), ("verb", "ye"), ("case", "ACC"), ("objectPosition", "afterAdverb")] }

def ex_84b : Datum :=
  { id := "major2024_84b"
    source := ⟨"major-2024", "ex. (84b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur polu-ni téz ye-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("polu-ni", "pilaf-ACC"), ("téz", "quickly"), ("ye-d-i", "eat-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "object"), ("verb", "ye"), ("case", "ACC"), ("objectPosition", "beforeAdverb")] }

def ex_84b_bare : Datum :=
  { id := "major2024_84b_bare"
    source := ⟨"major-2024", "ex. (84b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur polu téz ye-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("polu", "pilaf"), ("téz", "quickly"), ("ye-d-i", "eat-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "object"), ("verb", "ye"), ("case", "bare"), ("objectPosition", "beforeAdverb")] }

def ex_88a : Datum :=
  { id := "major2024_88a"
    source := ⟨"major-2024", "ex. (88a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Ziba bol-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("Ziba", "Ziba"), ("bol-d-i", "become-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "object"), ("verb", "bol"), ("case", "bare")] }

def ex_88a_acc : Datum :=
  { id := "major2024_88a_acc"
    source := ⟨"major-2024", "ex. (88a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Ziba-ni bol-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("Ziba-ni", "Ziba-ACC"), ("bol-d-i", "become-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "object"), ("verb", "bol"), ("case", "ACC")] }

def ex_89a : Datum :=
  { id := "major2024_89a"
    source := ⟨"major-2024", "ex. (89a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur söz-ni qil-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("söz-ni", "word-ACC"), ("qil-d-i", "make-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "object"), ("verb", "qil"), ("case", "ACC")] }

def ex_110a : Datum :=
  { id := "major2024_110a"
    source := ⟨"major-2024", "ex. (110a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur siz-ni ket-t-i dé-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("siz-ni", "2SG-ACC"), ("ket-t-i", "leave-PST-3"), ("dé-d-i", "say-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "finite"), ("case", "ACC"), ("matrixVerb", "de"), ("matrixSubject", "animate"), ("sayer", "animate")] }

def ex_110b : Datum :=
  { id := "major2024_110b"
    source := ⟨"major-2024", "ex. (110b)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur siz-ni ket-t-i de-p warqiri-d-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("siz-ni", "2SG-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("warqiri-d-i", "scream-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "dep"), ("case", "ACC"), ("matrixVerb", "warqira"), ("matrixSubject", "animate"), ("sayer", "animate")] }

def ex_110c : Datum :=
  { id := "major2024_110c"
    source := ⟨"major-2024", "ex. (110c)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur siz-ni ket-t-i de-p ket-t-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("siz-ni", "2SG-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("ket-t-i", "leave-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "dep"), ("case", "ACC"), ("matrixVerb", "ket"), ("matrixSubject", "animate"), ("sayer", "animate")] }

def ex_113a : Datum :=
  { id := "major2024_113a"
    source := ⟨"major-2024", "ex. (113a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur méning ut-qan-liq-i-ni eyt-t-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("méning", "1SG.GEN"), ("ut-qan-liq-i-ni", "win-PTPL.PST-COMP-3POSS-ACC"), ("eyt-t-i", "tell-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "participial"), ("case", "GEN"), ("matrixVerb", "éyt"), ("matrixSubject", "animate")] }

def ex_113a_acc : Datum :=
  { id := "major2024_113a_acc"
    source := ⟨"major-2024", "ex. (113a)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur méni ut-qan-liq-i-ni eyt-t-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("méni", "1SG.ACC"), ("ut-qan-liq-i-ni", "win-PTPL.PST-COMP-3POSS-ACC"), ("eyt-t-i", "tell-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "participial"), ("case", "ACC"), ("matrixVerb", "éyt"), ("matrixSubject", "animate")] }

def ex_122 : Datum :=
  { id := "major2024_122"
    source := ⟨"major-2024", "ex. (122)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Siz-ni ket-t-i de-p manga éyt-il-d-i."
    glossedTokens := [("Siz-ni", "2SG"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("manga", "1SG.DAT"), ("éyt-il-d-i", "tell-PASS-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "dep"), ("case", "ACC"), ("matrixVerb", "éyt"), ("matrixVoice", "passive"), ("matrixSubject", "none"), ("impliedAgent", "yes"), ("sayer", "animate")] }

def ex_123 : Datum :=
  { id := "major2024_123"
    source := ⟨"major-2024", "ex. (123)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur Tursun-ni ket-t-i de-p ket-t-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("Tursun-ni", "Tursun-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("ket-t-i", "leave-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "dep"), ("case", "ACC"), ("matrixVerb", "ket"), ("matrixSubject", "animate"), ("sayer", "animate")] }

def ex_124 : Datum :=
  { id := "major2024_124"
    source := ⟨"major-2024", "ex. (124)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Mahinur manga bu xewer-ni Tursun-ni ket-t-i de-p éyt-t-i."
    glossedTokens := [("Mahinur", "Mahinur"), ("manga", "1SG.DAT"), ("bu", "this"), ("xewer-ni", "news-ACC"), ("Tursun-ni", "Tursun-ACC"), ("ket-t-i", "leave-PST-3"), ("de-p", "say-CNV"), ("éyt-t-i", "tell-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "dep"), ("case", "ACC"), ("matrixVerb", "éyt"), ("matrixSubject", "animate"), ("matrixObject", "ACC"), ("sayer", "animate")] }

def ex_127 : Datum :=
  { id := "major2024_127"
    source := ⟨"major-2024", "ex. (127)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Bügün yighin-da Mahinur kéler yil-i Qeshqer-ge bar-i-du de-p éniq bol-d-i."
    glossedTokens := [("Bügün", "today"), ("yighin-da", "meeting-LOC"), ("Mahinur", "Mahinur"), ("kéler", "coming"), ("yil-i", "year-3POSS"), ("Qeshqer-ge", "Kashgar-DAT"), ("bar-i-du", "go-NONPST-3"), ("de-p", "say-CNV"), ("éniq", "clear"), ("bol-d-i", "become-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "dep"), ("case", "bare"), ("matrixVerb", "bol"), ("matrixSubject", "none"), ("sayer", "none")] }

def ex_127_acc : Datum :=
  { id := "major2024_127_acc"
    source := ⟨"major-2024", "ex. (127)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Bügün yighin-da Mahinur-ni kéler yil-i Qeshqer-ge bar-i-du de-p éniq bol-d-i."
    glossedTokens := [("Bügün", "today"), ("yighin-da", "meeting-LOC"), ("Mahinur-ni", "Mahinur-ACC"), ("kéler", "coming"), ("yil-i", "year-3POSS"), ("Qeshqer-ge", "Kashgar-DAT"), ("bar-i-du", "go-NONPST-3"), ("de-p", "say-CNV"), ("éniq", "clear"), ("bol-d-i", "become-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "dep"), ("case", "ACC"), ("matrixVerb", "bol"), ("matrixSubject", "none"), ("sayer", "none")] }

def ex_128 : Datum :=
  { id := "major2024_128"
    source := ⟨"major-2024", "ex. (128)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Bu xewer bügün yighin-da Mahinur kéler yil Qeshqer-ge bar-i-du de-p éniq bol-d-i."
    glossedTokens := [("Bu", "this"), ("xewer", "news"), ("bügün", "today"), ("yighin-da", "meeting-LOC"), ("Mahinur", "Mahinur"), ("kéler", "coming"), ("yil", "year"), ("Qeshqer-ge", "Kashgar-DAT"), ("bar-i-du", "go-NONPST-3"), ("de-p", "say-CNV"), ("éniq", "clear"), ("bol-d-i", "become-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "dep"), ("case", "bare"), ("matrixVerb", "bol"), ("matrixSubject", "inanimate"), ("sayer", "inanimate")] }

def ex_128_acc : Datum :=
  { id := "major2024_128_acc"
    source := ⟨"major-2024", "ex. (128)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Bu xewer bügün yighin-da Mahinur-ni kéler yil Qeshqer-ge bar-i-du de-p éniq bol-d-i."
    glossedTokens := [("Bu", "this"), ("xewer", "news"), ("bügün", "today"), ("yighin-da", "meeting-LOC"), ("Mahinur-ni", "Mahinur-ACC"), ("kéler", "coming"), ("yil", "year"), ("Qeshqer-ge", "Kashgar-DAT"), ("bar-i-du", "go-NONPST-3"), ("de-p", "say-CNV"), ("éniq", "clear"), ("bol-d-i", "become-PST-3")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "dep"), ("case", "ACC"), ("matrixVerb", "bol"), ("matrixSubject", "inanimate"), ("sayer", "inanimate")] }

def ex_129 : Datum :=
  { id := "major2024_129"
    source := ⟨"major-2024", "ex. (129)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Tursun manga éyt-qan xewer-de Mahinur-ni keler yil Qeshqer-ge bar-i-du de-p éniq bol-d-i."
    glossedTokens := [("Tursun", "Tursun"), ("manga", "1SG.DAT"), ("éyt-qan", "tell-PTPL.PST"), ("xewer-de", "news-LOC"), ("Mahinur-ni", "Mahinur-ACC"), ("keler", "coming"), ("yil", "year"), ("Qeshqer-ge", "Kashgar-DAT"), ("bar-i-du", "go-NONPST-3"), ("de-p", "say-CNV"), ("éniq", "clear"), ("bol-d-i", "become-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "dep"), ("case", "ACC"), ("matrixVerb", "bol"), ("matrixSubject", "none"), ("sayer", "animate")] }

def ex_130 : Datum :=
  { id := "major2024_130"
    source := ⟨"major-2024", "ex. (130)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Bashliq-i bügün yighin-da Mahinur-ni kéler yil Qeshqer-ge bar-i-du de-p bu xewer-ni éniq qil-d-i."
    glossedTokens := [("Bashliq-i", "boss-3SG.POSS"), ("bügün", "today"), ("yighin-da", "meeting-LOC"), ("Mahinur-ni", "Mahinur-ACC"), ("kéler", "coming"), ("yil", "year"), ("Qeshqer-ge", "Kashgar-DAT"), ("bar-i-du", "go-NONPST-3"), ("de-p", "say-CNV"), ("bu", "this"), ("xewer-ni", "news-ACC"), ("éniq", "clear"), ("qil-d-i", "make-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "dep"), ("case", "ACC"), ("matrixVerb", "qil"), ("matrixSubject", "animate"), ("matrixObject", "ACC"), ("sayer", "animate")] }

def ex_131 : Datum :=
  { id := "major2024_131"
    source := ⟨"major-2024", "ex. (131)"⟩
    reportedIn := none
    language := "uigh1240"
    primaryText := "Bu xewer meqsetlik bügün yighin-da Mahinur-ni kéler yil Qeshqer-ge bar-i-du de-p éniq qil-in-d-i."
    glossedTokens := [("Bu", "this"), ("xewer", "news"), ("meqsetlik", "intentionally"), ("bügün", "today"), ("yighin-da", "meeting-LOC"), ("Mahinur-ni", "Mahinur-ACC"), ("kéler", "coming"), ("yil", "year"), ("Qeshqer-ge", "Kashgar-DAT"), ("bar-i-du", "go-NONPST-3"), ("de-p", "say-CNV"), ("éniq", "clear"), ("qil-in-d-i", "make-PASS-PST-3")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "case"), ("np", "embeddedSubject"), ("clause", "dep"), ("case", "ACC"), ("matrixVerb", "qil"), ("matrixVoice", "passive"), ("matrixSubject", "inanimate"), ("impliedAgent", "yes"), ("sayer", "animate")] }

def all : List Datum := [ex_2, ex_18a, ex_18b, ex_23a, ex_26b, ex_38, ex_39a, ex_39a_bare, ex_39b, ex_39b_dp, ex_40a, ex_40b_participial, ex_41a, ex_41a_bare, ex_41b, ex_42a, ex_42a_bare, ex_42b, ex_49a, ex_49b, ex_54a, ex_54b, ex_55a, ex_55b, ex_61a, ex_61b, ex_65a, ex_65b, ex_84a, ex_84a_acc, ex_84b, ex_84b_bare, ex_88a, ex_88a_acc, ex_89a, ex_110a, ex_110b, ex_110c, ex_113a, ex_113a_acc, ex_122, ex_123, ex_124, ex_127, ex_127_acc, ex_128, ex_128_acc, ex_129, ex_130, ex_131]

end Major2024.Examples
