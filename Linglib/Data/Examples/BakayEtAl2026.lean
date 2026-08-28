import Linglib.Data.Examples.Schema

/-!
# `BakayEtAl2026` — typed example data

Auto-generated from `Linglib/Data/Examples/BakayEtAl2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BakayEtAl2026.Examples`.
-/

namespace BakayEtAl2026.Examples

open Data.Examples

def ex_5a_match : LinguisticExample :=
  { id := "bakayetal2026_5a_match"
    source := ⟨"bakay-etal-2026", "(5a), Distractor Match"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe yönetmenlerin yeni kameramanlarının sertçe birbirlerini eleştirdiklerini anlattı."
    discourseSegments := []
    glossedTokens := [("Ayşe", "Ayşe"), ("yönetmen-ler-in", "director-PL-GEN"), ("yeni", "new"), ("kameraman-ların-ın", "cameraman-3PL.POSS-GEN"), ("sertçe", "severely"), ("birbirlerin-i", "each.other-ACC"), ("eleştir-dik-lerin-i", "criticize-NMLZ-3PL.POSS-ACC"), ("anlat-tı", "say-PST")]
    translation := "Ayşe said that the directors' new cameramen severely criticized each other."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("distractor", .unacceptable), ("embedded subject", .acceptable)]
    paperFeatures := [("experiment", "1"), ("condition", "Recent Target, Distractor Match"), ("target", "subject"), ("distractor", "possessor in subject"), ("distractorNumber", "plural")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5a_mismatch : LinguisticExample :=
  { id := "bakayetal2026_5a_mismatch"
    source := ⟨"bakay-etal-2026", "(5a), Distractor Mismatch"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe yönetmenin yeni kameramanlarının sertçe birbirlerini eleştirdiklerini anlattı."
    discourseSegments := []
    glossedTokens := [("Ayşe", "Ayşe"), ("yönetmen-in", "director-GEN"), ("yeni", "new"), ("kameraman-ların-ın", "cameraman-3PL.POSS-GEN"), ("sertçe", "severely"), ("birbirlerin-i", "each.other-ACC"), ("eleştir-dik-lerin-i", "criticize-NMLZ-3PL.POSS-ACC"), ("anlat-tı", "say-PST")]
    translation := "Ayşe said that the director's new cameramen severely criticized each other."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("distractor", .unacceptable), ("embedded subject", .acceptable)]
    paperFeatures := [("experiment", "1"), ("condition", "Recent Target, Distractor Mismatch"), ("target", "subject"), ("distractor", "possessor in subject"), ("distractorNumber", "singular")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5b_match : LinguisticExample :=
  { id := "bakayetal2026_5b_match"
    source := ⟨"bakay-etal-2026", "(5b), Distractor Match"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanların yönetmenlerin izniyle sertçe birbirlerini eleştirdiklerini anlattı."
    discourseSegments := []
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-lar-ın", "cameraman-PL-GEN"), ("yönetmen-ler-in", "director-PL-GEN"), ("izn-i-yle", "permission-3SG.POSS-COM"), ("sertçe", "severely"), ("birbirlerin-i", "each.other-ACC"), ("eleştir-dik-lerin-i", "criticize-NMLZ-3PL.POSS-ACC"), ("anlat-tı", "say-PST")]
    translation := "Ayşe said that the cameramen, with the directors' permission, severely criticized each other."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("distractor", .unacceptable)]
    paperFeatures := [("experiment", "1"), ("condition", "Distant Target, Distractor Match"), ("target", "subject"), ("distractor", "possessor in adjunct"), ("distractorNumber", "plural")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5b_mismatch : LinguisticExample :=
  { id := "bakayetal2026_5b_mismatch"
    source := ⟨"bakay-etal-2026", "(5b), Distractor Mismatch"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanların yönetmenin izniyle sertçe birbirlerini eleştirdiklerini anlattı."
    discourseSegments := []
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-lar-ın", "cameraman-PL-GEN"), ("yönetmen-in", "director-GEN"), ("izn-i-yle", "permission-3SG.POSS-COM"), ("sertçe", "severely"), ("birbirlerin-i", "each.other-ACC"), ("eleştir-dik-lerin-i", "criticize-NMLZ-3PL.POSS-ACC"), ("anlat-tı", "say-PST")]
    translation := "Ayşe said that the cameramen, with the director's permission, severely criticized each other."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("distractor", .unacceptable)]
    paperFeatures := [("experiment", "1"), ("condition", "Distant Target, Distractor Mismatch"), ("target", "subject"), ("distractor", "possessor in adjunct"), ("distractorNumber", "singular")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8a_match : LinguisticExample :=
  { id := "bakayetal2026_8a_match"
    source := ⟨"bakay-etal-2026", "(8a), IO Match"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanların yönetmenlere açıkça birbirlerini sorduğunu anladı."
    discourseSegments := []
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-lar-ın", "cameraman-PL-GEN"), ("yönetmen-ler-e", "director-PL-DAT"), ("açıkça", "openly"), ("birbirlerin-i", "each.other-ACC"), ("sor-duğ-un-u", "ask-NMLZ-3SG.POSS-ACC"), ("anla-dı", "notice-PST")]
    translation := "Ayşe noticed that the cameramen openly asked the directors about each other."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("indirect object", .acceptable)]
    paperFeatures := [("experiment", "2"), ("condition", "Plural Subject, IO Match"), ("target", "subject"), ("second", "indirect object"), ("secondNumber", "plural")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8a_mismatch : LinguisticExample :=
  { id := "bakayetal2026_8a_mismatch"
    source := ⟨"bakay-etal-2026", "(8a), IO Mismatch"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanların yönetmene açıkça birbirlerini sorduğunu anladı."
    discourseSegments := []
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-lar-ın", "cameraman-PL-GEN"), ("yönetmen-e", "director-DAT"), ("açıkça", "openly"), ("birbirlerin-i", "each.other-ACC"), ("sor-duğ-un-u", "ask-NMLZ-3SG.POSS-ACC"), ("anla-dı", "notice-PST")]
    translation := "Ayşe noticed that the cameramen openly asked the director about each other."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("indirect object", .acceptable)]
    paperFeatures := [("experiment", "2"), ("condition", "Plural Subject, IO Mismatch"), ("target", "subject"), ("second", "indirect object"), ("secondNumber", "singular")]
    comment := "The paper coindexes singular indirect objects as available, since they occasionally bind the reciprocal despite the number mismatch."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8b_match : LinguisticExample :=
  { id := "bakayetal2026_8b_match"
    source := ⟨"bakay-etal-2026", "(8b), Distractor Match"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanların yönetmenlere göre açıkça birbirlerini sorduğunu anladı."
    discourseSegments := []
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-lar-ın", "cameraman-PL-GEN"), ("yönetmen-ler-e", "director-PL-DAT"), ("göre", "according.to"), ("açıkça", "openly"), ("birbirlerin-i", "each.other-ACC"), ("sor-duğ-un-u", "ask-NMLZ-3SG.POSS-ACC"), ("anla-dı", "notice-PST")]
    translation := "Ayşe noticed that the cameramen, according to the directors, openly asked about each other."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("distractor", .unacceptable)]
    paperFeatures := [("experiment", "2"), ("condition", "Plural Subject, Distractor Match"), ("target", "subject"), ("distractor", "postpositional adjunct"), ("distractorNumber", "plural")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8b_mismatch : LinguisticExample :=
  { id := "bakayetal2026_8b_mismatch"
    source := ⟨"bakay-etal-2026", "(8b), Distractor Mismatch"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanların yönetmene göre açıkça birbirlerini sorduğunu anladı."
    discourseSegments := []
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-lar-ın", "cameraman-PL-GEN"), ("yönetmen-e", "director-DAT"), ("göre", "according.to"), ("açıkça", "openly"), ("birbirlerin-i", "each.other-ACC"), ("sor-duğ-un-u", "ask-NMLZ-3SG.POSS-ACC"), ("anla-dı", "notice-PST")]
    translation := "Ayşe noticed that the cameramen, according to the director, openly asked about each other."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("distractor", .unacceptable)]
    paperFeatures := [("experiment", "2"), ("condition", "Plural Subject, Distractor Mismatch"), ("target", "subject"), ("distractor", "postpositional adjunct"), ("distractorNumber", "singular")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8c : LinguisticExample :=
  { id := "bakayetal2026_8c"
    source := ⟨"bakay-etal-2026", "(8c), Singular Subject, IO Match"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe kameramanın yönetmenlere açıkça birbirlerini sorduğunu anladı."
    discourseSegments := []
    glossedTokens := [("Ayşe", "Ayşe"), ("kameraman-ın", "cameraman-GEN"), ("yönetmen-ler-e", "director-PL-DAT"), ("açıkça", "openly"), ("birbirlerin-i", "each.other-ACC"), ("sor-duğ-un-u", "ask-NMLZ-3SG.POSS-ACC"), ("anla-dı", "notice-PST")]
    translation := "Ayşe noticed that the cameraman openly asked the directors about each other."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("indirect object", .acceptable)]
    paperFeatures := [("experiment", "2"), ("condition", "Singular Subject, IO Match"), ("target", "subject"), ("targetNumber", "singular"), ("second", "indirect object"), ("secondNumber", "plural")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10a : LinguisticExample :=
  { id := "bakayetal2026_10a"
    source := ⟨"bakay-etal-2026", "(10a), IO, Dative"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe aşçıların garsonlara sebepsizce birbirlerini kötülediklerini biliyor."
    discourseSegments := []
    glossedTokens := [("Ayşe", "Ayşe"), ("aşçı-lar-ın", "chef-PL-GEN"), ("garson-lar-a", "waiter-PL-DAT"), ("sebepsizce", "without.reason"), ("birbirlerin-i", "each.other-ACC"), ("kötüle-dik-lerin-i", "badmouth-NMLZ-3PL.POSS-ACC"), ("bil-iyor", "know-PROG")]
    translation := "Ayşe knows that the chefs badmouthed each other to the waiters for no reason."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("indirect object", .acceptable)]
    paperFeatures := [("experiment", "3"), ("condition", "IO, Dative"), ("target", "subject"), ("second", "indirect object"), ("secondNumber", "plural")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10b : LinguisticExample :=
  { id := "bakayetal2026_10b"
    source := ⟨"bakay-etal-2026", "(10b), Distractor, Dative"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe aşçıların garsonlara rağmen sebepsizce birbirlerini kötülediklerini biliyor."
    discourseSegments := []
    glossedTokens := [("Ayşe", "Ayşe"), ("aşçı-lar-ın", "chef-PL-GEN"), ("garson-lar-a", "waiter-PL-DAT"), ("rağmen", "despite"), ("sebepsizce", "without.reason"), ("birbirlerin-i", "each.other-ACC"), ("kötüle-dik-lerin-i", "badmouth-NMLZ-3PL.POSS-ACC"), ("bil-iyor", "know-PROG")]
    translation := "Ayşe knows that the chefs, despite the waiters, badmouthed each other for no reason."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("distractor", .unacceptable)]
    paperFeatures := [("experiment", "3"), ("condition", "Distractor, Dative"), ("target", "subject"), ("distractor", "postpositional adjunct"), ("distractorNumber", "plural")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10c : LinguisticExample :=
  { id := "bakayetal2026_10c"
    source := ⟨"bakay-etal-2026", "(10c), Distractor, Genitive"⟩
    reportedIn := none
    language := "nucl1301"
    primaryText := "Ayşe aşçıların garsonların etkisiyle sebepsizce birbirlerini kötülediklerini biliyor."
    discourseSegments := []
    glossedTokens := [("Ayşe", "Ayşe"), ("aşçı-lar-ın", "chef-PL-GEN"), ("garson-lar-ın", "waiter-PL-GEN"), ("etki-si-yle", "influence-3SG.POSS-COM"), ("sebepsizce", "without.reason"), ("birbirlerin-i", "each.other-ACC"), ("kötüle-dik-lerin-i", "badmouth-NMLZ-3PL.POSS-ACC"), ("bil-iyor", "know-PROG")]
    translation := "Ayşe knows that the chefs, with the waiters' influence, badmouthed each other for no reason."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("matrix subject", .unacceptable), ("embedded subject", .acceptable), ("distractor", .unacceptable)]
    paperFeatures := [("experiment", "3"), ("condition", "Distractor, Genitive"), ("target", "subject"), ("distractor", "possessor in adjunct"), ("distractorNumber", "plural")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_5a_match, ex_5a_mismatch, ex_5b_match, ex_5b_mismatch, ex_8a_match, ex_8a_mismatch, ex_8b_match, ex_8b_mismatch, ex_8c, ex_10a, ex_10b, ex_10c]

end BakayEtAl2026.Examples
