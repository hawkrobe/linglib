import Linglib.Data.Examples.Schema

/-!
# `Rubinstein2014` — typed example data

Auto-generated from `Linglib/Data/Examples/Rubinstein2014.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Rubinstein2014.Examples`.
-/

namespace Rubinstein2014.Examples

open Data.Examples

def nr_should : LinguisticExample :=
  { id := "rubinstein2014_nr_should"
    source := ⟨"horn-1978", "(31a)"⟩
    reportedIn := some ⟨"rubinstein-2014", "(31a)"⟩
    language := "stan1293"
    primaryText := "I don't think you should leave."
    discourseSegments := []
    glossedTokens := []
    translation := "I don't think you should leave."
    context := "Embedded under 'I don't think', testing the lower-negation (neg-raising) reading."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("modal", "should"), ("category", "modalVerb"), ("diagnostic", "negRaising")]
    comment := "Horn (1978, p. 198) ex. (31a): 'I don't think you should leave' is paraphrasable as 'I think you should stay' — the lower-negation (THINK > NOT > should) reading is available for weak necessity should."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def nr_ought : LinguisticExample :=
  { id := "rubinstein2014_nr_ought"
    source := ⟨"horn-1978", "(31a)"⟩
    reportedIn := some ⟨"rubinstein-2014", "(31a)"⟩
    language := "stan1293"
    primaryText := "I don't think you ought to leave."
    discourseSegments := []
    glossedTokens := []
    translation := "I don't think you ought to leave."
    context := "Embedded under 'I don't think', testing the lower-negation (neg-raising) reading."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("modal", "ought"), ("category", "modalVerb"), ("diagnostic", "negRaising")]
    comment := "Horn (1978, p. 198) ex. (31a): weak necessity 'ought to' admits the lower-negation reading 'I think you ought to stay'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def nr_better : LinguisticExample :=
  { id := "rubinstein2014_nr_better"
    source := ⟨"horn-1978", "(31a)"⟩
    reportedIn := some ⟨"rubinstein-2014", "(31a)"⟩
    language := "stan1293"
    primaryText := "I don't think you'd better leave."
    discourseSegments := []
    glossedTokens := []
    translation := "I don't think you'd better leave."
    context := "Embedded under 'I don't think', testing the lower-negation (neg-raising) reading."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("modal", "better"), ("category", "evaluativeComparative"), ("diagnostic", "negRaising")]
    comment := "Horn (1978, p. 198) ex. (31a): the comparative evaluative ''d better' neg-raises, paraphrasable as 'I think you'd better stay'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def nr_good : LinguisticExample :=
  { id := "rubinstein2014_nr_good"
    source := ⟨"horn-1978", "(30)"⟩
    reportedIn := some ⟨"rubinstein-2014", "(30)"⟩
    language := "stan1293"
    primaryText := "It wouldn't be good for you to cheat on your taxes."
    discourseSegments := []
    glossedTokens := []
    translation := "It wouldn't be good for you to cheat on your taxes."
    context := "Negated evaluative; tests the excluded-middle (neg-raising) inference under higher negation."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("modal", "good"), ("category", "evaluativeComparative"), ("diagnostic", "negRaising")]
    comment := "Horn (1978, p. 211) ex. (30): 'It wouldn't be good for you to cheat' is read as 'It would be good for you not to cheat' — modal 'good' neg-raises."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def nr_must : LinguisticExample :=
  { id := "rubinstein2014_nr_must"
    source := ⟨"horn-1978", "(31b)"⟩
    reportedIn := some ⟨"rubinstein-2014", "(31b)"⟩
    language := "stan1293"
    primaryText := "I don't think you must leave."
    discourseSegments := []
    glossedTokens := []
    translation := "I don't think you must leave."
    context := "Embedded under 'I don't think', testing whether the lower-negation reading is available for a strong necessity modal."
    judgment := .marginal
    alternatives := []
    readings := [("lowerNeg", .unacceptable)]
    paperFeatures := [("modal", "must"), ("category", "modalVerb"), ("diagnostic", "negRaising")]
    comment := "Horn (1978, p. 198) ex. (31b): strong necessity 'must' does NOT support the lower-negation reading — 'I don't think you must leave' is not equivalent to 'I think you must stay'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def nr_haveTo : LinguisticExample :=
  { id := "rubinstein2014_nr_haveTo"
    source := ⟨"horn-1978", "(31b)"⟩
    reportedIn := some ⟨"rubinstein-2014", "(31b)"⟩
    language := "stan1293"
    primaryText := "I don't think you have to leave."
    discourseSegments := []
    glossedTokens := []
    translation := "I don't think you have to leave."
    context := "Embedded under 'I don't think', testing whether the lower-negation reading is available for a strong necessity modal."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .unacceptable)]
    paperFeatures := [("modal", "have to"), ("category", "modalVerb"), ("diagnostic", "negRaising")]
    comment := "Horn (1978, p. 198) ex. (31b): strong necessity 'have to' lacks the lower-negation reading; negation can only be interpreted in the matrix clause."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def nr_adif : LinguisticExample :=
  { id := "rubinstein2014_nr_adif"
    source := ⟨"rubinstein-2014", "(33)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "ce'irim sinim kayom lo xošvim še-'adif axeret."
    discourseSegments := []
    glossedTokens := [("ce'irim", "young.PL"), ("sinim", "Chinese.PL"), ("kayom", "today"), ("lo", "NEG"), ("xošvim", "think.PL"), ("še-'adif", "that-preferable"), ("axeret", "differently")]
    translation := "Young Chinese these days don't think it would be better otherwise."
    context := "Blog discussion of attitudes; tests neg-raising (cyclicity) of 'adif 'preferable' in Hebrew."
    judgment := .acceptable
    alternatives := []
    readings := [("lowerNeg", .acceptable)]
    paperFeatures := [("modal", "adif"), ("category", "evaluativeComparative"), ("diagnostic", "negRaising")]
    comment := "Rubinstein (2014) ex. (33): 'adif 'preferable' shows the neg-raising (cyclicity) reading in Hebrew — negation interpreted narrowly under the evaluative comparative (THINK > PREFERABLE > NOT)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ought_lexical : LinguisticExample :=
  { id := "rubinstein2014_ought_lexical"
    source := ⟨"rubinstein-2014", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I ought to do the dishes but I don't have to."
    discourseSegments := []
    glossedTokens := []
    translation := "I ought to do the dishes but I don't have to."
    context := "Test 1 (x E q, but doesn't have to q) with lexical weak-necessity 'ought'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "ought"), ("category", "modalVerb"), ("strategy", "lexical"), ("diagnostic", "test1")]
    comment := "Rubinstein (2014) ex. (8a), 'Lexical WN': English dedicates a lexical item (ought/should) to weak necessity. Passes Test 1 — felicitous because weak necessity is strictly weaker than have-to."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def compositional_deberia : LinguisticExample :=
  { id := "rubinstein2014_compositional_deberia"
    source := ⟨"von-fintel-iatridou-2008", "(8b)"⟩
    reportedIn := some ⟨"rubinstein-2014", "(8b)"⟩
    language := "stan1288"
    primaryText := "Debería limpiar los platos, pero no estoy obligado."
    discourseSegments := []
    glossedTokens := [("Debería", "must.COND"), ("limpiar", "clean.INF"), ("los", "DEF.M.PL"), ("platos", "dish.PL"), ("pero", "but"), ("no", "NEG"), ("estoy", "be.1SG"), ("obligado", "obliged")]
    translation := "I ought to clean the dishes, but I am not obliged to."
    context := "Spanish derives weak necessity compositionally: strong modal deber + conditional morphology."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "deberia"), ("category", "compositional"), ("strategy", "compositional")]
    comment := "Rubinstein (2014) ex. (8b), 'Compositional WN' (von Fintel & Iatridou 2008, p. 122): Spanish builds weak necessity from a strong necessity modal (deber) plus the conditional morphology characteristic of counterfactual consequents."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def test1_carix : LinguisticExample :=
  { id := "rubinstein2014_test1_carix"
    source := ⟨"rubinstein-2014", "(16a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "hu carix lištof et ha-kelim, aval hu lo xayav."
    discourseSegments := []
    glossedTokens := [("hu", "3SG.M"), ("carix", "need.SG.M"), ("lištof", "wash.INF"), ("et", "ACC"), ("ha-kelim", "DEF-dish.PL"), ("aval", "but"), ("hu", "3SG.M"), ("lo", "NEG"), ("xayav", "must.SG.M")]
    translation := "He needs to wash the dishes, but he doesn't have to."
    context := "Test 1 (x ought to q, but doesn't have to) with carix 'need' substituted for ought."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "carix"), ("category", "modalVerb"), ("diagnostic", "test1")]
    comment := "Rubinstein (2014) ex. (16a): substituting carix 'need' for ought yields a contradiction in Test 1 — carix aligns with strong necessity (xayav 'must'), so 'needs to but doesn't have to' is infelicitous."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def test2_carix : LinguisticExample :=
  { id := "rubinstein2014_test2_carix"
    source := ⟨"rubinstein-2014", "(19)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "melcarim xayavim lištof yadayim, aval orxim raq crxim."
    discourseSegments := []
    glossedTokens := [("melcarim", "waiter.PL"), ("xayavim", "must.PL"), ("lištof", "wash.INF"), ("yadayim", "hand.DU"), ("aval", "but"), ("orxim", "guest.PL"), ("raq", "only"), ("crxim", "need.PL")]
    translation := "Waiters have to wash their hands, but guests only need to."
    context := "Test 2 with the exclusive 'only' (raq): y has to q, x only need-to q."
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "carix"), ("category", "modalVerb"), ("diagnostic", "test2")]
    comment := "Rubinstein (2014) ex. (19): 'Test 2 with an exclusive' — carix 'need' does not set up a felicitous scalar contrast against xayav 'must', confirming it is not a weak necessity modal."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def heb_yoter_tov : LinguisticExample :=
  { id := "rubinstein2014_heb_yoter_tov"
    source := ⟨"rubinstein-2014", "(21a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "yoter tov še-hu yitpater, aval hu lo xayav lehitpater."
    discourseSegments := []
    glossedTokens := [("yoter", "more"), ("tov", "good"), ("še-hu", "that-3SG.M"), ("yitpater", "resign.FUT.3SG.M"), ("aval", "but"), ("hu", "3SG.M"), ("lo", "NEG"), ("xayav", "must.SG.M"), ("lehitpater", "resign.INF")]
    translation := "It is better that he resign, but he doesn't have to resign."
    context := "Bribe scenario: a convicted politician ought to resign though no law requires it. Hebrew renders weak-necessity 'ought' via morphological comparison (yoter tov 'more good')."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "tov"), ("category", "evaluativeComparative"), ("strategy", "evaluativeComparative"), ("diagnostic", "test1")]
    comment := "Rubinstein (2014) ex. (21a): Hebrew, lacking a lexical weak-necessity modal, translates priority-type 'ought' with the morphological comparative yoter/haxi tov 'more/most good'. Passes Test 1."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def heb_adif : LinguisticExample :=
  { id := "rubinstein2014_heb_adif"
    source := ⟨"rubinstein-2014", "(21b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "'adif še-hu yitpater, aval hu lo xayav lehitpater."
    discourseSegments := []
    glossedTokens := [("'adif", "preferable"), ("še-hu", "that-3SG.M"), ("yitpater", "resign.FUT.3SG.M"), ("aval", "but"), ("hu", "3SG.M"), ("lo", "NEG"), ("xayav", "must.SG.M"), ("lehitpater", "resign.INF")]
    translation := "It is preferable that he resign, but he doesn't have to resign."
    context := "Bribe scenario; lexical comparison with a predicate of preference, 'adif 'preferable'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "adif"), ("category", "evaluativeComparative"), ("strategy", "evaluativeComparative"), ("diagnostic", "test1")]
    comment := "Rubinstein (2014) ex. (21b): lexical comparison with the predicate of preference 'adif 'preferable'."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def heb_kday : LinguisticExample :=
  { id := "rubinstein2014_heb_kday"
    source := ⟨"rubinstein-2014", "(21c)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "kday še-hu yitpater, aval hu lo xayav lehitpater."
    discourseSegments := []
    glossedTokens := [("kday", "worthwhile"), ("še-hu", "that-3SG.M"), ("yitpater", "resign.FUT.3SG.M"), ("aval", "but"), ("hu", "3SG.M"), ("lo", "NEG"), ("xayav", "must.SG.M"), ("lehitpater", "resign.INF")]
    translation := "It would be good that he resign, but he doesn't have to resign."
    context := "Bribe scenario; implicit comparison with evaluative predicates kday 'worthwhile' / ra'uy 'fitting'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "kday"), ("category", "evaluativeComparative"), ("strategy", "evaluativeComparative"), ("diagnostic", "test1")]
    comment := "Rubinstein (2014) ex. (21c): implicit comparison with evaluative predicates kday 'worthwhile' / ra'uy 'fitting'."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def comp_better : LinguisticExample :=
  { id := "rubinstein2014_comp_better"
    source := ⟨"rubinstein-2014", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It would be better that the politician gets himself fired than that he keep working, but he really ought to quit voluntarily."
    discourseSegments := []
    glossedTokens := []
    translation := "It would be better that the politician gets himself fired than that he keep working, but he really ought to quit voluntarily."
    context := "Three salient alternatives (get fired / keep working / resign). The morphological comparative pairwise-compares two of them."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "better"), ("category", "evaluativeComparative"), ("pairwise", "true")]
    comment := "Rubinstein (2014) ex. (24) (Julia Staffel, p.c.): the morphological comparative 'better' supports an explicit than-clause comparing two alternatives, whereas modal 'ought' (positive/superlative) only selects the overall best. The comparative backbone is overt in the than-clause."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [nr_should, nr_ought, nr_better, nr_good, nr_must, nr_haveTo, nr_adif, ought_lexical, compositional_deberia, test1_carix, test2_carix, heb_yoter_tov, heb_adif, heb_kday, comp_better]

end Rubinstein2014.Examples
