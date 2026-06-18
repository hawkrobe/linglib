import Linglib.Data.Examples.Schema

/-!
# `Iatridou2000` — typed example data

Auto-generated from `Linglib/Data/Examples/Iatridou2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Iatridou2000.Examples`.
-/

namespace Iatridou2000.Examples

open Data.Examples

def ex1a : LinguisticExample :=
  { id := "iatridou2000_ex1a"
    source := ⟨"iatridou-2000", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wish I had a car."
    discourseSegments := []
    glossedTokens := []
    translation := "I wish I had a car."
    context := "Present counterfactual wish. Conveys: I don't have a car now. Past morphology (`had`) but present-time reference."
    judgment := .acceptable
    alternatives := []
    readings := [("present-CF (car absent now)", .acceptable)]
    paperFeatures := [("construction", "wish"), ("cf_type", "presCF")]
    comment := "Iatridou 2000 ex (1a), Linguistic Inquiry 31(2) p. 232. First of the (1a)/(1b) wishes pair. The grammatical past-tense morpheme contributes counterfactuality (about the present), not temporal precedence — Iatridou's central exclusion-feature claim."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex1b : LinguisticExample :=
  { id := "iatridou2000_ex1b"
    source := ⟨"iatridou-2000", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wish I had had a car when I was a student."
    discourseSegments := []
    glossedTokens := []
    translation := "I wish I had had a car when I was a student."
    context := "Past counterfactual wish. Conveys: I didn't have a car then (student days). Says nothing about whether I have a car now. Past-on-past morphology (`had had`) — the doubling encodes BOTH counterfactuality AND past temporal reference."
    judgment := .acceptable
    alternatives := []
    readings := [("past-CF (no car as student)", .acceptable)]
    paperFeatures := [("construction", "wish"), ("cf_type", "pastCF")]
    comment := "Iatridou 2000 ex (1b), p. 232. Second of the wishes pair. The contrast (1a)/(1b) motivates separating the counterfactuality-marking past morpheme from the temporal past morpheme."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2a : LinguisticExample :=
  { id := "iatridou2000_ex2a"
    source := ⟨"iatridou-2000", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he were smart, he would be rich."
    discourseSegments := []
    glossedTokens := []
    translation := "If he were smart, he would be rich."
    context := "Present counterfactual conditional. Conveys: he is not smart AND he is not rich. Past morphology (`were`, `would`) with present reference."
    judgment := .acceptable
    alternatives := []
    readings := [("present-CF (he is not smart and not rich)", .acceptable)]
    paperFeatures := [("construction", "conditional"), ("cf_type", "presCF")]
    comment := "Iatridou 2000 ex (2a), p. 232. Canonical present counterfactual conditional. Iatridou's own (2a) uses `If he were smart`; the generic `If John were here` / `If John were taller` form is widely cited but not verbatim from the paper."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2b : LinguisticExample :=
  { id := "iatridou2000_ex2b"
    source := ⟨"iatridou-2000", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he had been smart, he would have been rich."
    discourseSegments := []
    glossedTokens := []
    translation := "If he had been smart, he would have been rich."
    context := "Past counterfactual conditional. Conveys: he was not smart (in general or on one specific occasion) AND he was not rich. Past-perfect morphology (`had been`, `would have been`) encodes BOTH counterfactuality AND past reference."
    judgment := .acceptable
    alternatives := []
    readings := [("past-CF (he was not smart and not rich)", .acceptable)]
    paperFeatures := [("construction", "conditional"), ("cf_type", "pastCF")]
    comment := "Iatridou 2000 ex (2b), p. 232. Past-CF counterpart to (2a). The (2a)/(2b) contrast — like (1a)/(1b) — diagnostics the exclusion-feature analysis: one past morpheme for counterfactuality (excludes the actual world), a second past morpheme for past tense (excludes the present)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def en_flv : LinguisticExample :=
  { id := "iatridou2000_en_flv"
    source := ⟨"iatridou-2000", "(62a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If he took the syrup, he would get better."
    discourseSegments := []
    glossedTokens := []
    translation := "If he took the syrup, he would get better."
    context := "Future Less Vivid conditional with a telic predicate (take the syrup). One (modal) ExclF; the past morphology is fake."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "flv"), ("past_layers", "1"), ("impf", "no"), ("subj", "no")]
    comment := "Iatridou 2000 ex (62a), p. 250. English FLV: simple past in the antecedent, `would` in the consequent. No imperfective morphology (English lacks it)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_presCF : LinguisticExample :=
  { id := "iatridou2000_en_presCF"
    source := ⟨"iatridou-2000", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I believed in ghosts, I would be afraid now."
    discourseSegments := []
    glossedTokens := []
    translation := "If I believed in ghosts, I would be afraid now."
    context := "Present counterfactual with an individual-level stative predicate (believe in ghosts). Same morphology as the FLV; the PresCF reading arises from the predicate's Aktionsart."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "presCF"), ("past_layers", "1"), ("impf", "no"), ("subj", "no")]
    comment := "Iatridou 2000 ex (61), p. 249. English PresCF, morphologically identical to the FLV (62a). The contrast is in predicate type, not morphology."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_pastCF : LinguisticExample :=
  { id := "iatridou2000_en_pastCF"
    source := ⟨"iatridou-2000", "(48c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If Napoleon had been tall, he would have defeated Wellington."
    discourseSegments := []
    glossedTokens := []
    translation := "If Napoleon had been tall, he would have defeated Wellington."
    context := "Past counterfactual conditional. The pluperfect antecedent has two past layers: one fake (modal ExclF), one real (temporal). Conveys Napoleon was not tall."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "pastCF"), ("past_layers", "2"), ("impf", "no"), ("subj", "no")]
    comment := "Iatridou 2000 ex (48c), p. 245. English PastCF: pluperfect antecedent (`had been`), `would have` consequent. Two past layers distinguish PastCF from FLV/PresCF."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def gr_flv : LinguisticExample :=
  { id := "iatridou2000_gr_flv"
    source := ⟨"iatridou-2000", "(8)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "An eperne afto to siropi tha yinotan kala."
    discourseSegments := []
    glossedTokens := [("An", "if"), ("eperne", "take.PST.IPFV"), ("afto", "this"), ("to", "the"), ("siropi", "syrup"), ("tha", "FUT"), ("yinotan", "become.PST.IPFV"), ("kala", "well")]
    translation := "If he took this syrup, he would get better."
    context := "Modern Greek FLV with a telic predicate. The verbs carry past + imperfective morphology, both fake (future-oriented reading). Contrasts with the FNV (7), which has nonpast + perfective."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "flv"), ("past_layers", "1"), ("impf", "yes"), ("subj", "no")]
    comment := "Iatridou 2000 ex (8), p. 234. Modern Greek FLV: antecedent `an + past + impf`, consequent `tha + past + impf`. Greek FLV and PresCF are morphologically identical, distinguished by predicate type."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def gr_pastCF : LinguisticExample :=
  { id := "iatridou2000_gr_pastCF"
    source := ⟨"iatridou-2000", "(5)"⟩
    reportedIn := none
    language := "mode1248"
    primaryText := "An ixe pari to siropi tha ixe yini kala."
    discourseSegments := []
    glossedTokens := [("An", "if"), ("ixe", "had"), ("pari", "take.PFV"), ("to", "the"), ("siropi", "syrup"), ("tha", "FUT"), ("ixe", "had"), ("yini", "become.PFV"), ("kala", "well")]
    translation := "If he had taken the syrup, he would have gotten better."
    context := "Modern Greek PastCF. Like English, MG uses the pluperfect in the antecedent of a PastCF; the future is an undeclinable particle (tha), so the highest verb (the perfect auxiliary) carries past morphology."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "pastCF"), ("past_layers", "2"), ("impf", "yes"), ("subj", "no")]
    comment := "Iatridou 2000 ex (5), p. 233. Modern Greek PastCF: the pluperfect (ixe + participle) adds a second past layer over the PresCF/FLV."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def fr_flv : LinguisticExample :=
  { id := "iatridou2000_fr_flv"
    source := ⟨"iatridou-2000", "(100)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Si Pierre partait demain, il arriverait là-bas la semaine prochaine."
    discourseSegments := []
    glossedTokens := [("Si", "if"), ("Pierre", "Pierre"), ("partait", "leave.IPFV"), ("demain", "tomorrow"), ("il", "he"), ("arriverait", "arrive.COND"), ("là-bas", "there"), ("la", "the"), ("semaine", "week"), ("prochaine", "next")]
    translation := "If Pierre left tomorrow, he would arrive there next week."
    context := "French FLV: imparfait in the antecedent, conditionnel in the consequent. Iatridou argues the conditionnel is imparfait morphology on a future stem (ExclF + Imp over a future), not a separate `conditional mood`."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "flv"), ("past_layers", "1"), ("impf", "yes"), ("subj", "no")]
    comment := "Iatridou 2000 ex (100), p. 266. French FLV with imparfait/conditionnel. French uses the past indicative, not the (lost productive) past subjunctive."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def fr_presCF : LinguisticExample :=
  { id := "iatridou2000_fr_presCF"
    source := ⟨"iatridou-2000", "(101)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Si je savais que c'était du chocolat, je le mangerais."
    discourseSegments := []
    glossedTokens := [("Si", "if"), ("je", "I"), ("savais", "know.IPFV"), ("que", "that"), ("c'était", "it.be.IPFV"), ("du", "of.the"), ("chocolat", "chocolate"), ("je", "I"), ("le", "it"), ("mangerais", "eat.COND")]
    translation := "If I knew that this were chocolate, I would eat it."
    context := "French PresCF: morphologically identical to the FLV (imparfait/conditionnel); the PresCF reading arises from the individual-level stative predicate."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "presCF"), ("past_layers", "1"), ("impf", "yes"), ("subj", "no")]
    comment := "Iatridou 2000 ex (101), p. 266. French PresCF, same morphology as the FLV (100)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def fr_pastCF : LinguisticExample :=
  { id := "iatridou2000_fr_pastCF"
    source := ⟨"iatridou-2000", "(102)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Si Pierre était venu, je l'aurais vu."
    discourseSegments := []
    glossedTokens := [("Si", "if"), ("Pierre", "Pierre"), ("était", "be.IPFV"), ("venu", "come.PTCP"), ("je", "I"), ("l'aurais", "it.have.COND"), ("vu", "see.PTCP")]
    translation := "If Pierre had come, I would have seen him."
    context := "French PastCF: plus-que-parfait in the antecedent, conditionnel passé in the consequent. Two past layers."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "conditional"), ("cf_type", "pastCF"), ("past_layers", "2"), ("impf", "yes"), ("subj", "no")]
    comment := "Iatridou 2000 ex (102), p. 266. French PastCF: plus-que-parfait/conditionnel passé."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [ex1a, ex1b, ex2a, ex2b, en_flv, en_presCF, en_pastCF, gr_flv, gr_pastCF, fr_flv, fr_presCF, fr_pastCF]

end Iatridou2000.Examples
