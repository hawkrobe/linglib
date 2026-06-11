import Linglib.Data.Examples.Schema

/-!
# `Declerck1991` — typed example data

Auto-generated from `Linglib/Data/Examples/Declerck1991.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Declerck1991.Examples`.
-/

namespace Declerck1991.Examples

open Data.Examples

def domainShift1a : LinguisticExample :=
  { id := "declerck1991_domainShift1a"
    source := ⟨"declerck-1991-grammar", "ch. 3 ex (1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I left while Bill was sleeping and Mary was having a bath."
    discourseSegments := []
    glossedTokens := []
    translation := "I left while Bill was sleeping and Mary was having a bath."
    context := "Declerck's example of three situations simultaneous within one temporal domain. `left` is an absolute past establishing a past domain; the two `was`-progressives are relative tenses expressing simultaneity with the central situation. All three are in the same temporal domain."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Declerck 1991 ch. 3, example (1a). Cornerstone illustration of temporal subordination (no domain shift) — three simultaneous situations under one past domain anchor."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def domainShift1b : LinguisticExample :=
  { id := "declerck1991_domainShift1b"
    source := ⟨"declerck-1991-grammar", "ch. 3 ex (1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Suddenly the phone rang. Jill stood up from her chair, went over to the telephone and picked up the receiver."
    discourseSegments := ["Suddenly the phone rang.", "Jill stood up from her chair, went over to the telephone and picked up the receiver."]
    glossedTokens := []
    translation := "Suddenly the phone rang. Jill stood up from her chair, went over to the telephone and picked up the receiver."
    context := "Declerck's example of domain shift via absolute preterites. Each clause uses an absolute past tense — no relative tense forms like past perfect (anteriority) or conditional (posteriority). Temporal ordering recovered from clause order alone, not from tense composition."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Declerck 1991 ch. 3, example (1b). The minimal pair with (1a): same time-sphere, but no temporal subordination — each clause shifts into a new domain. Iconic ordering from clause order is the pragmatic default."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def domainShift3a : LinguisticExample :=
  { id := "declerck1991_domainShift3a"
    source := ⟨"declerck-1991-grammar", "ch. 3 ex (3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The soldier got seriously wounded. He died shortly afterwards."
    discourseSegments := ["The soldier got seriously wounded.", "He died shortly afterwards."]
    glossedTokens := []
    translation := "The soldier got seriously wounded. He died shortly afterwards."
    context := "Declerck's example (3a): domain shift with `died` as absolute preterite. Temporal posteriority of dying relative to wounding comes from the adverbial `shortly afterwards`, not from any relative tense form."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Declerck 1991 ch. 3 ex (3a). Compared to (3b) `He would die shortly afterwards`, which uses a relative tense (conditional) within the same temporal domain anchored by `got wounded`."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def modalPastWish : LinguisticExample :=
  { id := "declerck1991_modalPastWish"
    source := ⟨"declerck-1991-grammar", "ch. 2 §3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I wish I didn't know his number."
    discourseSegments := []
    glossedTokens := []
    translation := "I wish I didn't know his number."
    context := "Declerck's example of modal past: `didn't know` is past in form but simultaneous in interpretation (the not-knowing is at the wishing time, which is now, not in the past). Contrasts with `He says I didn't know his number` (nonmodal past, true past reference)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Declerck 1991 ch. 2 §3. Cornerstone example of modal past tense — past morphology, non-past interpretation. The 'false tense' phenomenon."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def modalPastIfWas : LinguisticExample :=
  { id := "declerck1991_modalPastIfWas"
    source := ⟨"declerck-1991-grammar", "ch. 2 §3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If I was a rich man, I would travel a lot."
    discourseSegments := []
    glossedTokens := []
    translation := "If I was a rich man, I would travel a lot."
    context := "Declerck's example of modal past in conditional: `was` is past in form but the reference is to the present (the hypothetical speaker now), not to the past."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Declerck 1991 ch. 2 §3. Modal past in conditional protasis — the reference is non-past despite past morphology."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def futurePerfect : LinguisticExample :=
  { id := "declerck1991_futurePerfect"
    source := ⟨"declerck-1991-grammar", "ch. 2 §2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I will have left by then."
    discourseSegments := []
    glossedTokens := []
    translation := "I will have left by then."
    context := "Declerck's example of the future perfect form. The leaving event precedes a reference point `by then` which is itself future relative to utterance."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Declerck 1991 ch. 2 §2. Future perfect listed alongside present perfect, past perfect, conditional, conditional perfect in the tense inventory."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def whenPresent : LinguisticExample :=
  { id := "declerck1991_whenPresent"
    source := ⟨"declerck-1991-grammar", "ch. 2 §1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You will have to tell him (the news) when he comes home."
    discourseSegments := []
    glossedTokens := []
    translation := "You will have to tell him (the news) when he comes home."
    context := "Declerck's example of adverbial time clause with present-tense morphology referring to future. `when he comes home` uses present `comes` despite future reference — typical of when-/before-/after-clauses with future reference."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Declerck 1991 ch. 2 §1. Compare `He didn't tell me when he will come home` where `when` introduces a noun clause and `will` is allowed."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def perfectHaveCome : LinguisticExample :=
  { id := "declerck1991_perfectHaveCome"
    source := ⟨"declerck-1991-grammar", "ch. 2 §2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have come here."
    discourseSegments := []
    glossedTokens := []
    translation := "I have come here."
    context := "Declerck's basic present perfect example. The coming event is in the pre-present sector; the reference frame is present (R = P at TU). Contrasts with a past-tense counterpart that would locate the event in the past time-sphere proper."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Declerck 1991 ch. 2 §2. Present perfect listed alongside present, past, future, conditional, past perfect, future perfect, conditional perfect in the tense inventory."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def perfectOverslept : LinguisticExample :=
  { id := "declerck1991_perfectOverslept"
    source := ⟨"declerck-1991-grammar", "ch. 3 fn 49"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I have overslept this morning."
    discourseSegments := []
    glossedTokens := []
    translation := "I have overslept this morning."
    context := "Declerck's example showing the present-perfect time-sphere effect: `I have overslept this morning` REQUIRES that the morning is not yet over (present time-sphere). Its preterit counterpart `I overslept this morning` does NOT require that — the speaker treats the situation as detached from now."
    judgment := .acceptable
    alternatives := [("I overslept this morning.", .acceptable)]
    readings := []
    paperFeatures := []
    comment := "Declerck 1991 ch. 3 fn 49. Cornerstone perfect-vs-preterit minimal pair demonstrating the time-sphere distinction. Both can refer to the same objective event; the difference is conceptualization."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [domainShift1a, domainShift1b, domainShift3a, modalPastWish, modalPastIfWas, futurePerfect, whenPresent, perfectHaveCome, perfectOverslept]

end Declerck1991.Examples
