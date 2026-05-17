import Linglib.Data.Examples.Schema
import Linglib.Core.Time.Reichenbach
import Linglib.Core.Time.Boundedness

/-!
# @cite{declerck-1991}: Tense and the Present/Past Time-Sphere
@cite{declerck-1991}

Declerck's *A Comprehensive Descriptive Grammar of English* (1991)
organizes English tense around two **time-spheres** (past vs present)
and the **pre-present, present, post-present** sectors of the present
time-sphere. Relative tenses (e.g. past perfect, conditional) lie
within an established **temporal domain** anchored by an absolute
tense; domain **shift** introduces a fresh absolute anchor. Declerck
also introduces the FPS/PPS distinction (Future / Present Perspective
System) for conditionals.

This file covers Declerck's tense + aspect sections:

- §23: Temporal domain — subordination vs shift
- §24: Modal (false) past — politeness and tentativeness
- §25: PPS vs FPS in conditionals
- §26: Temporal conjunctions and the future-perfect / when-clause
  family
- §27: PUTI — bounded/unbounded default temporal interpretation
- §28: Present perfect vs preterit — the time-sphere distinction

## What's been verified

Declerck's framework (time-spheres, PPS/FPS terminology, modal-past
diagnostics, domain shift / subordination contrast) is taken
directly from the book and faithfully reproduced. The Reichenbach
frames below encode project-side analytical takes on the structural
patterns Declerck describes; many of the literal example sentences
in the frame docstrings are project paraphrases, not verbatim
Declerck examples. The verified Declerck example sentences live in
the JSON block below (extracted from the 1991 book via Zotero MCP
fulltext).

-/

namespace Phenomena.TenseAspect.Studies.Declerck1991

open Core.Time.Reichenbach
open Data.Examples (LinguisticExample)

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/Declerck1991.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
open Data.Examples

def domainShift1a : LinguisticExample :=
  { id := "declerck1991_domainShift1a"
    source := ⟨"declerck-1991", "ch. 3 ex (1a)"⟩
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
    source := ⟨"declerck-1991", "ch. 3 ex (1b)"⟩
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
    source := ⟨"declerck-1991", "ch. 3 ex (3a)"⟩
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
    source := ⟨"declerck-1991", "ch. 2 §3"⟩
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
    source := ⟨"declerck-1991", "ch. 2 §3"⟩
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
    comment := "Declerck 1991 ch. 2 §3. Modal past in conditional protasis — the reference is non-past despite past morphology. Compare Iatridou 2000 fake-past analysis (Phenomena/Conditionals/Studies/Iatridou2000.lean)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def futurePerfect : LinguisticExample :=
  { id := "declerck1991_futurePerfect"
    source := ⟨"declerck-1991", "ch. 2 §2"⟩
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
    source := ⟨"declerck-1991", "ch. 2 §1"⟩
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
    source := ⟨"declerck-1991", "ch. 2 §2"⟩
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
    source := ⟨"declerck-1991", "ch. 3 fn 49"⟩
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

end Examples
-- END GENERATED EXAMPLES


-- ════════════════════════════════════════════════════════════════
-- § §23 — Temporal Domain: Shift vs Subordination
-- ════════════════════════════════════════════════════════════════

/-! Declerck (ch. 3 §C): a stretch of discourse may either incorporate
    each new clause into an existing temporal domain (relative tenses
    expressing anteriority, simultaneity, posteriority), or shift to
    a new absolute domain. The frames below illustrate the structural
    contrast: subordination keeps the perspective on the existing
    domain anchor; shift resets the perspective to S.

    See `Examples.domainShift1a` (subordination) and
    `Examples.domainShift1b` (shift) for verified
    Declerck examples. -/

/-- "He left..." — past domain anchor (subordination pair). -/
def domainSubordLeft : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -5
  eventTime := -5

/-- "...and would never come back" — relative tense within the
    past domain established by `left`. -/
def domainSubordWouldReturn : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -5
  referenceTime := -3
  eventTime := -3

/-- "He left..." — independent past domain (shift pair). -/
def domainShiftLeft : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -5
  eventTime := -5

/-- "...and never came back" — independent past domain. -/
def domainShiftCameBack : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- Both `left` frames are past (R < P). -/
theorem domainSubordLeftPast :
    domainSubordLeft.referenceTime < domainSubordLeft.perspectiveTime := by decide

theorem domainShiftLeftPast :
    domainShiftLeft.referenceTime < domainShiftLeft.perspectiveTime := by decide

/-- Subordination: `wouldReturn` is posterior within the domain. -/
theorem domainSubordPosteriority :
    domainSubordWouldReturn.referenceTime > domainSubordLeft.eventTime := by decide

/-- Shift: both frames have P = S (absolute perspective). -/
theorem domainShiftBothAbsolute :
    domainShiftLeft.perspectiveTime = domainShiftLeft.speechTime ∧
    domainShiftCameBack.perspectiveTime = domainShiftCameBack.speechTime :=
  ⟨rfl, rfl⟩

/-- Subordination: `wouldReturn` has shifted perspective. -/
theorem domainSubordShiftedPerspective :
    domainSubordWouldReturn.perspectiveTime ≠ domainSubordWouldReturn.speechTime := by
  decide


-- ════════════════════════════════════════════════════════════════
-- § §24 — Modal (False) Past: Politeness and Tentativeness
-- ════════════════════════════════════════════════════════════════

/-! Declerck (ch. 2 §3): some uses of the past tense have non-past
    reference. The past morphology marks modal distance (politeness,
    tentativeness, hypotheticality) rather than past temporal
    location.

    See `Examples.modalPastWish` and `Examples.modalPastIfWas` for
    verified examples. -/

/-- "I wanted to ask you something." — modal past.
    Past morphology, present-time reference (the wanting is now). -/
def falsePastWanted : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0
  eventTime := 0

/-- "Could you help me?" — modal past in a modal verb.
    Past form `could`, present-time request. -/
def falsePastCould : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0
  eventTime := 0


-- ════════════════════════════════════════════════════════════════
-- § §25 — PPS vs FPS in Conditionals
-- ════════════════════════════════════════════════════════════════

/-! Declerck distinguishes the **Present Perspective System** (PPS)
    and **Future Perspective System** (FPS) for conditional
    constructions. The two systems differ in how the if-clause and
    matrix tense forms anchor the temporal location of the conditional
    situations.

    The frames below encode the project-side analytical structure;
    specific Declerck example sentences for the four PPS/FPS-
    diagnostic positions were not directly extracted from the book.
    Consumers should treat the frames as structural illustrations
    rather than verbatim Declerck examples. -/

/-- PPS if-clause: "If he comes home..." — present tense in protasis. -/
def ppsIfComes : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0
  eventTime := 0

/-- PPS matrix: "...he will be happy." — will-future in apodosis. -/
def ppsWillBeHappy : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 3
  eventTime := 3

/-- FPS if-clause: "If he will go..." — will-form in protasis (FPS). -/
def fpsIfWillGo : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 3
  eventTime := 3

/-- FPS matrix: "...he should publish." — modal-present in apodosis. -/
def fpsShouldPublish : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0
  eventTime := 0

/-- PPS pattern: present in protasis, future in apodosis. -/
theorem ppsProtasisPresentApodosisFuture :
    ppsIfComes.isPresent ∧ ppsWillBeHappy.isFuture := by
  refine ⟨rfl, ?_⟩
  simp only [ReichenbachFrame.isFuture, ppsWillBeHappy]; omega

/-- FPS pattern: future in protasis, present in apodosis (reversed). -/
theorem fpsProtasisFutureApodosisPresent :
    fpsIfWillGo.isFuture ∧ fpsShouldPublish.isPresent := by
  refine ⟨?_, rfl⟩
  simp only [ReichenbachFrame.isFuture, fpsIfWillGo]; omega

/-- The PPS/FPS distinction is structural: the if-clause vs apodosis
    tense pattern reverses between systems. -/
theorem ppsFpsReversed :
    (ppsIfComes.referenceTime = ppsIfComes.perspectiveTime ∧
     ppsWillBeHappy.referenceTime > ppsWillBeHappy.perspectiveTime) ∧
    (fpsIfWillGo.referenceTime > fpsIfWillGo.perspectiveTime ∧
     fpsShouldPublish.referenceTime = fpsShouldPublish.perspectiveTime) := by
  refine ⟨⟨rfl, ?_⟩, ⟨?_, rfl⟩⟩ <;> decide


-- ════════════════════════════════════════════════════════════════
-- § §26 — Temporal Conjunctions with Implicit TOs
-- ════════════════════════════════════════════════════════════════

/-! Declerck (ch. 2 §1, §2): when-, before-, and after-clauses with
    future reference often use present-tense morphology rather than
    will-future. The future-perfect form encodes an event anterior
    to a future reference point. The past-perfect form encodes an
    event anterior to a past reference point.

    See `Examples.futurePerfect` and `Examples.whenPresent` for
    verified examples. -/

/-- "I will have left by then" — future perfect.
    Event before a future reference point (R > P, E < R). -/
def futPerfLeft : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 3
  eventTime := 2

/-- "...when he comes" — present-tense in temporal clause with
    future reference. R = present (= TO at speech time), but the
    pragmatic interpretation locates the event in the future. -/
def whenArrives : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 3
  eventTime := 3

/-- "I had left before he arrived" — past perfect.
    Event anterior to a past reference point. -/
def hadLeftBefore : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -5

/-- "...before he arrived" — past time-sphere reference point. -/
def beforeArrived : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- Before-clause: leaving before arrival (E_had_left < E_arrived). -/
theorem beforeLeavingBeforeArrival :
    hadLeftBefore.eventTime < beforeArrived.eventTime := by decide

/-- Past perfect frame has E < R (perfect aspect). -/
theorem hadLeftIsPerfect :
    hadLeftBefore.isPerfect := by
  simp only [ReichenbachFrame.isPerfect, hadLeftBefore]; omega


-- ════════════════════════════════════════════════════════════════
-- § §27 — PUTI: Bounded / Unbounded Default Interpretation
-- ════════════════════════════════════════════════════════════════

/-! Declerck (ch. 3 §1.2) distinguishes **bounded** vs **unbounded**
    sentences: a sentence is bounded if it represents a situation as
    reaching a terminal point, and unbounded otherwise. The contrast
    is sentence-level (not lexical) and distinct from the
    telic/atelic Aktionsart distinction (compare *Bill ran five
    miles* — bounded — with *Bill was running five miles* —
    unbounded; same telic VP, different boundedness).

    The "Principle of Unmarked Temporal Interpretation" (PUTI) is
    the project's name for Declerck's discussion of default temporal
    arrangements when two situations of given boundedness types are
    juxtaposed:
    - bounded + bounded → sequential (iconic) ordering;
    - unbounded + unbounded → simultaneity;
    - mixed → temporal inclusion of the bounded inside the unbounded.

    These are pragmatic defaults, not logical entailments — the
    frames below illustrate the construction; the per-pair ordering
    theorems verify that the constructed frames satisfy the default.

    Frames below use plain `ReichenbachFrame ℤ` and record
    boundedness in prose. Boundedness characterizes the predicate-
    over-interval, not the (S,P,R,E) frame, so the two are kept
    orthogonal; consumers needing the boundedness label use
    `SituationBoundedness` at use site.

    Verified Declerck examples in the JSON above:
    `declerck1991_domainShift_1a` (unbounded simultaneity) and
    `declerck1991_domainShift_1b` (bounded sequential). For the
    bounded/unbounded contrast itself, Declerck's textbook examples
    include *John read the letter.* (bounded) vs *John was reading a
    letter.* (unbounded) and *John drank whisky.* (unbounded) vs
    *John drank five glasses of whisky.* (bounded). -/

open Core.Time (SituationBoundedness)

/-- "He arrived." — bounded (achievement). -/
def arrivedFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -5
  eventTime := -5

/-- "He sat down." — bounded (achievement). After arriving, by PUTI default. -/
def satDownFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -4
  eventTime := -4

/-- "It was raining." — unbounded (state/activity). -/
def rainingFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- "The wind was blowing." — unbounded (activity), simultaneous with
    raining by PUTI default. -/
def windBlowingFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- "He was reading." — unbounded (activity). Frame for the mixed-inclusion case. -/
def readingFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- "The phone rang." — bounded (achievement), included in reading
    interval by PUTI default. -/
def phoneRangFrame : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- Bounded + bounded → sequential: arrival precedes sitting in the
    constructed frames (illustration of Declerck's domain-shift case
    with iconic ordering). -/
theorem boundedSequential :
    arrivedFrame.eventTime < satDownFrame.eventTime := by decide

/-- Unbounded + unbounded → simultaneous: raining and wind-blowing share
    an event time in the constructed frames. -/
theorem unboundedSimultaneous :
    rainingFrame.eventTime = windBlowingFrame.eventTime := rfl

/-- Mixed bounded + unbounded → temporal inclusion: phone ringing
    falls within reading in the constructed frames. -/
theorem mixedInclusion :
    phoneRangFrame.eventTime = readingFrame.eventTime := rfl


-- ════════════════════════════════════════════════════════════════
-- § §28 — Present Perfect vs Preterit: Time-Sphere
-- ════════════════════════════════════════════════════════════════

/-! Declerck's distinctive claim: the present perfect and preterit
    differ *not* in definiteness or current relevance but in
    time-sphere membership. Both can refer to the same objective
    event; what differs is the speaker's conceptualization (whether
    the situation is anchored to the present time-sphere or detached
    from it).

    Declerck's minimal pair (book fn 49): `I have overslept this
    morning` requires that the morning is not yet over (present
    time-sphere); `I overslept this morning` does not (past time-
    sphere). See `Examples.perfectOverslept`. -/

/-- "I have overslept this morning." — present perfect.
    Pre-present sector: E < R and R = P (present time-sphere).
    The morning must not yet be over. -/
def perfectOverslept : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0
  eventTime := -3

/-- "I overslept this morning." — simple preterit.
    Past time-sphere: E = R < P. The morning may be over. -/
def preteritOverslept : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- Both frames locate the event before speech time. -/
theorem perfectPreteritBothEventBeforeSpeech :
    perfectOverslept.eventTime < perfectOverslept.speechTime ∧
    preteritOverslept.eventTime < preteritOverslept.speechTime := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Same event time — the difference is structural, not temporal. -/
theorem perfectPreteritSameEventTime :
    perfectOverslept.eventTime = preteritOverslept.eventTime := rfl

/-- Present perfect: E < R (perfect aspect, pre-present). -/
theorem perfectIsPerfect :
    perfectOverslept.isPerfect := by
  simp only [ReichenbachFrame.isPerfect, perfectOverslept]; omega

/-- Present perfect: R = P (present orientation). -/
theorem perfectIsPresent :
    perfectOverslept.isPresent := rfl

/-- Preterit: R < P (past orientation). -/
theorem preteritIsPast :
    preteritOverslept.isPast := by
  simp only [ReichenbachFrame.isPast, preteritOverslept]; omega

/-- Preterit is perfective (E = R). -/
theorem preteritIsPerfective :
    preteritOverslept.isPerfective := rfl

end Phenomena.TenseAspect.Studies.Declerck1991
