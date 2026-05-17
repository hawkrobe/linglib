import Linglib.Data.Examples.Schema
import Linglib.Core.Time.Reichenbach
import Linglib.Core.Time.Boundedness
import Linglib.Theories.Semantics.Tense.Basic

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
open Semantics.Tense (shiftedFrame)
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
-- § TO-chain architecture (substrate; previously Tense/TOChain.lean)
-- ════════════════════════════════════════════════════════════════

namespace TOChain

open Core.Time (Relation Domain NamedTO TO Orientation)
open Core.Time.Reichenbach (ReichenbachFrame)


-- ════════════════════════════════════════════════════════════════
-- § Time-Spheres
-- ════════════════════════════════════════════════════════════════

/-- The two time-spheres of English (@cite{declerck-1991}, @cite{declerck-2006}).

    The tense system partitions linguistic time into two spheres:
    - **past**: wholly before t₀, containing the preterit, past perfect,
      conditional, and conditional perfect
    - **present**: includes t₀, containing the present, present perfect,
      future, and future perfect

    This is a conceptual partition, not a temporal relation: both "I visited
    Paris" and "I have visited Paris" can refer to the same objective event,
    but differ in time-sphere membership. -/
inductive TimeSphere where
  | past     -- wholly before t₀
  | present  -- includes t₀
  deriving DecidableEq, Repr


-- ════════════════════════════════════════════════════════════════
-- § TO-Chain Architecture
-- ════════════════════════════════════════════════════════════════

/-- A single link in a TO chain: a `Core.Time.Orientation`-labelled
    Time of Orientation related to the next TO inward by a temporal
    relation.

    Example: in the past perfect schema `TS simul TO_sit before TO₂ before TO₁`,
    the link for TO₂ is `⟨.sub 0, .before, t₂⟩` — meaning TO₂ (= `.sub 0`,
    one step out from the binding TO₁ = `.perspective`) stands in the
    `before` relation to the next TO outward. The `.situation` role
    labels TO_sit. -/
structure TOLink (Time : Type*) where
  /-- The orientation-time role of this link (`.situation` for TO_sit;
      `.sub n` for an intermediate TO). -/
  name : Orientation
  /-- How this TO relates to the next TO inward toward TO₁.
      `before` = this TO precedes the next; `after` = this TO follows it;
      `overlapping` = simultaneous. -/
  relation : Relation
  /-- The resolved time value. -/
  time : Time

/-- Declerck's tense schema: a chain of TOs from TO₁ outward to TO_sit,
    with a time-sphere classification.

    The `chain` runs from TO₁ (innermost, adjacent to t₀) outward through
    intermediate TOs to TO_sit. The situation time TS is always simultaneous
    with TO_sit (Declerck's universal principle: every tense represents TS
    as coinciding with some TO), so there is no separate `ts` field — both
    E and R in the Reichenbach projection are derived from TO_sit.

    The chain captures only adjacent relations. Non-adjacent TOs (e.g.,
    TO_sit and TO₁ in the conditional tense) have no asserted relation —
    this is Declerck's account of temporal vagueness. -/
structure DeclercianSchema (Time : Type*) where
  /-- Temporal zero-point (usually = speech time) -/
  t0 : Time
  /-- Basic TO (TO₁): the starting point for temporal relations.
      Usually = t₀, but can be a future or past time in embedded contexts. -/
  to1 : Time
  /-- Chain of TOs from TO₁ outward. Each link's `relation` connects it
      to the previous link (or to TO₁ for the first link). The last element
      is TO_sit, which TS is simultaneous with. -/
  chain : List (TOLink Time)
  /-- Which time-sphere the tense belongs to -/
  timeSphere : TimeSphere

/-- The situation-TO (= TS): the TO with which the situation time coincides.
    This is the last element of the chain, or TO₁ if the chain is empty. -/
def DeclercianSchema.toSit {Time : Type*} (s : DeclercianSchema Time) : Time :=
  match s.chain.getLast? with
  | some link => link.time
  | none => s.to1

/-- Number of TOs in the schema (including TO₁). -/
def DeclercianSchema.depth {Time : Type*} (s : DeclercianSchema Time) : ℕ :=
  s.chain.length + 1


-- ════════════════════════════════════════════════════════════════
-- § Projection to ReichenbachFrame
-- ════════════════════════════════════════════════════════════════

/-- Project a Declercian schema to a Reichenbach frame.

    The mapping:
    - S = t₀
    - P = TO₁ (basic TO = perspective time)
    - R = TO_sit (situation-TO)
    - E = TO_sit (= TS, by Declerck's universal principle TS = TO_sit)

    Since R = E = TO_sit, every Declercian frame has `isPerfective` (E = R)
    and can never satisfy `isPerfect` (E < R). The "perfect" in Declerck's
    system is a chain property (TO_sit before TO₂), not an E/R relation.

    This is a lossy projection: the chain structure (intermediate TOs,
    temporal vagueness) is collapsed. -/
def DeclercianSchema.toFrame {Time : Type*}
    (s : DeclercianSchema Time) : ReichenbachFrame Time where
  speechTime := s.t0
  perspectiveTime := s.to1
  referenceTime := s.toSit
  eventTime := s.toSit

/-- Every Declercian frame has E = R (Declerck's TS = TO_sit principle). -/
theorem DeclercianSchema.eventTime_eq_refTime {Time : Type*}
    (s : DeclercianSchema Time) :
    s.toFrame.eventTime = s.toFrame.referenceTime := rfl


-- ════════════════════════════════════════════════════════════════
-- § The Eight English Tense Schemata
-- ════════════════════════════════════════════════════════════════

/-! Each schema is parameterized by concrete times so that bridge
    theorems can verify the structural relations. -/

section Schemata

variable {Time : Type*} [LinearOrder Time]

/-- **Preterit**: TS simul TO_sit, TO_sit before TO₁.
    Past time-sphere. Two TOs in the chain.

    Example: "John was ill yesterday."
    - TO₁ = t₀ (absolute use)
    - TO_sit before TO₁ (past time-sphere)
    - TS = TO_sit -/
def preterit (t0 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.situation, .before, toSit⟩]
  timeSphere := .past

/-- **Present tense**: TS simul TO_sit, TO_sit includes t₀.
    Present time-sphere. Two TOs in the chain.

    Declerck's key insight: the present tense does NOT assert `TO_sit = t₀`
    but rather `TO_sit includes t₀`. For point times this degenerates to
    equality (captured by `.overlapping`), but for intervals "John is in
    London today" has TO_sit = today, which properly includes t₀. The
    interval-level inclusion is handled by `Interval.subinterval`.

    Example: "John is in London."
    - TO_sit includes t₀ (= overlapping for point times)
    - TS = TO_sit -/
def present (t0 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.situation, .overlapping, toSit⟩]
  timeSphere := .present

/-- **Present perfect**: TS simul TO_sit, TO_sit before TO₁.
    Present time-sphere (the crucial difference from the preterit).

    Declerck's distinctive claim: the present perfect and preterit differ
    in time-sphere membership, not in definiteness or current relevance.
    Both can refer to the same event; the perfect places it in the
    pre-present sector of the present time-sphere.

    Example: "I have visited Paris."
    - TO₁ = t₀
    - TO_sit before TO₁ (pre-present sector)
    - TS = TO_sit
    - Present time-sphere (vs. past for the preterit) -/
def presentPerfect (t0 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.situation, .before, toSit⟩]
  timeSphere := .present

/-- **Past perfect**: TS simul TO_sit, TO_sit before TO₂, TO₂ before TO₁.
    Past time-sphere. Three TOs in the chain.

    The past perfect is either "the past of the preterit" or "the past of the
    present perfect." In both cases TO₂ lies in the past time-sphere relative
    to TO₁, and TO_sit is anterior to TO₂.

    Example: "John had left before we arrived."
    - TO₁ = t₀
    - TO₂ before TO₁ (past time-sphere)
    - TO_sit before TO₂ (anterior to the past reference)
    - TS = TO_sit -/
def pastPerfect (t0 to2 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.sub 0, .before, to2⟩, ⟨.situation, .before, toSit⟩]
  timeSphere := .past

/-- **Future tense**: TS simul TO_sit, TO_sit after TO₁.
    Present time-sphere. Two TOs in the chain.

    The future locates TO_sit either wholly after t₀ or from t₀ onwards.
    For point times, `after` suffices.

    Example: "I will do it next week."
    - TO₁ = t₀
    - TO_sit after TO₁ (post-present sector)
    - TS = TO_sit -/
def future (t0 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.situation, .after, toSit⟩]
  timeSphere := .present

/-- **Future perfect**: TS simul TO_sit, TO_sit before TO₂, TO₂ after TO₁.
    Present time-sphere. Three TOs in the chain.

    The future perfect is vague about the relation between TO_sit and TO₁:
    John may have already left, may be leaving now, or may leave later.
    The chain captures this by NOT asserting a TO_sit–TO₁ relation.

    Example: "John will have left when we arrive."
    - TO₁ = t₀
    - TO₂ after TO₁ (future reference point)
    - TO_sit before TO₂ (anterior to the future reference)
    - TS = TO_sit -/
def futurePerfect (t0 to2 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.sub 0, .after, to2⟩, ⟨.situation, .before, toSit⟩]
  timeSphere := .present

/-- **Conditional tense**: TS simul TO_sit, TO_sit after TO₂, TO₂ before TO₁.
    Past time-sphere (for TO₂). Three TOs in the chain.

    The conditional is the mirror image of the future perfect: "future in
    the past." Like the future perfect, it is vague about TO_sit's relation
    to TO₁ — the situation may or may not have occurred by speech time.

    Example: "The house would weather many more storms."
    - TO₁ = t₀
    - TO₂ before TO₁ (past time-sphere)
    - TO_sit after TO₂ (posterior within the past domain)
    - TS = TO_sit -/
def conditional (t0 to2 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.sub 0, .before, to2⟩, ⟨.situation, .after, toSit⟩]
  timeSphere := .past

/-- **Conditional perfect**: TS simul TO_sit, TO_sit before TO₃,
    TO₃ after TO₂, TO₂ before TO₁. Past time-sphere. Four TOs in the chain.

    The most intricate English tense: "past in the future in the past."

    Example: "He would have left by then."
    - TO₁ = t₀
    - TO₂ before TO₁ (past time-sphere)
    - TO₃ after TO₂ (future within the past domain)
    - TO_sit before TO₃ (anterior to the future-in-past reference)
    - TS = TO_sit -/
def conditionalPerfect (t0 to2 to3 toSit : Time) : DeclercianSchema Time where
  t0 := t0
  to1 := t0
  chain := [⟨.sub 0, .before, to2⟩, ⟨.sub 1, .after, to3⟩, ⟨.situation, .before, toSit⟩]
  timeSphere := .past

end Schemata


-- ════════════════════════════════════════════════════════════════
-- § Chain Depth Theorems
-- ════════════════════════════════════════════════════════════════

section Depth

variable {Time : Type*}

/-- Simple tenses have depth 2 (TO₁ + TO_sit). -/
theorem preterit_depth (t0 toSit : Time) :
    (preterit t0 toSit).depth = 2 := rfl

theorem present_depth (t0 toSit : Time) :
    (present t0 toSit).depth = 2 := rfl

theorem presentPerfect_depth (t0 toSit : Time) :
    (presentPerfect t0 toSit).depth = 2 := rfl

theorem future_depth (t0 toSit : Time) :
    (future t0 toSit).depth = 2 := rfl

/-- Compound tenses have depth 3 (TO₁ + TO₂ + TO_sit). -/
theorem pastPerfect_depth (t0 to2 toSit : Time) :
    (pastPerfect t0 to2 toSit).depth = 3 := rfl

theorem futurePerfect_depth (t0 to2 toSit : Time) :
    (futurePerfect t0 to2 toSit).depth = 3 := rfl

theorem conditional_depth (t0 to2 toSit : Time) :
    (conditional t0 to2 toSit).depth = 3 := rfl

/-- The conditional perfect has depth 4 (TO₁ + TO₂ + TO₃ + TO_sit). -/
theorem conditionalPerfect_depth (t0 to2 to3 toSit : Time) :
    (conditionalPerfect t0 to2 to3 toSit).depth = 4 := rfl

end Depth


-- ════════════════════════════════════════════════════════════════
-- § Time-Sphere Classification
-- ════════════════════════════════════════════════════════════════

section TimeSphereClassification

variable {Time : Type*}

/-- Present time-sphere tenses: present, present perfect, future, future perfect. -/
theorem present_sphere (t0 toSit : Time) :
    (present t0 toSit).timeSphere = .present := rfl

theorem presentPerfect_sphere (t0 toSit : Time) :
    (presentPerfect t0 toSit).timeSphere = .present := rfl

theorem future_sphere (t0 toSit : Time) :
    (future t0 toSit).timeSphere = .present := rfl

theorem futurePerfect_sphere (t0 to2 toSit : Time) :
    (futurePerfect t0 to2 toSit).timeSphere = .present := rfl

/-- Past time-sphere tenses: preterit, past perfect, conditional, conditional perfect. -/
theorem preterit_sphere (t0 toSit : Time) :
    (preterit t0 toSit).timeSphere = .past := rfl

theorem pastPerfect_sphere (t0 to2 toSit : Time) :
    (pastPerfect t0 to2 toSit).timeSphere = .past := rfl

theorem conditional_sphere (t0 to2 toSit : Time) :
    (conditional t0 to2 toSit).timeSphere = .past := rfl

theorem conditionalPerfect_sphere (t0 to2 to3 toSit : Time) :
    (conditionalPerfect t0 to2 to3 toSit).timeSphere = .past := rfl

end TimeSphereClassification


-- ════════════════════════════════════════════════════════════════
-- § Bridge Theorems: Declercian Schema → Reichenbach Frame
-- ════════════════════════════════════════════════════════════════

/-! Each bridge theorem shows that a Declercian schema, when resolved to
    concrete times satisfying the chain constraints, projects to a
    `ReichenbachFrame` satisfying the expected Reichenbach tense predicate.

    This connects Declerck's chain architecture to the existing Reichenbach
    infrastructure used by all other tense theories in linglib. -/

section Bridge

/-- Preterit projects to a frame satisfying PAST (R < P). -/
theorem preterit_isPast (t0 toSit : ℤ) (h : toSit < t0) :
    (preterit t0 toSit).toFrame.isPast := by
  simp [preterit, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isPast]
  exact h

/-- Present projects to a frame satisfying PRESENT (R = P) for point times. -/
theorem present_isPresent (t0 : ℤ) :
    (present t0 t0).toFrame.isPresent := by
  simp [present, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isPresent]

/-- Present perfect projects to a frame satisfying PAST (R < P) —
    because TO_sit (= R) < TO₁ (= P). The present-sphere membership is
    tracked by `timeSphere`, not by the Reichenbach R/P relation.

    This is Declerck's key structural claim: the perfect/preterit distinction
    is time-sphere, not R/P configuration. Both project to R < P. -/
theorem presentPerfect_frame_isPast (t0 toSit : ℤ) (h : toSit < t0) :
    (presentPerfect t0 toSit).toFrame.isPast := by
  simp [presentPerfect, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isPast]
  exact h

/-- Preterit and present perfect produce identical Reichenbach frames for
    the same times — they differ ONLY in time-sphere. This is Declerck's
    central thesis about the perfect/preterit distinction: the contrast
    is sphere membership, not R/P configuration. -/
theorem preterit_presentPerfect_same_frame (t0 toSit : ℤ) :
    (preterit t0 toSit).toFrame = (presentPerfect t0 toSit).toFrame := by
  simp [preterit, presentPerfect, DeclercianSchema.toFrame, DeclercianSchema.toSit]

/--... but they differ in time-sphere. -/
theorem preterit_presentPerfect_differ_sphere (t0 toSit : ℤ) :
    (preterit t0 toSit).timeSphere ≠ (presentPerfect t0 toSit).timeSphere := by
  simp [preterit, presentPerfect]

/-- Past perfect projects to PAST (R < P). The chain gives
    TO_sit < TO₂ < TO₁, so R (= TO_sit) < P (= TO₁). -/
theorem pastPerfect_isPast (t0 to2 toSit : ℤ)
    (h₁ : toSit < to2) (h₂ : to2 < t0) :
    (pastPerfect t0 to2 toSit).toFrame.isPast := by
  simp [pastPerfect, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isPast]
  omega

/-- Future projects to FUTURE (R > P). -/
theorem future_isFuture (t0 toSit : ℤ) (h : toSit > t0) :
    (future t0 toSit).toFrame.isFuture := by
  simp [future, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isFuture]
  exact h

/-- Conditional: TO₂ < TO₁ projects to PAST for the intermediate reference.
    The full frame has R (= TO_sit) related to P (= TO₁), but the relation
    is underspecified — TO_sit may be before, at, or after TO₁.

    We can only prove that TO₂ < TO₁ (the chain constraint), which Reichenbach
    would misrepresent as three separate tense schemata. -/
theorem conditional_to2_before_to1 (t0 to2 toSit : ℤ) (h : to2 < t0) :
    to2 < (conditional t0 to2 toSit).to1 := by
  simp [conditional]; exact h

end Bridge


-- ════════════════════════════════════════════════════════════════
-- § Temporal Vagueness
-- ════════════════════════════════════════════════════════════════

/-! Declerck's chain model captures temporal vagueness naturally:
    when a schema's chain doesn't include a direct link between two
    TOs, their relation is genuinely unspecified.

    The future perfect and conditional tense are both vague about
    the relation between TO_sit and TO₁. @cite{reichenbach-1947}
    incorrectly treats this as three-way ambiguity (S–R–E, R–S–E,
    R–E–S as distinct schemata for the conditional). -/

/-- The future perfect is vague about TO_sit's relation to t₀:
    the chain relates TO_sit to TO₂ and TO₂ to TO₁, but NOT
    TO_sit to TO₁. All three scenarios are consistent. -/
theorem futurePerfect_vague_sit_t0 :
    ∃ (toSit₁ toSit₂ toSit₃ to2 : ℤ),
      -- TO₂ after TO₁ (= t₀ = 0) in all cases
      to2 > 0 ∧
      -- TO_sit before TO₂ in all cases
      toSit₁ < to2 ∧ toSit₂ < to2 ∧ toSit₃ < to2 ∧
      -- But TO_sit can be before, at, or after t₀
      toSit₁ < 0 ∧ toSit₂ = 0 ∧ toSit₃ > 0 := by
  exact ⟨-1, 0, 1, 5, by omega, by omega, by omega, by omega,
         by omega, rfl, by omega⟩

/-- The conditional tense is vague about TO_sit's relation to t₀:
    the chain relates TO_sit to TO₂ and TO₂ to TO₁, but NOT
    TO_sit to TO₁. All three scenarios are consistent.

    @cite{reichenbach-1947}'s three separate schemata for the conditional
    (S–R–E, R–S–E, R–E–S) are NOT distinct tenses — they are instances
    of a single vague schema. -/
theorem conditional_vague_sit_t0 :
    ∃ (toSit₁ toSit₂ toSit₃ to2 : ℤ),
      -- TO₂ before TO₁ (= t₀ = 0) in all cases
      to2 < 0 ∧
      -- TO_sit after TO₂ in all cases
      toSit₁ > to2 ∧ toSit₂ > to2 ∧ toSit₃ > to2 ∧
      -- But TO_sit can be before, at, or after t₀
      toSit₁ < 0 ∧ toSit₂ = 0 ∧ toSit₃ > 0 := by
  exact ⟨-1, 0, 1, -3, by omega, by omega, by omega, by omega,
         by omega, rfl, by omega⟩


-- ════════════════════════════════════════════════════════════════
-- § Concrete Instantiations (ℤ)
-- ════════════════════════════════════════════════════════════════

/-! Concrete examples matching the Phenomena/Tense/Data.lean frames,
    showing the Declercian schemata produce the same data. -/

/-- "John was ill yesterday" — preterit, absolute use. -/
def exPreterit : DeclercianSchema ℤ := preterit 0 (-3)

/-- "It is raining" — present, point time. -/
def exPresent : DeclercianSchema ℤ := present 0 0

/-- "I have visited Paris" — present perfect. -/
def exPresentPerfect : DeclercianSchema ℤ := presentPerfect 0 (-3)

/-- "I visited Paris" — preterit (same event, different sphere). -/
def exPreteritParis : DeclercianSchema ℤ := preterit 0 (-3)

/-- "John had left before we arrived" — past perfect. -/
def exPastPerfect : DeclercianSchema ℤ := pastPerfect 0 (-2) (-4)

/-- "I will do it next week" — future. -/
def exFuture : DeclercianSchema ℤ := future 0 5

/-- "John will have left when we arrive" — future perfect. -/
def exFuturePerfect : DeclercianSchema ℤ := futurePerfect 0 5 3

/-- "The house would weather many more storms" — conditional. -/
def exConditional : DeclercianSchema ℤ := conditional 0 (-5) (-3)

/-- "He would have left by then" — conditional perfect. -/
def exConditionalPerfect : DeclercianSchema ℤ := conditionalPerfect 0 (-5) (-3) (-4)


-- ── Concrete bridge verification ──

/-- Concrete preterit satisfies PAST. -/
theorem exPreterit_isPast : exPreterit.toFrame.isPast := by
  simp [exPreterit, preterit, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isPast]

/-- Concrete present satisfies PRESENT. -/
theorem exPresent_isPresent : exPresent.toFrame.isPresent := by
  simp [exPresent, present, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isPresent]

/-- Present perfect and preterit project to identical Reichenbach frames. -/
theorem exPerfect_eq_preterit_frame :
    exPresentPerfect.toFrame = exPreteritParis.toFrame := by
  simp [exPresentPerfect, exPreteritParis, presentPerfect, preterit,
        DeclercianSchema.toFrame, DeclercianSchema.toSit]

/-- But they have different time-spheres. -/
theorem exPerfect_neq_preterit_sphere :
    exPresentPerfect.timeSphere ≠ exPreteritParis.timeSphere := by
  simp only [exPresentPerfect, exPreteritParis, presentPerfect, preterit]; decide

/-- Concrete future satisfies FUTURE. -/
theorem exFuture_isFuture : exFuture.toFrame.isFuture := by
  simp [exFuture, future, DeclercianSchema.toFrame, DeclercianSchema.toSit,
        ReichenbachFrame.isFuture]

/-- Concrete future perfect: TO_sit (3) < TO₂ (5), and TO₂ (5) > t₀ (0). -/
theorem exFuturePerfect_chain_valid :
    (futurePerfect 0 5 3 : DeclercianSchema ℤ).toSit < 5 ∧ (5 : ℤ) > 0 := by
  simp [futurePerfect, DeclercianSchema.toSit]

/-- Concrete conditional: TO₂ (-5) < t₀ (0), TO_sit (-3) > TO₂ (-5). -/
theorem exConditional_chain_valid :
    (-5 : ℤ) < 0 ∧ exConditional.toSit > (-5 : ℤ) := by
  simp [exConditional, conditional, DeclercianSchema.toSit]

/-- Conditional perfect: 4-deep chain is valid. -/
theorem exConditionalPerfect_chain_valid :
    (-5 : ℤ) < 0 ∧ (-3 : ℤ) > (-5 : ℤ) ∧ exConditionalPerfect.toSit < (-3 : ℤ) := by
  simp [exConditionalPerfect, conditionalPerfect, DeclercianSchema.toSit]


-- ════════════════════════════════════════════════════════════════
-- § Tower Bridge: TO-Chain as Context Tower
-- ════════════════════════════════════════════════════════════════

/-!
### Declerck TO-Chain ↔ Context Tower

Each link in a TO-chain corresponds to a temporal shift in a context tower.
The chain runs from TO₁ outward to TO_sit; each link introduces a new temporal
perspective point, which is exactly what pushing a `temporalShift` does.

- TO₁ corresponds to the tower origin (the basic temporal reference point)
- Each subsequent TO in the chain maps to a tower push with `temporalShift`
- `DeclercianSchema.depth` = `chain.length + 1` corresponds to tower depth + 1
  (the tower counts shifts, while Declerck counts TOs including TO₁)

The mapping is `tower.depth = schema.chain.length`, and
`schema.depth = tower.depth + 1` (because Declerck counts TO₁ as depth 1).
-/

section TowerBridge

variable {Time : Type*}

open Core.Context (ContextTower ContextShift KContext)

/-- Convert a Declercian TO-chain to a list of temporal shifts.
    Each `TOLink` becomes a `temporalShift` with `.temporal` label.
    The relation in the link is not encoded in the shift itself —
    it is a constraint on the times, not a transformation. -/
def declercianToShifts {E P : Type*} (chain : List (TOLink Time)) :
    List (ContextShift (KContext Time E P Time)) :=
  chain.map λ link => {
    apply := λ c => { c with time := link.time }
    label := .temporal
  }

/-- Convert a Declercian schema to a context tower.
    The origin context has `time := to1` (the basic TO).
    Each chain link becomes a temporal shift. -/
def declercianToTower {E P : Type*}
    (s : DeclercianSchema Time) (agent addressee : E) (world : Time) (pos : P) :
    ContextTower (KContext Time E P Time) where
  origin := {
    agent := agent
    addressee := addressee
    world := world
    time := s.to1
    position := pos
  }
  shifts := declercianToShifts (E := E) (P := P) s.chain

/-- The tower depth equals the chain length. -/
theorem declercianToTower_depth {E P : Type*}
    (s : DeclercianSchema Time) (agent addr : E) (world : Time) (pos : P) :
    (declercianToTower (E := E) (P := P) s agent addr world pos).depth = s.chain.length := by
  simp only [declercianToTower, ContextTower.depth, declercianToShifts, List.length_map]

/-- Declerck's depth = tower depth + 1. The "+1" is because Declerck counts
    TO₁ as part of the depth (depth = number of TOs), while the tower counts
    only shifts (depth = number of pushes). -/
theorem declerck_depth_is_tower_depth_plus_one {E P : Type*}
    (s : DeclercianSchema Time) (agent addr : E) (world : Time) (pos : P) :
    s.depth = (declercianToTower (E := E) (P := P) s agent addr world pos).depth + 1 := by
  simp only [DeclercianSchema.depth, declercianToTower_depth]

/-- For simple tenses (chain length 1), the tower has depth 1. -/
theorem preterit_tower_depth (t0 toSit : Time) {E P : Type*}
    (agent addr : E) (world : Time) (pos : P) :
    (declercianToTower (E := E) (P := P) (preterit t0 toSit) agent addr world pos).depth = 1 := by
  simp only [declercianToTower, ContextTower.depth, declercianToShifts,
             preterit, List.length_map, List.length_cons, List.length_nil]

/-- For compound tenses (chain length 2), the tower has depth 2. -/
theorem pastPerfect_tower_depth (t0 to2 toSit : Time) {E P : Type*}
    (agent addr : E) (world : Time) (pos : P) :
    (declercianToTower (E := E) (P := P) (pastPerfect t0 to2 toSit)
      agent addr world pos).depth = 2 := by
  simp only [declercianToTower, ContextTower.depth, declercianToShifts,
             pastPerfect, List.length_map, List.length_cons, List.length_nil]

/-- For the conditional perfect (chain length 3), the tower has depth 3. -/
theorem conditionalPerfect_tower_depth (t0 to2 to3 toSit : Time) {E P : Type*}
    (agent addr : E) (world : Time) (pos : P) :
    (declercianToTower (E := E) (P := P) (conditionalPerfect t0 to2 to3 toSit)
      agent addr world pos).depth = 3 := by
  simp only [declercianToTower, ContextTower.depth, declercianToShifts,
             conditionalPerfect, List.length_map, List.length_cons, List.length_nil]

end TowerBridge

-- ════════════════════════════════════════════════════════════════
-- § Domain Bridge: TO-Chain as Core.Time.Domain
-- ════════════════════════════════════════════════════════════════

/-! Re-express `DeclercianSchema` via the framework-agnostic
    `Core.Time.Domain` substrate (central TO + list of sub-TOs, with
    Allen relations computed on demand from the underlying linear
    order). The `toDomain` builder lifts the chain structure into a
    `Domain Time Orientation` whose central TO is the utterance
    time (T₀) and whose sub-TOs are the perspective TO (TO₁) followed
    by every chain link as a point interval.

    This is **additive**: the `DeclercianSchema` structure and all the
    named-tense constructors stay unchanged. Domain-level tooling can
    now work uniformly with
    `s.toDomain.relatedByName precedesSet .situation .perspective`,
    while existing Reichenbach-projecting code continues to use
    `s.toFrame`. -/

section DomainBridge

variable {Time : Type*} [LinearOrder Time]

/-- The schema as a `Core.Time.Domain` over the universal
    `Orientation` role vocabulary: central = `.utterance` (T₀, the
    temporal zero-point), sub-TOs = `.perspective` (TO₁) followed by
    every chain link as a point interval.

    The Allen relations between any pair of TOs are **computed** from
    the underlying `LinearOrder Time` via `Interval.allenRel`; nothing
    is stored. The chain's `relation` field encodes the *intended*
    Declercian temporal relation but is not consulted here — its job is
    to constrain admissible time assignments at the call site, not to
    reproduce information already implicit in the linear order. -/
def DeclercianSchema.toDomain (s : DeclercianSchema Time) :
    Domain Time Orientation where
  central := NamedTO.ofPoint .utterance s.t0
  subTOs := NamedTO.ofPoint .perspective s.to1 ::
            s.chain.map (fun link => NamedTO.ofPoint link.name link.time)

@[simp] theorem DeclercianSchema.toDomain_central (s : DeclercianSchema Time) :
    s.toDomain.central = NamedTO.ofPoint .utterance s.t0 := rfl

@[simp] theorem DeclercianSchema.toDomain_subTOs (s : DeclercianSchema Time) :
    s.toDomain.subTOs = NamedTO.ofPoint .perspective s.to1 ::
      s.chain.map (fun link => NamedTO.ofPoint link.name link.time) := rfl

/-- The schema's domain labels: utterance first, then perspective, then
    every chain link's role. Useful for stating role-set invariants. -/
theorem DeclercianSchema.toDomain_labels (s : DeclercianSchema Time) :
    s.toDomain.labels =
      Orientation.utterance :: .perspective :: s.chain.map TOLink.name := by
  simp [DeclercianSchema.toDomain, Domain.labels, Domain.all,
        NamedTO.ofPoint, List.map_cons, List.map_map, Function.comp]

end DomainBridge

-- ════════════════════════════════════════════════════════════════
-- § Zone Classifier
-- ════════════════════════════════════════════════════════════════

/-! The `Zone` enum encodes Declerck's six principal temporal sectors
    — two time-spheres (`past`, `present`) crossed with three positions
    (anterior `pre-`, central, posterior `post-`). Each English tense
    locates its situation time in one of these zones. The
    `DeclercianSchema.zoneOf` classifier projects a schema to its zone
    based on `(timeSphere, last chain-link relation)` — the relation of
    `TO_sit` to its outer anchor, plus the sphere membership of that
    anchor.

    For **simple tenses** (chain length 1, anchor = `TO₁` = `t₀`):
    - `(past, before)` → `past` (preterit)
    - `(present, before)` → `prePresent` (present perfect)
    - `(present, overlapping)` → `present` (present)
    - `(present, after)` → `postPresent` (future)

    For **compound tenses** (chain length ≥ 2, anchor = `TO₂` etc.):
    - `(past, before)` → `prePast` (past perfect, conditional perfect)
    - `(past, after)` → `postPast` (conditional)
    - `(present, before)` → `prePresent` (future perfect's TO_sit, anterior)
    - `(present, after)` → `postPresent`

    The classifier is **not** the inverse of the chain — vague tenses
    (future perfect, conditional) under-determine `TO_sit`'s zone, and
    the classifier returns the zone of the immediate anchor. The
    `zone_of_*` `rfl`-theorems below verify each named tense classifies
    to its expected zone. -/

/-- The six principal Declercian zones: two time-spheres crossed with
    three sphere-internal positions. -/
inductive Zone where
  | prePast
  | past
  | postPast
  | prePresent
  | present
  | postPresent
  deriving DecidableEq, Repr

namespace DeclercianSchema

variable {Time : Type*}

/-- Classify a schema's TO_sit by zone, based on `(timeSphere, last
    chain link's relation)`. See the section docstring for the mapping.
    Defaults to the sphere's center for empty chains and odd cases. -/
def zoneOf (s : DeclercianSchema Time) : Zone :=
  let lastRel := (s.chain.getLast?).map TOLink.relation
  let nLinks := s.chain.length
  match s.timeSphere, nLinks, lastRel with
  | .past,    1, some .before      => .past         -- preterit
  | .past,    1, some .overlapping => .past
  | .past,    1, some .after       => .postPast
  | .present, 1, some .before      => .prePresent   -- present perfect
  | .present, 1, some .overlapping => .present      -- present
  | .present, 1, some .after       => .postPresent  -- future
  | .past,    _, some .before      => .prePast      -- past perfect, conditional perfect
  | .past,    _, some .overlapping => .past
  | .past,    _, some .after       => .postPast     -- conditional
  | .present, _, some .before      => .prePresent   -- future perfect (TO_sit before TO₂)
  | .present, _, some .overlapping => .present
  | .present, _, some .after       => .postPresent
  | .past,    _, _                 => .past
  | .present, _, _                 => .present

end DeclercianSchema

-- ── Per-tense zone theorems (each named English tense in its expected zone) ──

section ZoneClassification

variable {Time : Type*}

theorem preterit_zone (t0 toSit : Time) :
    (preterit t0 toSit).zoneOf = .past := rfl

theorem present_zone (t0 toSit : Time) :
    (present t0 toSit).zoneOf = .present := rfl

theorem presentPerfect_zone (t0 toSit : Time) :
    (presentPerfect t0 toSit).zoneOf = .prePresent := rfl

theorem future_zone (t0 toSit : Time) :
    (future t0 toSit).zoneOf = .postPresent := rfl

theorem pastPerfect_zone (t0 to2 toSit : Time) :
    (pastPerfect t0 to2 toSit).zoneOf = .prePast := rfl

theorem conditional_zone (t0 to2 toSit : Time) :
    (conditional t0 to2 toSit).zoneOf = .postPast := rfl

theorem futurePerfect_zone (t0 to2 toSit : Time) :
    (futurePerfect t0 to2 toSit).zoneOf = .prePresent := rfl

theorem conditionalPerfect_zone (t0 to2 to3 toSit : Time) :
    (conditionalPerfect t0 to2 to3 toSit).zoneOf = .prePast := rfl

end ZoneClassification

/-- Preterit and present perfect classify to **different zones** (`past`
    vs `prePresent`) despite projecting to identical Reichenbach frames
    (`preterit_presentPerfect_same_frame`). This is exactly Declerck's
    central claim about the perfect/preterit distinction: the difference
    lives in the time-sphere/zone, not in the underlying R/P
    configuration. The Zone classifier surfaces what `toFrame` flattens. -/
theorem preterit_presentPerfect_differ_zone {Time : Type*} (t0 toSit : Time) :
    (preterit t0 toSit).zoneOf ≠ (presentPerfect t0 toSit).zoneOf := by
  simp [preterit, presentPerfect, DeclercianSchema.zoneOf]

-- ════════════════════════════════════════════════════════════════
-- § TenseSystem and AspectSystem Instances
-- ════════════════════════════════════════════════════════════════

/-! Declerck's `DeclercianSchema` as a `Core.Time.TenseSystem`
    (anchor = `.perspective` for TO₁, situation = `.situation` for
    TO_sit) and `Core.Time.AspectSystem` instance. The aspect instance
    collapses event and reference roles both to `.situation` —
    Declerck's universal `TS = TO_sit` principle means E = R always
    holds, so any predicate of the form "event equals reference" is
    trivially satisfied for every Declercian schema, and "event
    precedes reference" can never hold. The "perfect" lives in the
    chain structure (TO_sit before `.sub 0`), not in the E/R relation
    — exactly Declerck's claim. -/

instance declercianSchema_tenseSystem {Time : Type*} [LinearOrder Time] :
    Core.Time.TenseSystem (DeclercianSchema Time) Time Orientation where
  toDomain := DeclercianSchema.toDomain
  anchor := .perspective
  situation := .situation

instance declercianSchema_aspectSystem {Time : Type*} [LinearOrder Time] :
    Core.Time.AspectSystem (DeclercianSchema Time) Time Orientation where
  toDomain := DeclercianSchema.toDomain
  event := .situation
  reference := .situation

end TOChain



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

/-- "...and would never come back" — relative tense within the past
    domain established by `left`. Constructed via `shiftedFrame` so
    the perspective is taken from `domainSubordLeft.eventTime`. -/
def domainSubordWouldReturn : ReichenbachFrame ℤ :=
  shiftedFrame domainSubordLeft (-3) (-3)

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
    domainSubordWouldReturn.referenceTime > domainSubordLeft.eventTime := by
  simp only [domainSubordWouldReturn, shiftedFrame, domainSubordLeft]; omega

/-- Shift: both frames have P = S (absolute perspective). -/
theorem domainShiftBothAbsolute :
    domainShiftLeft.perspectiveTime = domainShiftLeft.speechTime ∧
    domainShiftCameBack.perspectiveTime = domainShiftCameBack.speechTime :=
  ⟨rfl, rfl⟩

/-- Subordination: `wouldReturn` has shifted perspective. -/
theorem domainSubordShiftedPerspective :
    domainSubordWouldReturn.perspectiveTime ≠ domainSubordWouldReturn.speechTime := by
  simp only [domainSubordWouldReturn, shiftedFrame, domainSubordLeft]; decide


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
