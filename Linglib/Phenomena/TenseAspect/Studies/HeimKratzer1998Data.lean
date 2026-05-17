import Linglib.Core.Time.Reichenbach
import Linglib.Core.Time.Boundedness
import Linglib.Core.Time.Tense

/-!
# Tense Phenomena: Multi-Source Empirical Data (DEPRECATED — in dissolution)
@cite{abusch-1997} @cite{anand-nevins-2004} @cite{banfield-1982}
@cite{comrie-1985} @cite{deal-2020} @cite{declerck-1991}
@cite{declerck-2006} @cite{iatridou-2000} @cite{klecha-2016}
@cite{kratzer-1998} @cite{ogihara-sharvit-2012} @cite{schlenker-2004}
@cite{sharvit-2003} @cite{von-stechow-2009} @cite{wurmbrand-2014}
@cite{schlenker-2003}

**This file is being dissolved per-paper into individual Studies/
files** (see `Studies/Kratzer1998.lean` for §29, which has already
migrated). The original aggregation violated CLAUDE.md's per-paper
anchoring rule — every Lean file must anchor on one paper / named
framework / documented empirical pattern. The remaining sections
(§0–§28) await migration to their respective per-paper homes.

Was `Phenomena/TenseAspect/Data.lean`; relocated to `Studies/` per
the provenance-tracking policy. Per-section migration plan:
`Studies/Abusch1997.lean` (§1-3, 5, 9); `Studies/Ogihara1996.lean`
(§4, 14); `Studies/Klecha2016.lean` (§7); `Studies/Schlenker2004.lean`
(§12); `Studies/Sharvit2003.lean` (§6, 11, 18, 21);
`Studies/Iatridou2000.lean` (§8, 20); `Studies/Wurmbrand2014.lean`
(§15, 22); `Studies/AnandNevins2004.lean` (§17);
`Studies/Musan1995.lean` (§19); `Studies/Declerck1991.lean` (§23-26,
28); `Phenomena/Aspect/Studies/Declerck1991.lean` (§27). §0 +
§10 will be deleted (boilerplate / narration). The current consumer
`Studies/Schlenker2004.lean` will repoint to `Studies/Abusch1997.lean`
once the latter receives the `matrixSaid`/`embeddedSick*` symbols.

Coverage: 10+ temporal phenomena that distinguish tense theories,
absorbing the former `Phenomena/SequenceOfTense/Data.lean`.

## Phenomena Covered

### Baseline (§0)
0. Root-clause simple tenses: past, present, future

### Core comparison set (10 + 1 debate)
1. Past-under-past: "John said Mary was sick" (shifted + simultaneous)
2. Present-under-past: "John said Mary is sick" (double access)
3. Future-under-past: "John said Mary would leave"
4. SOT vs non-SOT: English vs Japanese
5. Upper Limit Constraint: no forward-shifted readings
6. Relative clause tense: "the man who was tall"
7. Modal-tense interaction: "John might have left"
8. Counterfactual tense: "If John were here..."
9. Temporal de re: "John believed it was raining"
10. Deletion vs ambiguity: same surface, different mechanisms

### Eventual targets (7)
11. SOT in indirect questions: "John asked who was sick"
12. Free indirect discourse: perspective shift without attitude verb
13. Historical/narrative present: "Napoleon enters the room"
14. Perfect tense interactions: "John said Mary had been sick"
15. Future-oriented complements: "John wanted to leave"
16. Tense in adjunct clauses: "Before John left, Mary was happy"
17. Indexical tense shift: Amharic/Zazaki tense under attitudes

### Extended phenomena (5) — Sharvit, Zeijlstra, Wurmbrand
18. Embedded present puzzle: "John will say Mary is sick"
19. Lifetime effects: "Aristotle was a philosopher"
20. Fake past: "If John were taller..."
21. Optional SOT (Hebrew-type)
22. Dependent vs independent tense

### Discourse-level phenomena (6) — @cite{declerck-1991}/2006
23. Temporal domain shift vs subordination
24. False tense: politeness and tentativeness
25. PPS vs FPS in conditionals
26. Temporal conjunctions with implicit TOs
27. Bounded/unbounded default interpretation (PUTI)
28. Present perfect vs preterit: time-sphere distinction

-/

namespace Phenomena.TenseAspect

open Core.Time.Reichenbach
open Core.Time (SituationBoundedness)
open Core.Time.Tense


-- ════════════════════════════════════════════════════════════════
-- § 6. Relative Clause Tense: "the man who was tall"
-- ════════════════════════════════════════════════════════════════

/-- Relative clause frame: "the man who was tall"
    Perspective time = time of the described event (not matrix E).
    The past tense in the RC is checked against the RC's own
    perspective time, not the matrix tense. -/
def rcWasTall : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0    -- RC perspective = speech time (default)
  referenceTime := -3     -- PAST: man was tall before now
  eventTime := -3         -- tallness at past time

/-- Relative clause under past matrix: "John met the man who was tall"
    Here the RC tense could be relative to matrix E or to S —
    this is the Sharvit challenge to Abusch. -/
def rcWasTallUnderPast : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- if RC perspective shifts to matrix E
  referenceTime := -4     -- past relative to matrix E
  eventTime := -4


-- ════════════════════════════════════════════════════════════════
-- § 11. SOT in Indirect Questions: "John asked who was sick"
-- ════════════════════════════════════════════════════════════════

/-! Indirect questions show SOT effects: "John asked who was sick"
    has both a simultaneous reading (who is sick at the asking time?)
    and a shifted reading (who was sick before the asking?).

    The question embedding adds a layer: the embedded wh-clause's
    tense interacts with both the question semantics and the matrix
    tense. @cite{sharvit-2003} and @cite{ogihara-sharvit-2012} argue this
    is not a simple extension of declarative SOT. -/

/-- Matrix frame for "John asked..." (past tense, perfective). -/
def matrixAsked : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2
  eventTime := -2

/-- Embedded frame for "who was sick" — simultaneous with asking.
    The question is about sickness at the asking time. -/
def indirectQSimultaneous : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -2     -- simultaneous: R' = E_matrix
  eventTime := -2

/-- Embedded frame for "who was sick" — shifted before asking.
    The question is about sickness before the asking time. -/
def indirectQShifted : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -4     -- shifted: R' < E_matrix
  eventTime := -4


-- ════════════════════════════════════════════════════════════════
-- § 13. Historical / Narrative Present
-- ════════════════════════════════════════════════════════════════

/-! Historical present: present tense morphology with past temporal
    reference.

    "Napoleon enters the room. He sees the generals."

    The present tense "enters" does not locate the event at speech time.
    It refers to a past event but uses present morphology for vividness.
    This is problematic for theories where present tense = R = S:
    the constraint is violated, yet the sentence is felicitous.

    @cite{wolfson-1979}, @cite{schiffrin-1981}. -/

/-- Historical present: "Napoleon enters the room."
    Present morphology (R = P) but the event is in the past.
    Speech time S = 0, but the narrated event is at -200 (schematic). -/
def historicalPresent : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -200  -- narrative perspective shifted to past
  referenceTime := -200    -- R = P (present morphology)
  eventTime := -200        -- event at the narrated past time

/-- Historical present is "present" relative to narrative perspective. -/
theorem historicalPresent_is_present :
    historicalPresent.isPresent := rfl


-- ════════════════════════════════════════════════════════════════
-- § 15. Future-Oriented Complements
-- ════════════════════════════════════════════════════════════════

/-! Verbs like *want*, *plan*, *hope* orient their complement toward
    the future without standard SOT:

    "John wanted to leave."

    The leaving is AFTER the wanting, but there is no future tense
    morphology. The futurity comes from the verb's lexical semantics,
    not from tense. @cite{wurmbrand-2014}: the temporal orientation is
    part of the verb's selection, not tense composition.

    "John planned to leave" — the leaving is strictly after the planning.
    "John hoped to win" — the winning is after the hoping.

    These complements behave differently from standard SOT because the
    embedded temporal location is lexically determined, not computed
    from tense morphology. -/

/-- Future-oriented complement: "John wanted to leave."
    The wanting is past; the (desired) leaving is after the wanting.
    No tense morphology on the infinitival complement. -/
def wantedToLeave : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2     -- wanting in the past
  eventTime := -1         -- desired leaving after the wanting

/-- Future-oriented: event time after reference time. -/
theorem wantedToLeave_future_oriented :
    wantedToLeave.eventTime > wantedToLeave.referenceTime := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § 16. Tense in Adjunct Clauses
-- ════════════════════════════════════════════════════════════════

/-! Temporal adjunct clauses have their own tense interpretation
    that doesn't follow the attitude-embedding pattern:

    "Before John left, Mary was happy."
    "After John arrived, Mary smiled."

    The tense in the adjunct ("left", "arrived") locates an event
    relative to the matrix event, but NOT via the perspective-shift
    mechanism used for attitude complements. The adjunct tense is
    more like an independent temporal reference anchored by the
    temporal connective (*before*, *after*).

    @cite{arregui-kusumoto-1998}, @cite{ogihara-sharvit-2012}. -/

/-- Adjunct clause: "Before John left, Mary was happy."
    John's leaving is before Mary's happiness.
    Both are past relative to S, but their relative ordering
    comes from "before", not from tense composition. -/
def adjunctBeforeLeft : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0    -- adjunct tense is absolute (like non-SOT)
  referenceTime := -3     -- adjunct event: John's leaving
  eventTime := -3

/-- Matrix with adjunct: "Mary was happy (before John left)." -/
def matrixWasHappy : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2     -- matrix event: Mary's happiness
  eventTime := -2

/-- The adjunct event precedes the matrix event (from "before"). -/
theorem adjunct_before_matrix :
    adjunctBeforeLeft.eventTime < matrixWasHappy.eventTime := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § 18. Embedded Present Puzzle: "John will say Mary is sick"
-- ════════════════════════════════════════════════════════════════

/-! The embedded present puzzle: present tense under
    a future matrix verb gets a simultaneous reading with the FUTURE
    saying time, not with speech time.

    "John will say Mary is sick" → Mary is sick at the (future) saying
    time, not necessarily at speech time.

    This is puzzling for theories where present = R = S: the present
    tense should force the event to be at speech time, yet the reading
    locates it at the future saying time. Sharvit: the "present" is
    a simultaneous tense evaluated at the future saying time. -/

/-- Matrix frame for "John will say..." (future tense).
    Speech time S = 0, saying event at t = 3 (future). -/
def matrixWillSay : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0    -- root clause: P = S
  referenceTime := 3      -- FUTURE: R > P
  eventTime := 3          -- saying at future time

/-- Embedded frame for "Mary is sick" under future — simultaneous.
    The sickness is at the future saying time (= matrix E = 3),
    not at speech time. -/
def embeddedPresentUnderFuture : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 3    -- embedded P = matrix E (future saying time)
  referenceTime := 3      -- simultaneous: R' = P' = matrix E
  eventTime := 3          -- sick at the saying time


-- ════════════════════════════════════════════════════════════════
-- § 21. Optional SOT (Hebrew-type)
-- ════════════════════════════════════════════════════════════════

/-! Optional SOT in Hebrew-type languages.

    In English, SOT is obligatory: "John said Mary was sick" is the
    only form for the simultaneous reading. In Hebrew, both forms
    are grammatical:

    "John said Mary was sick" → simultaneous reading (simultaneous tense)
    "John said Mary is sick" → simultaneous reading (present tense)

    Both forms are available with slightly different pragmatic profiles.
    The past-form version uses Sharvit's simultaneous tense; the
    present-form version uses genuine present tense. -/

/-- Hebrew-type SOT with past form (simultaneous tense):
    "John said Mary was sick" → simultaneous reading.
    Same frame as English embeddedSickSimultaneous. -/
def optionalSOTPastForm : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -2     -- simultaneous: R' = P'
  eventTime := -2

/-- Hebrew-type SOT with present form:
    "John said Mary is sick" → also simultaneous, but via present tense.
    The present tense directly locates the event at the attitude time. -/
def optionalSOTPresentForm : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -2     -- R' = P' (present tense)
  eventTime := -2


-- ════════════════════════════════════════════════════════════════
-- § 22. Dependent vs Independent Tense (@cite{wurmbrand-2014})
-- ════════════════════════════════════════════════════════════════

/-! @cite{wurmbrand-2014} classifies infinitival tense into three types:

    1. **Future irrealis** (decide, want): no independent tense;
       future orientation comes from woll.
       "John decided to leave" → leaving after deciding.

    2. **Propositional** (believe, claim): NOW-anchored tense.
       "John believes Mary to be sick" → simultaneous with believing.

    3. **Restructuring** (try, begin): dependent on matrix tense.
       "John tried to leave" → leaving in the same temporal domain.

    This is relevant because it shows that the "tenselessness" of
    infinitives is not uniform — different complement types have
    different temporal behavior. -/

/-- Future-irrealis complement: "John decided to leave."
    The deciding is past; the leaving is after the deciding.
    No tense morphology on "to leave." -/
def decidedToLeave : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2     -- deciding in the past
  eventTime := -1         -- leaving after the deciding

/-- Propositional complement: "John believes Mary to be sick."
    The believing is present; the sickness is simultaneous. -/
def believesToBeSick : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0      -- believing now
  eventTime := 0          -- sickness simultaneous with believing

/-- Restructuring complement: "John tried to leave."
    The trying and the leaving are in the same temporal domain. -/
def triedToLeave : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2     -- trying in the past
  eventTime := -2         -- leaving in the same temporal domain


-- ════════════════════════════════════════════════════════════════
-- § Theory-Neutral Temporal Facts
-- ════════════════════════════════════════════════════════════════


/-- RC tense: past reference. -/
theorem rc_past_reference :
    rcWasTall.referenceTime < rcWasTall.perspectiveTime := by native_decide


-- ── Eventual target facts ──

/-- Indirect question: simultaneous frame has R = P. -/
theorem indirectQ_simultaneous_present :
    indirectQSimultaneous.isPresent := rfl

/-- Indirect question: shifted frame has R < P. -/
theorem indirectQ_shifted_past :
    indirectQShifted.referenceTime < indirectQShifted.perspectiveTime := by native_decide

/-- Historical present: present morphology despite past event. -/
theorem historicalPresent_R_eq_P :
    historicalPresent.referenceTime = historicalPresent.perspectiveTime := rfl

/-- Historical present: event time ≠ speech time. -/
theorem historicalPresent_not_at_speech :
    historicalPresent.eventTime ≠ historicalPresent.speechTime := by native_decide

/-- Adjunct "before": adjunct event precedes matrix event. -/
theorem adjunct_precedes_matrix :
    adjunctBeforeLeft.eventTime < matrixWasHappy.eventTime := by native_decide


-- ── Extended phenomena facts ──

/-- Embedded present puzzle: present under future has R = P (simultaneous). -/
theorem embeddedPresentUnderFuture_simultaneous :
    embeddedPresentUnderFuture.isPresent := rfl

/-- Embedded present puzzle: event NOT at speech time. -/
theorem embeddedPresentUnderFuture_not_at_speech :
    embeddedPresentUnderFuture.eventTime ≠ embeddedPresentUnderFuture.speechTime := by
  native_decide

/-- Embedded present puzzle: matrix is future. -/
theorem matrixWillSay_is_future :
    matrixWillSay.referenceTime > matrixWillSay.perspectiveTime := by native_decide


/-- Optional SOT: both forms give R = P. -/
theorem optionalSOT_both_simultaneous :
    optionalSOTPastForm.isPresent ∧ optionalSOTPresentForm.isPresent :=
  ⟨rfl, rfl⟩

/-- Optional SOT: both forms have the same temporal structure. -/
theorem optionalSOT_same_frame :
    optionalSOTPastForm = optionalSOTPresentForm := rfl

/-- Future-irrealis complement: event after reference (future-oriented). -/
theorem decidedToLeave_future_oriented :
    decidedToLeave.eventTime > decidedToLeave.referenceTime := by native_decide

/-- Propositional complement: event at reference (simultaneous). -/
theorem believesToBeSick_simultaneous :
    believesToBeSick.eventTime = believesToBeSick.referenceTime := rfl

/-- Restructuring complement: event at reference (same domain). -/
theorem triedToLeave_same_domain :
    triedToLeave.eventTime = triedToLeave.referenceTime := rfl


-- ════════════════════════════════════════════════════════════════
-- § 23. Temporal Domain: Shift vs. Subordination (Declerck ch. 2 §12–14)
-- ════════════════════════════════════════════════════════════════

/-! Two ways successive clauses relate temporally:

    **Temporal subordination**: "He left and would never come back."
    The conditional (`would`) is a *relative* tense expressing
    posteriority within the past domain established by `left`.

    **Domain shift**: "He left and never came back."
    Both clauses use *absolute* preterits establishing independent
    domains. Temporal ordering is recovered pragmatically, not
    structurally.

    @cite{declerck-1991} ch. 2 §12–14. -/

/-- "He left..." — past domain anchor (subordination pair).
    Speech time S = 0, leaving event at t = -5. -/
def domainSubordLeft : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -5
  eventTime := -5

/-- "... and would never come back" — relative tense within the
    past domain established by `left`. The `would` expresses
    posteriority relative to the leaving, not to speech time. -/
def domainSubordWouldReturn : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -5   -- P' = domain anchor (left's E)
  referenceTime := -3     -- R > P': posterior within domain
  eventTime := -3

/-- "He left..." — independent past domain (shift pair). -/
def domainShiftLeft : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -5
  eventTime := -5

/-- "... and never came back" — independent past domain.
    Both clauses are absolute preterits; no structural
    temporal relation between them. -/
def domainShiftCameBack : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0    -- absolute: P = S (not shifted)
  referenceTime := -3
  eventTime := -3


-- ── § 23 temporal facts ──

/-- Both `left` frames are past (R < P). -/
theorem domainSubord_left_past :
    domainSubordLeft.referenceTime < domainSubordLeft.perspectiveTime := by native_decide

theorem domainShift_left_past :
    domainShiftLeft.referenceTime < domainShiftLeft.perspectiveTime := by native_decide

/-- Subordination: `wouldReturn` is posterior within the domain
    established by `left` (R > P' where P' = left's E). -/
theorem domainSubord_posteriority :
    domainSubordWouldReturn.referenceTime > domainSubordLeft.eventTime := by native_decide

/-- Shift: both frames independently satisfy PAST relative to their own P.
    The shift pair has P = S for both clauses (absolute perspective). -/
theorem domainShift_both_absolute :
    domainShiftLeft.perspectiveTime = domainShiftLeft.speechTime ∧
    domainShiftCameBack.perspectiveTime = domainShiftCameBack.speechTime :=
  ⟨rfl, rfl⟩

/-- Subordination: `wouldReturn` has shifted perspective (P ≠ S). -/
theorem domainSubord_shifted_perspective :
    domainSubordWouldReturn.perspectiveTime ≠ domainSubordWouldReturn.speechTime := by
  native_decide


-- ════════════════════════════════════════════════════════════════
-- § 24. False Tense: Politeness and Tentativeness (Declerck ch. 2 §20–21)
-- ════════════════════════════════════════════════════════════════

/-! Past morphology with present-time reference for pragmatic effects:

    "I wanted to ask you something." — past morphology, present request
    "Could you help me?" — past modal, present request

    Distinct from §20 (fake past / counterfactual): false tense is *not*
    counterfactual — the speaker is genuinely asking now. Declerck
    analyzes this as a shift of temporal perspective from present to past,
    exploiting the metaphor between temporal remoteness and social distance.

    @cite{declerck-1991} ch. 2 §20–21. -/

/-- "I wanted to ask you something." — false past.
    Past morphology ("wanted") but present-time reference:
    the wanting is happening now, not in the past. -/
def falsePastWanted : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0      -- present reference despite past morphology
  eventTime := 0

/-- "Could you help me?" — false past modal.
    Past modal morphology ("could") but present-time request. -/
def falsePastCould : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0      -- present reference despite past morphology
  eventTime := 0


-- ── § 24 temporal facts ──

/-- Both false-past frames have R = P (present reference). -/
theorem falsePast_present_reference_wanted :
    falsePastWanted.referenceTime = falsePastWanted.perspectiveTime := rfl

theorem falsePast_present_reference_could :
    falsePastCould.referenceTime = falsePastCould.perspectiveTime := rfl

-- ════════════════════════════════════════════════════════════════
-- § 25. PPS vs FPS in Conditionals (Declerck ch. 4 §2)
-- ════════════════════════════════════════════════════════════════

/-! Standard conditionals use the Present Perspective System (PPS):
    present tense in if-clause for future reference.
    Non-standard types use the Future Perspective System (FPS):
    will/be going to in if-clause.

    PPS: "If he comes, I will be happy."
    FPS: "If he will go to China, we should publish now."

    The FPS if-clause has explicit future morphology, reversing the
    typical temporal anchoring: the if-clause is future and the
    matrix clause is present.

    @cite{declerck-1991} ch. 4 §2. -/

/-- PPS if-clause: "If he comes..." — present morphology,
    future pragmatic reference. R = P (present tense form). -/
def ppsIfComes : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0      -- present tense morphology
  eventTime := 3          -- pragmatically future event

/-- PPS matrix: "... I will be happy." — future tense. -/
def ppsWillBeHappy : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 3      -- future: R > P
  eventTime := 3

/-- FPS if-clause: "If he will go to China..." — future in
    the if-clause (non-standard). -/
def fpsIfWillGo : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 5      -- future: R > P (explicit future in if-clause)
  eventTime := 5

/-- FPS matrix: "... we should publish now." — present tense. -/
def fpsShouldPublish : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0      -- present: R = P
  eventTime := 0


-- ── § 25 temporal facts ──

/-- PPS if-clause: present morphology (R = P). -/
theorem pps_ifClause_present_morphology :
    ppsIfComes.referenceTime = ppsIfComes.perspectiveTime := rfl

/-- FPS if-clause: future morphology (R > P). -/
theorem fps_ifClause_future_morphology :
    fpsIfWillGo.referenceTime > fpsIfWillGo.perspectiveTime := by native_decide

/-- PPS matrix is future; FPS matrix is present — reversed anchoring. -/
theorem pps_fps_reversed_anchoring :
    ppsWillBeHappy.referenceTime > ppsWillBeHappy.perspectiveTime ∧
    fpsShouldPublish.referenceTime = fpsShouldPublish.perspectiveTime :=
  ⟨by native_decide, rfl⟩

/-- PPS: if-clause event is in the future despite present morphology. -/
theorem pps_ifClause_future_event :
    ppsIfComes.eventTime > ppsIfComes.speechTime := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § 26. Temporal Conjunctions with Implicit TOs (Declerck ch. 2 §24–25)
-- ════════════════════════════════════════════════════════════════

/-! Temporal connectives (before/after/when) involve an implicit TO
    distinct from the situation-TOs of either clause:

    "Bill will have left when John arrives."
    The present tense in the when-clause expresses simultaneity with
    an implicit TO (= TO₂ of the future perfect), not with Bill's leaving.

    "John had left before we arrived."
    The preterit `arrived` expresses simultaneity with an implicit TO
    that is posterior to John's leaving.

    @cite{declerck-1991} ch. 2 §24–25. -/

/-- "Bill will have left..." — future perfect.
    E < R (perfect: leaving before reference) and R > P (future). -/
def futPerfLeft : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 5      -- future reference
  eventTime := 3          -- leaving before reference (E < R = perfect)

/-- "... when John arrives." — when-clause present tense.
    R = P' where P' is the implicit TO (= futPerfLeft.R).
    The present tense is relative to the implicit TO, not speech time. -/
def whenArrives : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 5    -- implicit TO = future perfect's R
  referenceTime := 5      -- R = P' (present relative to implicit TO)
  eventTime := 5          -- arriving at the implicit TO

/-- "John had left..." — past perfect (before-clause pair).
    E < R (perfect) and R < P (past). -/
def hadLeftBefore : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2     -- past reference
  eventTime := -4         -- leaving before reference (perfect: E < R)

/-- "... before we arrived." — before-clause.
    The arrival is at the implicit TO, which is posterior to
    John's leaving. -/
def beforeArrived : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2     -- past reference
  eventTime := -2         -- arrival at the implicit TO


-- ── § 26 temporal facts ──

/-- Future perfect: leaving before arrival (E_left < E_arrives). -/
theorem futPerf_leaving_before_arrival :
    futPerfLeft.eventTime < whenArrives.eventTime := by native_decide

/-- Future perfect frame has E < R (perfect aspect). -/
theorem futPerf_is_perfect :
    futPerfLeft.isPerfect := by
  simp only [ReichenbachFrame.isPerfect, futPerfLeft]; omega

/-- When-clause: present relative to implicit TO (R = P). -/
theorem when_clause_present :
    whenArrives.isPresent := rfl

/-- Before-clause: leaving before arrival (E_had_left < E_arrived). -/
theorem before_leaving_before_arrival :
    hadLeftBefore.eventTime < beforeArrived.eventTime := by native_decide

/-- Past perfect frame has E < R (perfect aspect). -/
theorem hadLeft_is_perfect :
    hadLeftBefore.isPerfect := by
  simp only [ReichenbachFrame.isPerfect, hadLeftBefore]; omega


-- ════════════════════════════════════════════════════════════════
-- § 27. Bounded/Unbounded Default Interpretation (Declerck ch. 3 §1.2)
-- ════════════════════════════════════════════════════════════════

/-! Declerck's Principle of Unmarked Temporal Interpretation (PUTI):

    - Bounded + bounded → iconic (sequential) ordering
    - Unbounded + unbounded → simultaneity
    - Mixed → temporal inclusion

    These are pragmatic defaults, not semantic entailments.

    @cite{declerck-1991} ch. 3 §1.2. -/

/-- A Reichenbach frame paired with its aspectual boundedness. -/
structure BoundedFrame where
  frame : ReichenbachFrame ℤ
  boundedness : SituationBoundedness

/-- "He arrived." — bounded (achievement). -/
def arrivedBounded : BoundedFrame where
  frame := { speechTime := 0, perspectiveTime := 0, referenceTime := -5, eventTime := -5 }
  boundedness := .bounded

/-- "He sat down." — bounded (achievement), after arrival. -/
def satDownBounded : BoundedFrame where
  frame := { speechTime := 0, perspectiveTime := 0, referenceTime := -4, eventTime := -4 }
  boundedness := .bounded

/-- "It was raining." — unbounded (activity/state). -/
def rainingUnbounded : BoundedFrame where
  frame := { speechTime := 0, perspectiveTime := 0, referenceTime := -3, eventTime := -3 }
  boundedness := .unbounded

/-- "The wind was blowing." — unbounded (activity), simultaneous with rain. -/
def windBlowingUnbounded : BoundedFrame where
  frame := { speechTime := 0, perspectiveTime := 0, referenceTime := -3, eventTime := -3 }
  boundedness := .unbounded

/-- "He was reading." — unbounded (activity). -/
def readingUnbounded : BoundedFrame where
  frame := { speechTime := 0, perspectiveTime := 0, referenceTime := -3, eventTime := -3 }
  boundedness := .unbounded

/-- "The phone rang." — bounded (achievement), included in reading interval. -/
def phoneRangBounded : BoundedFrame where
  frame := { speechTime := 0, perspectiveTime := 0, referenceTime := -3, eventTime := -3 }
  boundedness := .bounded


-- ── § 27 temporal facts ──

/-- Sequential (bounded + bounded): arrival before sitting (iconic ordering). -/
theorem bounded_sequential :
    arrivedBounded.frame.eventTime < satDownBounded.frame.eventTime := by native_decide

/-- Simultaneous (unbounded + unbounded): rain and wind at the same time. -/
theorem unbounded_simultaneous :
    rainingUnbounded.frame.eventTime = windBlowingUnbounded.frame.eventTime := rfl

/-- Inclusion (mixed): phone ringing within reading interval. -/
theorem mixed_inclusion :
    phoneRangBounded.frame.eventTime = readingUnbounded.frame.eventTime := rfl

/-- Both bounded frames are bounded. -/
theorem sequential_both_bounded :
    arrivedBounded.boundedness = .bounded ∧ satDownBounded.boundedness = .bounded :=
  ⟨rfl, rfl⟩

/-- Both unbounded frames are unbounded. -/
theorem simultaneous_both_unbounded :
    rainingUnbounded.boundedness = .unbounded ∧ windBlowingUnbounded.boundedness = .unbounded :=
  ⟨rfl, rfl⟩

/-- Mixed: one unbounded, one bounded. -/
theorem inclusion_mixed_boundedness :
    readingUnbounded.boundedness = .unbounded ∧ phoneRangBounded.boundedness = .bounded :=
  ⟨rfl, rfl⟩


-- ════════════════════════════════════════════════════════════════
-- § 28. Present Perfect vs Preterit: Time-Sphere (Declerck ch. 7 §1,3)
-- ════════════════════════════════════════════════════════════════

/-! Declerck's distinctive claim: the present perfect and preterit differ
    *not* in definiteness or current relevance but in time-sphere membership.
    Both can refer to the same objective event; what differs is the speaker's
    conceptualization.

    "I have visited Paris." (pre-present sector: E ≤ R ≤ P,
      situation anchored to present time-sphere)
    "I visited Paris." (past time-sphere: E = R < P,
      situation detached from present)

    @cite{declerck-1991} ch. 7 §1,3; @cite{declerck-2006}. -/

/-- "I have visited Paris." — present perfect.
    Pre-present sector: E < R and R = P (present time-sphere).
    The event is past but the reference frame is present. -/
def perfectVisitedParis : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0      -- R = P (present time-sphere)
  eventTime := -3         -- E < R (past event)

/-- "I visited Paris." — simple preterit.
    Past time-sphere: E = R < P.
    Same objective event time as the perfect, but the reference
    frame is past. -/
def preteritVisitedParis : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3     -- R < P (past time-sphere)
  eventTime := -3         -- E = R


-- ── § 28 temporal facts ──

/-- Both frames locate the event before speech time. -/
theorem perfectPreterit_both_event_before_speech :
    perfectVisitedParis.eventTime < perfectVisitedParis.speechTime ∧
    preteritVisitedParis.eventTime < preteritVisitedParis.speechTime := by
  constructor <;> native_decide

/-- Same event time — the difference is structural, not temporal. -/
theorem perfectPreterit_same_eventTime :
    perfectVisitedParis.eventTime = preteritVisitedParis.eventTime := rfl

/-- Present perfect: E < R (perfect aspect, pre-present). -/
theorem perfect_is_perfect :
    perfectVisitedParis.isPerfect := by
  simp only [ReichenbachFrame.isPerfect, perfectVisitedParis]; omega

/-- Present perfect: R = P (present orientation). -/
theorem perfect_isPresent :
    perfectVisitedParis.isPresent := rfl

/-- Preterit: R < P (past orientation). -/
theorem preterit_isPast :
    preteritVisitedParis.isPast := by
  simp only [ReichenbachFrame.isPast, preteritVisitedParis]; omega

/-- Preterit is perfective (E = R). -/
theorem preterit_is_perfective :
    preteritVisitedParis.isPerfective := rfl


end Phenomena.TenseAspect
