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


-- (§13 migrated to Phenomena/TenseAspect/HistoricalPresent.lean — sub-phenomenon file,
--  no Reichenbach frame; the (S,P,R,E) tuple conflates morphology with interpretation
--  for HP, per memory feedback_reichenbach_morph_vs_interp_conflation)
-- (§16 migrated to Studies/ArreguiKusumoto1998.lean)


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


-- (§27 PUTI / Bounded-Unbounded migrated to Phenomena/Aspect/Studies/Declerck1991.lean
--  per audit finding: aspect content, not tense content. BoundedFrame struct dropped
--  per audit; plain ReichenbachFrame defs in the new file.)


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
