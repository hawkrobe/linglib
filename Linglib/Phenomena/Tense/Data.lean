import Linglib.Core.Reichenbach
import Linglib.Core.Time
import Linglib.Core.Tense

/-!
# Tense Phenomena: Empirical Data

Unified entry point for tense phenomena. Absorbs the former
`Phenomena/SequenceOfTense/Data.lean` and extends coverage to
10+ temporal phenomena that distinguish tense theories.

Theory-neutral empirical data only — no theoretical commitments.
Bridge theorems connecting this data to specific tense theories
are in `Bridge.lean`.

## Phenomena Covered

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
22. Dependent vs independent tense (Wurmbrand 2014)

## References

- Ogihara, T. (1989/1996). Tense, Attitudes, and Scope.
- Ogihara, T. & Sharvit, Y. (2012). Embedded tenses.
- Abusch, D. (1997). Sequence of tense and temporal de re.
- Von Stechow, A. (2009). Tenses in compositional semantics.
- Kratzer, A. (1998). More structural analogies between pronouns and tenses.
- Klecha, P. (2016). Modality and embedded temporal operators.
- Deal, A. R. (2020). Counterfactuals and the Upper Limit Constraint.
- Sharvit, Y. (2003). Trying to be progressive.
- Iatridou, S. (2000). The grammatical ingredients of counterfactuality.
- Banfield, A. (1982). Unspeakable Sentences.
- Schlenker, P. (2004). Context of thought and context of utterance.
- Anand, P. & Nevins, A. (2004). Shifty operators in changing contexts.
- Wurmbrand, S. (2014). Tense and aspect in English infinitives.
- Comrie, B. (1985). Tense.
- Sharvit, Y. (2003). Embedded tense and universal grammar.
- Musan, R. (1995/1997). On the temporal interpretation of noun phrases.
- Iatridou, S. (2000). The grammatical ingredients of counterfactuality.
-/

namespace Phenomena.Tense

open Core.Reichenbach
open Core.Tense


-- ════════════════════════════════════════════════════════════════
-- § 1. Past-Under-Past: "John said Mary was sick"
-- ════════════════════════════════════════════════════════════════

/-! Two readings of "John said that Mary was sick":
    - SIMULTANEOUS: Mary's being sick overlaps with John's saying
    - SHIFTED: Mary's being sick precedes John's saying -/

/-- Matrix frame for "John said ..." (past tense, perfective).
    Speech time S = 0, saying event at t = -2. -/
def matrixSaid : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0    -- root clause: P = S
  referenceTime := -2     -- PAST: R < P
  eventTime := -2         -- perfective: E = R

/-- Embedded frame for "Mary was sick" — SIMULTANEOUS reading.
    Embedded P = matrix E = -2, R' = E_matrix = -2.
    Mary is sick at the time of the saying. -/
def embeddedSickSimultaneous : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -2     -- simultaneous: R' = E_matrix
  eventTime := -2         -- sick-time = say-time

/-- Embedded frame for "Mary was sick" — SHIFTED reading.
    Embedded P = matrix E = -2, R' = -5 < E_matrix.
    Mary was sick before the saying. -/
def embeddedSickShifted : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -5     -- shifted: R' < E_matrix
  eventTime := -5         -- sick-time before say-time


-- ════════════════════════════════════════════════════════════════
-- § 2. Present-Under-Past: "John said Mary is sick"
-- ════════════════════════════════════════════════════════════════

/-- Embedded frame for "Mary is sick" — PRESENT under PAST.
    Double-access reading: Mary is sick now (at speech time) AND
    the sickness is relevant at the time of saying. -/
def embeddedSickPresent : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -2     -- R' = P' (present relative to matrix)
  eventTime := 0          -- sick at speech time (double-access)


-- ════════════════════════════════════════════════════════════════
-- § 3. Future-Under-Past: "John said Mary would leave"
-- ════════════════════════════════════════════════════════════════

/-- Embedded frame for "Mary would leave" — FUTURE under PAST.
    "Would" = PAST + FUTURE (Condoravdi 2002): the leaving is
    after the saying but before or at speech time. -/
def embeddedWouldLeave : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -1     -- R' > E_matrix (future relative to saying)
  eventTime := -1         -- leaving after saying


-- ════════════════════════════════════════════════════════════════
-- § 4. SOT vs Non-SOT: English vs Japanese
-- ════════════════════════════════════════════════════════════════

/-- Japanese matrix frame: "Taroo-ga ... to itta" (Taro said ...).
    Same temporal structure as English matrix. -/
def matrixItta : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2
  eventTime := -2

/-- Japanese embedded: "Mary-ga byooki-datta" (Mary was sick) — absolute past.
    In non-SOT Japanese, embedded past is absolute (relative to S, not E).
    Only the shifted reading: sick-time < say-time. -/
def embeddedByookiDatta : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0    -- non-SOT: P = S (absolute, not shifted)
  referenceTime := -5     -- PAST relative to S: R < S
  eventTime := -5


-- ════════════════════════════════════════════════════════════════
-- § 5. Upper Limit Constraint: No Forward-Shifted Readings
-- ════════════════════════════════════════════════════════════════

/-- Hypothetical forward-shifted frame (for gap demonstration).
    If past-under-past allowed forward shift, R' > E_matrix.
    This frame is PREDICTED NOT TO EXIST as a reading. -/
def embeddedSickForwardShifted : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -1     -- R' = -1 > E_matrix = -2 (forward shifted!)
  eventTime := -1         -- sick AFTER the saying


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
-- § 7. Modal-Tense: "John might have left"
-- ════════════════════════════════════════════════════════════════

/-- Modal-past frame: "John might have left"
    The past tense "have left" is under the modal "might".
    The leaving is past relative to... what? Speech time? Modal eval time?
    Klecha (2016): relative to the modal's evaluation time. -/
def modalPast : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0    -- modal evaluated at speech time
  referenceTime := -1     -- past: the leaving is before now
  eventTime := -1


-- ════════════════════════════════════════════════════════════════
-- § 8. Counterfactual Tense: "If John were here..."
-- ════════════════════════════════════════════════════════════════

/-- Counterfactual frame: "If John were here..."
    Past morphology ("were") but present-time reference.
    The "pastness" is modal distance, not temporal precedence. -/
def counterfactualWere : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0    -- present-time scenario
  referenceTime := 0      -- NOT past! "were" = now, counterfactually
  eventTime := 0


-- ════════════════════════════════════════════════════════════════
-- § 9. Temporal De Re: "John believed it was raining"
-- ════════════════════════════════════════════════════════════════

/-- Temporal de re frame: "John believed it was raining"
    The rain event is located at a time determined in the actual
    world (de re), not in John's belief worlds (de dicto). -/
def temporalDeRe : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- John's belief time (= saying time)
  referenceTime := -3     -- the rain time (de re: actual world)
  eventTime := -3


-- ════════════════════════════════════════════════════════════════
-- § 10. Deletion vs Ambiguity
-- ════════════════════════════════════════════════════════════════

/-! The simultaneous reading of "John said Mary was sick" arises from
    the same surface form regardless of mechanism. The debate is about
    the underlying representation:
    - Kratzer: deletion removes embedded past → R' = E_matrix
    - Ogihara: zero tense reading of past → R' = E_matrix
    Both produce `embeddedSickSimultaneous` — same Reichenbach frame.
    The disagreement is about the derivation, not the result. -/


-- ════════════════════════════════════════════════════════════════
-- § 11. SOT in Indirect Questions: "John asked who was sick"
-- ════════════════════════════════════════════════════════════════

/-! Indirect questions show SOT effects: "John asked who was sick"
    has both a simultaneous reading (who is sick at the asking time?)
    and a shifted reading (who was sick before the asking?).

    The question embedding adds a layer: the embedded wh-clause's
    tense interacts with both the question semantics and the matrix
    tense. Sharvit (2003) and Ogihara & Sharvit (2012) argue this
    is not a simple extension of declarative SOT. -/

/-- Matrix frame for "John asked ..." (past tense, perfective). -/
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
-- § 12. Free Indirect Discourse
-- ════════════════════════════════════════════════════════════════

/-! Free indirect discourse (FID) exhibits perspective shift in tense
    without an overt attitude verb:

    "She walked to the window. The garden was/*is beautiful."

    The past tense in the second sentence is evaluated from the
    character's perspective time, not the narrator's. This challenges
    theories that derive perspective shift from attitude verb semantics
    (Abusch, Von Stechow, Kratzer, Ogihara) — there is no attitude verb
    to trigger the shift.

    Banfield (1982), Schlenker (2004), Sharvit (2008). -/

/-- FID matrix: "She walked to the window" (past, narrated event at -3). -/
def fidWalked : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -3
  eventTime := -3

/-- FID continuation: "The garden was beautiful."
    Perspective shifts to character's viewpoint (E_matrix = -3)
    even though there is no attitude verb. -/
def fidGardenBeautiful : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -3   -- perspective = character's time (no attitude verb!)
  referenceTime := -3     -- simultaneous with character's experience
  eventTime := -3


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

    Wolfson (1979), Schiffrin (1981). -/

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
-- § 14. Perfect Tense Interactions
-- ════════════════════════════════════════════════════════════════

/-! The pluperfect (past perfect) disambiguates past-under-past:

    "John said Mary had been sick."

    Unlike simple past-under-past ("John said Mary was sick"), the
    pluperfect ONLY has the shifted reading. There is no simultaneous
    reading — "had been" forces the sickness to precede the saying.
    This is a useful test case because it disambiguates between
    theories' predictions about what triggers the simultaneous reading.

    Comrie (1985), Ogihara (1996) ch. 4. -/

/-- Pluperfect under past: "John said Mary had been sick."
    Only the shifted reading: sickness before saying.
    The pluperfect adds an additional layer of temporal precedence:
    E < R (perfect aspect) + R < P (past tense). -/
def pluperfectShifted : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E
  referenceTime := -4     -- R' < E_matrix (past of the shifted perspective)
  eventTime := -5         -- E < R (perfect: event precedes reference)

/-- The pluperfect frame has the perfect configuration: E < R. -/
theorem pluperfect_is_perfect :
    pluperfectShifted.isPerfect := by
  simp only [ReichenbachFrame.isPerfect, pluperfectShifted]; omega

/-- The pluperfect frame is past relative to embedded P: R < P. -/
theorem pluperfect_is_past :
    pluperfectShifted.isPast := by
  simp only [ReichenbachFrame.isPast, pluperfectShifted]; omega


-- ════════════════════════════════════════════════════════════════
-- § 15. Future-Oriented Complements
-- ════════════════════════════════════════════════════════════════

/-! Verbs like *want*, *plan*, *hope* orient their complement toward
    the future without standard SOT:

    "John wanted to leave."

    The leaving is AFTER the wanting, but there is no future tense
    morphology. The futurity comes from the verb's lexical semantics,
    not from tense. Wurmbrand (2014): the temporal orientation is
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

    Arregui & Kusumoto (1998), Ogihara & Sharvit (2012). -/

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
-- § 17. Indexical Tense Shift
-- ════════════════════════════════════════════════════════════════

/-! In some languages, tense can shift under attitude verbs in
    ways that parallel the shift of indexical pronouns.

    **Amharic** (Schlenker 2003): the present tense in an attitude
    complement can be interpreted relative to the attitude holder's
    "now" rather than the speaker's speech time.

    **Zazaki** (Anand & Nevins 2004): similar indexical shift for tense
    under reportative evidentials.

    This directly bears on the Partee (1973) analogy between tenses
    and pronouns: if both can undergo indexical shift in the same
    environments, the structural parallel runs deeper than English
    data alone suggests.

    In English, indexical shift of tense is debated (but see the
    double-access reading as a partial parallel). In shifting languages,
    the embedded present tense receives the attitude holder's time,
    not the speaker's speech time. -/

/-- Indexical-shift present under past (Amharic-type):
    "Abebe said Mary IS-sick" where the present tense is interpreted
    at Abebe's saying time, not at speech time.

    Compare with English double-access `embeddedSickPresent` where
    present under past requires truth at BOTH speech time and matrix E.
    In Amharic, there is no double-access requirement — the present
    is simply evaluated at the attitude holder's time. -/
def indexicalShiftPresent : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := -2   -- embedded P = matrix E (attitude holder's time)
  referenceTime := -2     -- R' = P' (present, shifted to attitude time)
  eventTime := -2         -- event at attitude holder's "now"

/-- Indexical shift: event time ≠ speech time (unlike English present).
    The key difference from English double-access: no requirement
    that E = S. The shifted present locates the event at the
    attitude holder's time exclusively. -/
theorem indexicalShift_not_at_speech :
    indexicalShiftPresent.eventTime ≠ indexicalShiftPresent.speechTime := by native_decide


-- ════════════════════════════════════════════════════════════════
-- § 18. Embedded Present Puzzle: "John will say Mary is sick"
-- ════════════════════════════════════════════════════════════════

/-! The embedded present puzzle (Sharvit 2003): present tense under
    a future matrix verb gets a simultaneous reading with the FUTURE
    saying time, not with speech time.

    "John will say Mary is sick" → Mary is sick at the (future) saying
    time, not necessarily at speech time.

    This is puzzling for theories where present = R = S: the present
    tense should force the event to be at speech time, yet the reading
    locates it at the future saying time. Sharvit: the "present" is
    a simultaneous tense evaluated at the future saying time. -/

/-- Matrix frame for "John will say ..." (future tense).
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
-- § 19. Lifetime Effects: "Aristotle was a philosopher"
-- ════════════════════════════════════════════════════════════════

/-! Lifetime effects (Musan 1995/1997): past tense with individual-level
    predicates implicates that the subject no longer exists.

    "Aristotle was a philosopher" → Aristotle is dead.
    "Aristotle was blond" → Aristotle is dead (or no longer blond).

    But: "Aristotle was a philosopher" does NOT merely mean that his
    philosophizing ended — it implicates his death. This is the
    "lifetime effect": past tense + individual-level predicate →
    subject's lifetime has ended.

    This bears on tense theory because it shows that past tense
    interacts with predicate type (individual-level vs stage-level)
    in ways that go beyond simple temporal precedence. -/

/-- Lifetime effect frame: "Aristotle was a philosopher."
    The past tense locates the philosophical property in the past.
    The lifetime effect (Aristotle is dead) is an implicature, not
    part of the Reichenbach frame. -/
def lifetimeAristotle : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := -2400  -- schematic: Aristotle's time
  eventTime := -2400


-- ════════════════════════════════════════════════════════════════
-- § 20. Fake Past: "If John were taller..."
-- ════════════════════════════════════════════════════════════════

/-! Fake past (Iatridou 2000): past morphology with non-past semantics
    in subjunctive/counterfactual contexts.

    "If John were taller, he would play basketball."

    The "were" is morphologically past but does not locate the event
    before speech time. Rather, it expresses counterfactual distance
    (Iatridou 2000) or modal remoteness (Deal 2020).

    This differs from Deal's `counterfactualTense` in specificity:
    fake past is the broader phenomenon (Iatridou's cross-linguistic
    generalization), while Deal's treatment focuses on ULC refinement
    for counterfactuals. -/

/-- Fake past frame: "If John were taller..."
    Past morphology ("were") but present-time reference.
    The temporal coordinates are present; the "pastness" is
    modal distance, not temporal. -/
def fakePastSubjunctive : ReichenbachFrame ℤ where
  speechTime := 0
  perspectiveTime := 0
  referenceTime := 0      -- NOT past: present-time scenario
  eventTime := 0          -- counterfactual present


-- ════════════════════════════════════════════════════════════════
-- § 21. Optional SOT (Hebrew-type)
-- ════════════════════════════════════════════════════════════════

/-! Optional SOT in Hebrew-type languages (Sharvit 2003).

    In English, SOT is obligatory: "John said Mary was sick" is the
    only form for the simultaneous reading. In Hebrew, both forms
    are grammatical:

    "John said Mary was sick" → simultaneous reading (simultaneous tense)
    "John said Mary is sick"  → simultaneous reading (present tense)

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
-- § 22. Dependent vs Independent Tense (Wurmbrand 2014)
-- ════════════════════════════════════════════════════════════════

/-! Wurmbrand (2014) classifies infinitival tense into three types:

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

/-- The matrix "said" is past: R < P. -/
theorem matrixSaid_R_lt_P :
    matrixSaid.referenceTime < matrixSaid.perspectiveTime := by native_decide

/-- The matrix frame is a root clause: P = S. -/
theorem matrixSaid_root :
    matrixSaid.perspectiveTime = matrixSaid.speechTime := by native_decide

/-- Simultaneous reading: embedded R = matrix E. -/
theorem simultaneous_R_eq_matrix_E :
    embeddedSickSimultaneous.referenceTime = matrixSaid.eventTime := by native_decide

/-- Shifted reading: embedded R < matrix E. -/
theorem shifted_R_lt_matrix_E :
    embeddedSickShifted.referenceTime < matrixSaid.eventTime := by native_decide

/-- Simultaneous: sick-time = say-time. -/
theorem simultaneous_sick_at_say_time :
    embeddedSickSimultaneous.eventTime = matrixSaid.eventTime := by native_decide

/-- Shifted: sick-time < say-time. -/
theorem shifted_sick_before_say :
    embeddedSickShifted.eventTime < matrixSaid.eventTime := by native_decide

/-- Japanese: embedded P = S (absolute, not shifted to matrix E). -/
theorem japanese_absolute_perspective :
    embeddedByookiDatta.perspectiveTime = embeddedByookiDatta.speechTime := by native_decide

/-- English simultaneous: embedded P = matrix E (perspective shifted). -/
theorem english_simultaneous_perspective_shifted :
    embeddedSickSimultaneous.perspectiveTime = matrixSaid.eventTime := by native_decide

/-- English shifted: embedded P = matrix E (perspective shifted). -/
theorem english_shifted_perspective_shifted :
    embeddedSickShifted.perspectiveTime = matrixSaid.eventTime := by native_decide

/-- Forward-shifted: R' > matrix E (theory-neutral temporal fact). -/
theorem forwardShifted_R_gt_matrix_E :
    embeddedSickForwardShifted.referenceTime > matrixSaid.eventTime := by native_decide

/-- Double access reading: present-under-past requires overlap with speech time. -/
theorem double_access_overlaps_speech :
    embeddedSickPresent.eventTime = embeddedSickPresent.speechTime := by native_decide

/-- Future-under-past: embedded R > matrix E. -/
theorem futureUnderPast_R_gt_matrix_E :
    embeddedWouldLeave.referenceTime > matrixSaid.eventTime := by native_decide

/-- Counterfactual: past morphology but R = P (present reference). -/
theorem counterfactual_present_reference :
    counterfactualWere.referenceTime = counterfactualWere.perspectiveTime := by native_decide

/-- Temporal de re: R < P (past reference relative to belief time). -/
theorem deRe_past_reference :
    temporalDeRe.referenceTime < temporalDeRe.perspectiveTime := by native_decide

/-- RC tense: past reference. -/
theorem rc_past_reference :
    rcWasTall.referenceTime < rcWasTall.perspectiveTime := by native_decide

/-- Modal past: past reference relative to modal eval time. -/
theorem modalPast_past_reference :
    modalPast.referenceTime < modalPast.perspectiveTime := by native_decide


-- ── Eventual target facts ──

/-- Indirect question: simultaneous frame has R = P. -/
theorem indirectQ_simultaneous_present :
    indirectQSimultaneous.isPresent := rfl

/-- Indirect question: shifted frame has R < P. -/
theorem indirectQ_shifted_past :
    indirectQShifted.referenceTime < indirectQShifted.perspectiveTime := by native_decide

/-- FID: perspective shifts without attitude verb. -/
theorem fid_perspective_shifted :
    fidGardenBeautiful.perspectiveTime = fidWalked.eventTime := by native_decide

/-- FID garden: R = P (simultaneous with character's experience). -/
theorem fid_garden_present :
    fidGardenBeautiful.isPresent := rfl

/-- Historical present: present morphology despite past event. -/
theorem historicalPresent_R_eq_P :
    historicalPresent.referenceTime = historicalPresent.perspectiveTime := rfl

/-- Historical present: event time ≠ speech time. -/
theorem historicalPresent_not_at_speech :
    historicalPresent.eventTime ≠ historicalPresent.speechTime := by native_decide

/-- Pluperfect: E < R < P (both perfect and past). -/
theorem pluperfect_E_lt_R_lt_P :
    pluperfectShifted.eventTime < pluperfectShifted.referenceTime ∧
    pluperfectShifted.referenceTime < pluperfectShifted.perspectiveTime := by
  constructor <;> native_decide

/-- Adjunct "before": adjunct event precedes matrix event. -/
theorem adjunct_precedes_matrix :
    adjunctBeforeLeft.eventTime < matrixWasHappy.eventTime := by native_decide

/-- Indexical shift: present tense at attitude time, not speech time. -/
theorem indexicalShift_at_attitude_time :
    indexicalShiftPresent.referenceTime = indexicalShiftPresent.perspectiveTime ∧
    indexicalShiftPresent.eventTime ≠ indexicalShiftPresent.speechTime := by
  constructor
  · rfl
  · native_decide



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

/-- Lifetime effects: past reference. -/
theorem lifetimeAristotle_past :
    lifetimeAristotle.referenceTime < lifetimeAristotle.perspectiveTime := by native_decide

/-- Fake past: past morphology but R = P (present reference). -/
theorem fakePast_present_reference :
    fakePastSubjunctive.referenceTime = fakePastSubjunctive.perspectiveTime := rfl

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


end Phenomena.Tense
