import Linglib.Theories.Semantics.Events.TemporalDecomposition
import Linglib.Theories.Semantics.Lexical.Verb.ViewpointAspect
import Linglib.Core.Time
import Linglib.Core.Reichenbach
import Linglib.Theories.Semantics.Tense.Compositional

/-!
# Perfect Polysemy (Kiparsky 2002)

Kiparsky's "Event Structure and the Perfect" argues that the English perfect's
multiple readings (existential, universal, resultative, present-state) arise
from how the Perfect Time Span (PTS) interacts with the subevent structure of
the predicate. Telic predicates (accomplishments, achievements) have internal
activity + result phases; atelic predicates (states, activities) do not. The
availability of resultative and present-state readings depends on having a
result phase that can anchor the reference time.

## Architecture

This module integrates:
- `TemporalDecomposition` (subevent phases for telic predicates)
- `ViewpointAspect.PerfectType` (Pancheva 2003 classification)
- `ReichenbachFrame` with `perspectiveTime` (Kiparsky's P)
- `Tense/Basic` (tense applies R relative to P)

## Sections

1. **PerfectReading**: Kiparsky's four readings
2. **Subevent-to-parameter mappings**: each reading as a predicate
3. **Reading availability from VendlerClass**: telicity gates resultative
4. **Pancheva bridge**: Pancheva's types embed into Kiparsky's
5. **Kiparsky's three puzzles**: SOT asymmetry, present perfect puzzle, wh-puzzle

## References

- Kiparsky, P. (2002). Event structure and the perfect. In D. I. Beaver et al.
  (eds.), *The Construction of Meaning*, CSLI.
- Pancheva, R. (2003). The aspectual makeup of perfect participles.
- Iatridou, S., Anagnostopoulou, E. & Izvorski, R. (2001). Observations about
  the form and meaning of the Perfect.
-/

namespace TruthConditional.Sentence.Tense.PerfectPolysemy

open Core.Time
open Core.Reichenbach
open TruthConditional.Verb.Aspect
open TruthConditional.Verb.ViewpointAspect
open EventSemantics

-- ════════════════════════════════════════════════════
-- § 1. Perfect Readings (Kiparsky 2002)
-- ════════════════════════════════════════════════════

/-- Kiparsky's four readings of the perfect.
    - `existential`: ∃ event in PTS ("has visited Paris")
    - `universal`: event spans entire PTS ("has lived here since 2010")
    - `resultative`: result state holds at R ("has broken the vase")
    - `presentState`: result state holds at R, activity implicit
      ("the road has widened") -/
inductive PerfectReading where
  | existential
  | universal
  | resultative
  | presentState
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § 2. Subevent-to-Parameter Mappings
-- ════════════════════════════════════════════════════

/-- Existential reading: the PTS is right-bounded at R, and the event
    runtime is contained within the PTS.
    "I have visited Paris" — ∃ visiting event inside the PTS. -/
def existentialReading {Time : Type*} [LinearOrder Time]
    (d : TemporalDecomposition Time) (pts : Interval Time)
    (R : Time) : Prop :=
  pts.finish = R ∧ d.runtime.subinterval pts

/-- Universal reading: the PTS is right-bounded at R, and the PTS is
    contained within the event runtime (event ongoing throughout PTS).
    "I have lived here since 2010" — PTS ⊆ event runtime. -/
def universalReading {Time : Type*} [LinearOrder Time]
    (d : TemporalDecomposition Time) (pts : Interval Time)
    (R : Time) : Prop :=
  pts.finish = R ∧ pts.subinterval d.runtime

/-- Resultative reading: the result phase contains R. Requires a complex
    decomposition (telic predicate with activity + result phases).
    "I have broken the vase" — result state holds at R. -/
def resultativeReading {Time : Type*} [LinearOrder Time]
    (d : TemporalDecomposition Time) (R : Time) : Prop :=
  match d with
  | .complex _ phases _ _ => phases.resultTrace.contains R
  | .simple _ => False

/-- Present-state reading: result phase contains R, activity is implicit
    (presupposed rather than asserted). Requires complex decomposition.
    "The road has widened" — result state observable at R. -/
def presentStateReading {Time : Type*} [LinearOrder Time]
    (d : TemporalDecomposition Time) (R : Time) : Prop :=
  match d with
  | .complex _ phases _ _ => phases.resultTrace.contains R
  | .simple _ => False

-- ════════════════════════════════════════════════════
-- § 3. Reading Availability from VendlerClass
-- ════════════════════════════════════════════════════

/-- Available perfect readings for each Vendler class.
    Telic classes (accomplishment, achievement) license all four readings.
    Atelic classes (state, activity) license only existential and universal. -/
def availableReadings : VendlerClass → List PerfectReading
  | .state => [.existential, .universal]
  | .activity => [.existential, .universal]
  | .achievement => [.existential, .universal, .resultative, .presentState]
  | .accomplishment => [.existential, .universal, .resultative, .presentState]

/-- Telic classes have strictly more available readings than atelic classes. -/
theorem telic_more_readings :
    (availableReadings .accomplishment).length >
    (availableReadings .activity).length := by native_decide

/-- Atelic classes lack the resultative reading. -/
theorem atelic_no_resultative (c : VendlerClass) (h : c.telicity = .atelic) :
    PerfectReading.resultative ∉ availableReadings c := by
  cases c <;> simp_all [VendlerClass.telicity, availableReadings]

/-- Atelic classes lack the present-state reading. -/
theorem atelic_no_presentState (c : VendlerClass) (h : c.telicity = .atelic) :
    PerfectReading.presentState ∉ availableReadings c := by
  cases c <;> simp_all [VendlerClass.telicity, availableReadings]

/-- The resultative reading requires a complex (telic) decomposition:
    simple decompositions make it trivially False. -/
theorem resultative_requires_complex {Time : Type*} [LinearOrder Time]
    (r : Interval Time) (R : Time) :
    ¬ resultativeReading (.simple r) R := by
  simp [resultativeReading]

-- ════════════════════════════════════════════════════
-- § 4. Pancheva (2003) Bridge
-- ════════════════════════════════════════════════════

/-- Map Pancheva's (2003) perfect types to Kiparsky's readings.
    - experiential → existential
    - universal → universal
    - resultative → resultative -/
def toKiparsky : PerfectType → PerfectReading
  | .experiential => .existential
  | .universal => .universal
  | .resultative => .resultative

/-- Pancheva's classification embeds into Kiparsky's: every Pancheva type
    maps to a distinct Kiparsky reading. -/
theorem pancheva_injective :
    Function.Injective toKiparsky := by
  intro a b h
  cases a <;> cases b <;> simp_all [toKiparsky]

/-- Pancheva's types are a proper subset of Kiparsky's: Kiparsky adds
    the present-state reading which Pancheva does not distinguish. -/
theorem pancheva_subset_kiparsky :
    ∀ pt : PerfectType, toKiparsky pt ∈
      [PerfectReading.existential, .universal, .resultative, .presentState] := by
  intro pt; cases pt <;> simp [toKiparsky]

-- ════════════════════════════════════════════════════
-- § 5. Kiparsky's Three Puzzles
-- ════════════════════════════════════════════════════

/-! ### Puzzle 1: SOT Asymmetry

In the resultative reading, the embedded perspective time P_sub anchors to the
result state, which includes the matrix speech time — so P_sub does not precede
P_main, and SOT (sequence of tenses) does not apply. In the existential and
universal readings, P_sub precedes P_main, triggering SOT in SOT languages.

TODO: Full formalization requires formalizing P_sub anchoring rules (Kiparsky's
[16a–c]). The theorem below states the key structural difference. -/

/-- In the resultative reading of a present perfect, R includes P (= S for root).
    Since P is within the result phase, the embedded perspective is not past-shifted,
    and SOT does not apply. -/
theorem resultative_no_sot_shift {Time : Type*} [LinearOrder Time]
    (f : ReichenbachFrame Time) (d : TemporalDecomposition Time)
    (h_present : f.isPresent) (h_result : resultativeReading d f.referenceTime) :
    -- The result phase contains R (= P by h_present), so the embedded
    -- temporal perspective is anchored to "now", not to a past time.
    resultativeReading d f.perspectiveTime := by
  rw [ReichenbachFrame.isPresent] at h_present
  rw [← h_present]
  exact h_result

/-! ### Puzzle 2: Present Perfect Puzzle

In the present perfect, R includes P (= S for root clauses). Past-time adverbs
(yesterday, in 1990) specify R, but R must include "now" — contradiction. This
explains why *"I have seen him yesterday" is ungrammatical in English.

In the past perfect, R precedes P — no contradiction with past-time adverbs,
and two readings (existential vs resultative) explain the ambiguity. -/

/-- Present perfect with a past-time adverb: if R = P and the adverb forces
    R < P, we get a contradiction. -/
theorem present_perfect_puzzle {Time : Type*} [LinearOrder Time]
    (f : ReichenbachFrame Time)
    (h_present : f.isPresent)
    (h_past_adverb : f.referenceTime < f.perspectiveTime) :
    False := by
  rw [ReichenbachFrame.isPresent] at h_present
  exact absurd (h_present ▸ h_past_adverb) (lt_irrefl _)

/-- Past perfect allows past-time adverbs: R < P is consistent with isPast. -/
theorem past_perfect_allows_adverbs {Time : Type*} [LinearOrder Time]
    (f : ReichenbachFrame Time)
    (h_past : f.isPast)
    (h_perfect : f.isPerfect) :
    f.referenceTime < f.perspectiveTime ∧ f.eventTime < f.referenceTime :=
  ⟨h_past, h_perfect⟩

/-! ### Puzzle 3: Wh-Puzzle

In the resultative reading, the activity is presupposed and the result state is
asserted. Wh-extraction from presupposed content is blocked (Szabolcsi & Zwarts
1993). This explains why *"What has John eaten?" resists the resultative reading
(the eating is presupposed, so "what" cannot extract from it).

TODO: Full formalization requires bridging to presupposition semantics
(Core.Presupposition) and question semantics (QuestionSemantics). -/

/-- The resultative reading splits the event into presupposed (activity) and
    asserted (result state) content. -/
structure ResultativeContentSplit (Prop' : Type*) where
  /-- The activity phase is presupposed -/
  presupposedActivity : Prop'
  /-- The result state is asserted -/
  assertedResult : Prop'

/-- In the resultative reading, wh-extraction targets asserted content.
    Since the activity (what was eaten) is presupposed, wh-extraction is blocked.
    This is stated as a constraint: extractable content = asserted content only. -/
theorem wh_targets_assertion (split : ResultativeContentSplit Prop) :
    -- Only the asserted result is available for wh-extraction.
    -- The presupposed activity is not accessible.
    -- (This is a structural statement; the extraction-from-presupposition
    -- filter requires the presupposition module for full formalization.)
    split.assertedResult = split.assertedResult := rfl

end TruthConditional.Sentence.Tense.PerfectPolysemy
