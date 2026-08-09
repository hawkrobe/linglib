import Linglib.Semantics.Modality.TemporalAxes
import Linglib.Semantics.Modality.EventRelativity
import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.Modality.ActualityEntailments
import Linglib.Data.Examples.Hacquard2006

/-!
# Hacquard 2006: Aspects of Modality

[hacquard-2006]: modals are relative to an *event* of evaluation, and the
event fixes both the individual and the time the accessibility relation is
keyed to — its holder and temporal trace. A high modal (above Asp) is bound
by the speech event in matrix clauses and by the attitude event under
attitude verbs; a low modal (below Asp) is bound by aspect to the VP event,
whose time is the one provided by tense. Root modals under perfective yield
actuality entailments ([bhatt-1999]'s discovery, extended to French and
Italian); epistemics, being above aspect, are immune.

Substrate note: the event-relative machinery (`EventBinder`,
`ModalPosition`, `EventProjection`, content licensing) lives in
`Semantics/Modality/EventRelativity.lean`, anchored to the journal version
[hacquard-2010]; this file uses those project-canonical types.

## Main results

* `positionPerspective`, `withAttitude_shifts_perspective` — the temporal
  perspective ([condoravdi-2002]) projected from the anchoring event, via
  `ModalPosition.defaultBinder` / `withAttitude`.
* `epistemic_reading_possible`, `goal_reading_necessary` — the two readings
  of "Jane a dû prendre le train" (201) from one modal entry.
* `aspect_bound_epistemic_necessity` — contentful complements license
  aspect-bound epistemics (246)–(248).
* `data_matches_position_theory` — the perfective/imperfective actuality
  split across `Data/Examples/Hacquard2006.json` rows matches the
  position × aspect prediction.
-/

namespace Hacquard2006

open Modality Modality.Kratzer
open Semantics.Aspect (Perfectivity)
open Data.Examples (LinguisticExample)

/-! ### Position → temporal perspective

The anchoring event fixes the evaluation time: "the agent and temporal
trace of the speech event" for speech-bound modals, "the subject and the
time provided by Tense" for aspect-bound ones. The perspective map factors
through the substrate's binding maps; its codomain has no future case, so
no position yields a future perspective. -/

/-- Perspective of the anchoring event in a past-tense clause: only the
speech event sits at utterance time. -/
def binderPerspective : EventBinder → TemporalPerspective
  | .speechAct => .present
  | _ => .past

/-- Perspective from modal position in a matrix clause. -/
def positionPerspective (pos : ModalPosition) : TemporalPerspective :=
  binderPerspective pos.defaultBinder

/-- The same modal (*devoir*, *pouvoir*) gets different temporal
perspectives from different structural positions. -/
theorem position_determines_perspective :
    positionPerspective .aboveAsp ≠ positionPerspective .belowAsp := nofun

/-- Embedded under a past attitude, a high modal is keyed to the attitude
time: the perspective tracks the binder, not the position. -/
theorem withAttitude_shifts_perspective :
    binderPerspective ModalPosition.aboveAsp.withAttitude ≠
    binderPerspective ModalPosition.aboveAsp.defaultBinder := nofun

/-! ### Perspective and aspect scope

Position fixes the temporal *perspective* and the modal/aspect *scope* at
once. On [condoravdi-2002]'s account this pair determines which modal base
types are available: present perspective + MODAL > PERF yields a settled
past property (epistemic only); past perspective + PERF > MODAL yields an
unsettled future property (metaphysical available). That machinery lives in
`Semantics/Modality/HistoricalAlternatives.lean`; chaining the two halves
into one composition theorem is left as follow-up. -/

/-- Position determines both perspective and aspect scope: high modals pair
present perspective with MODAL > ASP, low modals pair past perspective with
ASP > MODAL. -/
theorem position_determines_modal_base_type :
    (positionPerspective .aboveAsp = .present ∧
     toAspectScope .aboveAsp = .modalOverAspect) ∧
    (positionPerspective .belowAsp = .past ∧
     toAspectScope .belowAsp = .aspectOverModal) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-! ### Worked example: "Jane a dû prendre le train" (201)

`Examples.ex201` is ambiguous between an epistemic and a goal-oriented
reading. The two readings differ only in the event that anchors the modal:

| Reading | Event | holder(e) | τ(e) | Modal domain |
|---------|-------|-----------|------|--------------|
| Epistemic | speech act | speaker | now | speaker's evidence now |
| Goal-oriented | VP event | Jane | then | Jane's circumstances then |

The same modal *devoir* gets different parameters from different event
bindings; no lexical ambiguity is needed. -/

/-- Two individuals in the train scenario. -/
inductive TrainPerson where | speaker | jane
  deriving DecidableEq, Repr, Inhabited

/-- Two time points: speech time and the past event time. -/
inductive TrainTime where | now | then
  deriving DecidableEq, Repr, Inhabited

/-- Two events: the speech act and Jane's train-taking. -/
inductive TrainEvent where | speechAct | janesTaking
  deriving DecidableEq, Repr

/-- The event projection for the train scenario: the speech act projects
to (speaker, now), the VP event to (Jane, then). -/
def trainProjection : EventProjection TrainEvent TrainPerson TrainTime where
  holder
    | .speechAct => .speaker
    | .janesTaking => .jane
  time
    | .speechAct => .now
    | .janesTaking => .then

/-- Speech event projects to (speaker, now). -/
theorem speech_projects_to_speaker_now :
    trainProjection.toPair .speechAct = ⟨.speaker, .now⟩ := rfl

/-- VP event projects to (Jane, then). -/
theorem vp_projects_to_jane_then :
    trainProjection.toPair .janesTaking = ⟨.jane, .then⟩ := rfl

/-- The same modal (*devoir*) gets different individual-time pairs from
different event bindings: the epistemic reading relativizes to the
speaker's evidence now, the goal-oriented reading to Jane's circumstances
then. -/
theorem same_modal_different_params :
    trainProjection.toPair .speechAct ≠
    trainProjection.toPair .janesTaking := by decide

/-- Two worlds: one where Jane took the train, one where she didn't. -/
inductive TrainWorld where | took | didnt
  deriving DecidableEq, Repr, Inhabited

/-- Epistemic anchoring (via speech event): the speaker considers both
worlds possible (no decisive evidence either way), so the background is
empty at every projection. -/
private def epistemicBg : TrainPerson → TrainTime → ConvBackground TrainWorld :=
  λ _ _ _ => []

/-- Goal-oriented anchoring (via VP event): given Jane's circumstances at
the past time, only the took-world is compatible. -/
private def goalBg : TrainPerson → TrainTime → ConvBackground TrainWorld
  | .jane, .then, _ => [λ w => w = .took]
  | _, _, _ => []

/-- The epistemic anchoring function (factored through projection). -/
private def fEpistemicTrain : AnchoringFn TrainEvent TrainWorld :=
  factoredAnchoring trainProjection epistemicBg

/-- The goal-oriented anchoring function (factored through projection). -/
private def fGoalTrain : AnchoringFn TrainEvent TrainWorld :=
  factoredAnchoring trainProjection goalBg

/-- Epistemic reading: modal anchored to the speech event.
`◇_{f(e₀)} took` holds because the speaker considers `took` possible. -/
theorem epistemic_reading_possible :
    simplePossibility (fEpistemicTrain .speechAct) (· = .took) .took :=
  ⟨.took, by simp [fEpistemicTrain, factoredAnchoring, epistemicBg, kratzerR], rfl⟩

/-- Goal-oriented reading: modal anchored to the VP event.
`□_{f(e)} took` holds because only `took` is accessible. -/
theorem goal_reading_necessary :
    simpleNecessity (fGoalTrain .janesTaking) (· = .took) .took := by
  intro w' hw'
  simpa [fGoalTrain, factoredAnchoring, trainProjection, goalBg,
    accessibleWorlds, kratzerR] using hw'

/-- The goal-oriented anchoring restricts the accessible worlds more than
the epistemic one: the didnt-world is epistemically accessible but not
goal-accessible. Both readings use the same modal; the difference comes
entirely from the event bindings. -/
theorem goal_restricts_more :
    kratzerR (fEpistemicTrain .speechAct) .took .didnt ∧
    ¬ kratzerR (fGoalTrain .janesTaking) .took .didnt := by
  constructor <;>
    simp [fEpistemicTrain, fGoalTrain, factoredAnchoring, trainProjection,
      epistemicBg, goalBg, kratzerR]

/-! ### Aspect-bound epistemics: (246)–(248)

A low modal is normally barred from epistemic readings: the event provided
by aspect lacks propositional content (246) — the substrate's
`position_determines_epistemic`. But when the complement itself supplies a
contentful attitude event, aspect can bind it: in `Examples.ex247b` "Jane
a pu penser que Darcy aimait Lizzie", the LF where the modal is merged
below tense relativizes it to Jane's thinking event, reporting an
epistemic state of the *subject* at a past belief state — the salient
speech-bound reading instead reports the speaker's evidence. -/

/-- Two worlds for the (247b) scenario. -/
inductive DarcyWorld where | loves | lovesNot
  deriving DecidableEq, Repr, Inhabited

/-- Two candidate binders for the modal in (247b): the matrix speech act
and Jane's thinking event. -/
inductive PenserEvent where | speech | thinking
  deriving DecidableEq, Repr

/-- Anchoring for (247b): the speech event carries the speaker's undecided
evidence (both worlds accessible); the thinking event carries CON(e) =
Jane's beliefs, which settle that Darcy loved Lizzie. -/
private def fPenser : AnchoringFn PenserEvent DarcyWorld
  | .speech, _ => []
  | .thinking, _ => [λ w => w = .loves]

/-- Aspect-bound epistemic: the modal bound to Jane's thinking event
expresses an epistemic necessity for Jane — under CON(thinking), only the
loves-world is accessible. -/
theorem aspect_bound_epistemic_necessity :
    simpleNecessity (fPenser .thinking) (· = .loves) .lovesNot := by
  intro w' hw'
  simpa [fPenser, accessibleWorlds, kratzerR] using hw'

/-- Speech-bound epistemic: bound to the speech event, both worlds remain
possible for the speaker. -/
theorem speech_bound_both_possible :
    simplePossibility (fPenser .speech) (· = .loves) .lovesNot ∧
    simplePossibility (fPenser .speech) (· = .lovesNot) .lovesNot :=
  ⟨⟨.loves, by simp [fPenser, kratzerR], rfl⟩,
   ⟨.lovesNot, by simp [fPenser, kratzerR], rfl⟩⟩

/-- Same modal, different binders, different epistemic domains: the
lovesNot-world is accessible from the speech event but not from Jane's
thinking event. -/
theorem binding_determines_epistemic_domain :
    kratzerR (fPenser .speech) .lovesNot .lovesNot ∧
    ¬ kratzerR (fPenser .thinking) .lovesNot .lovesNot := by
  constructor <;> simp [fPenser, kratzerR]

/-! ### Actuality entailments

Root modals with perfective aspect entail their complement; with
imperfective they do not ([bhatt-1999]; French and Italian extensions in
[hacquard-2006]). The stimuli live in `Data/Examples/Hacquard2006.json`:
the French pairs (1) and (22)/(23), the Italian pair (22b)/(23b), and
Bhatt's English adverbial pair (2). Bhatt's primary Hindi and Greek data
are not reproduced in the dissertation (its fn. 7), and its own Greek
discussion (318) defers the language's complement-internal aspect, so no
Hindi or Greek rows are included here. -/

/-- Aspect and observed actuality entailment of an example row, read off
its `paperFeatures`; `none` for rows without the aspect contrast. -/
def aeDatum (e : LinguisticExample) : Option (Perfectivity × Bool) :=
  match e.feature? "aspect", e.feature? "actualityEntailment" with
  | some "perfective", some ae => some (.perfective, ae == "true")
  | some "imperfective", some ae => some (.imperfective, ae == "true")
  | _, _ => none

/-- Positive witness: the perfective French pair member carries the
entailment. -/
theorem ex22a_perfective_entails :
    aeDatum Examples.ex22a = some (.perfective, true) := rfl

/-- Every datum's observed entailment matches the position × aspect
prediction for root modals (all rows are root: below Asp, so perfective
forces actualization). -/
theorem data_matches_position_theory :
    (Examples.all.filterMap aeDatum).all
      (λ d => d.2 == actualityEntailmentPredicted .belowAsp d.1) = true := by
  decide

end Hacquard2006
