import Linglib.Semantics.Modality.TemporalAxes
import Linglib.Semantics.Modality.EventRelativity
import Linglib.Semantics.Aspect.Basic
import Linglib.Semantics.Modality.ActualityEntailments
import Linglib.Studies.Condoravdi2002
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
* `high_position_epistemic_only`, `low_position_counterfactual_available` —
  [condoravdi-2002]'s might-have ambiguity (176) recast positionally: the
  high position pairs with the epistemic reading's perspective and its
  settled prejacent blocks the metaphysical base; the low position pairs
  with the counterfactual reading's, whose base only widens.
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

The anchoring event fixes the evaluation time: speech-bound modals sit at
the utterance time, aspect-bound ones at the time provided by tense. The
map factors through the substrate's binding maps, and its codomain has no
future case. -/

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

/-! ### Condoravdi's ambiguity from position

"They might (already/still) have won the game" (176): the dissertation
recasts [condoravdi-2002]'s scopal ambiguity positionally; composing with
the settledness machinery in `Studies/Condoravdi2002.lean` derives which
modal bases survive at each position. -/

section CondoravdiBridge

open Condoravdi2002 HistoricalAlternatives

variable {W Time : Type*} [LinearOrder Time]

/-- From the high position, "might have" is epistemic-only: the high
perspective is exactly the epistemic reading's, and the back-shifted
prejacent, being settled, admits no diverse metaphysical base
(`modal_over_perf_blocks_metaphysical`). -/
theorem high_position_epistemic_only
    (history : HistoricalAlternatives W Time) (MB : W → Time → Set W)
    (cg : Set W) (now : Time) (P : W → Event Time → Prop)
    (hMB : ∀ w ∈ cg, ∀ w' ∈ MB w now, histEquiv history now w w')
    (hSettled : settled history cg now (λ w => perf .dynamic P w now)) :
    positionPerspective .aboveAsp = ModalReading.epistemic.perspective ∧
    ¬ diverse MB cg now (λ w => perf .dynamic P w now) :=
  ⟨rfl, modal_over_perf_blocks_metaphysical history MB cg now P hMB hSettled⟩

/-- From the low position, the counterfactual reading is available: the low
perspective is exactly the counterfactual reading's, and moving the
evaluation time back only widens the metaphysical base
(`counterfactual_widens_domain`). -/
theorem low_position_counterfactual_available
    (history : HistoricalAlternatives W Time)
    (hBC : history.backwardsClosed) (w : W) {t' now : Time} (hle : t' ≤ now) :
    positionPerspective .belowAsp = ModalReading.counterfactual.perspective ∧
    metaphysicalBase history w now ⊆ metaphysicalBase history w t' :=
  ⟨rfl, counterfactual_widens_domain history hBC w hle⟩

end CondoravdiBridge

/-! ### Worked example: "Jane a dû prendre le train" (201)

`Examples.ex201`'s two readings differ only in the anchoring event:

| Reading | Event | holder(e) | τ(e) | Modal domain |
|---------|-------|-----------|------|--------------|
| Epistemic | speech act | speaker | now | speaker's evidence now |
| Goal-oriented | VP event | Jane | then | Jane's circumstances then |
-/

/-- Two individuals in the train scenario. -/
inductive TrainPerson where | speaker | jane
  deriving DecidableEq, Repr

/-- Speech time and the past event time. -/
inductive TrainTime where | now | then
  deriving DecidableEq, Repr

/-- The speech act and Jane's train-taking. -/
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

/-- One world where Jane took the train, one where she didn't. -/
inductive TrainWorld where | took | didnt
  deriving DecidableEq, Repr

/-- The scenario's facts by projected pair: the speaker's evidence now is
undecided; Jane's circumstances then force the train. -/
private def trainBg : TrainPerson → TrainTime → ConvBackground TrainWorld
  | .jane, .then, _ => [λ w => w = .took]
  | _, _, _ => []

/-- The single anchoring for *devoir*: no lexical ambiguity, just `trainBg`
read through the projection. -/
private def trainAnchoring : AnchoringFn TrainEvent TrainWorld :=
  factoredAnchoring trainProjection trainBg

/-- `took` is possible when the modal is anchored to the speech event —
the epistemic reading. -/
theorem epistemic_reading_possible :
    simplePossibility (trainAnchoring .speechAct) (· = .took) .took :=
  ⟨.took, fun _ h => (List.not_mem_nil h).elim, rfl⟩

/-- `took` is necessary when the modal is anchored to the VP event — the
goal-oriented reading. -/
theorem goal_reading_necessary :
    simpleNecessity (trainAnchoring .janesTaking) (· = .took) .took :=
  fun _ h => h _ (List.Mem.head _)

/-- The didnt-world is accessible from the speech event but not from the
VP event. -/
theorem same_modal_different_domains :
    kratzerR (trainAnchoring .speechAct) .took .didnt ∧
    ¬ kratzerR (trainAnchoring .janesTaking) .took .didnt :=
  ⟨fun _ h => (List.not_mem_nil h).elim,
   fun h => nomatch h _ (List.Mem.head _)⟩

/-! ### Aspect-bound epistemics (246)–(248)

Low modals lack epistemic readings because aspect's event has no content
(the substrate's `position_determines_epistemic`) — unless the complement
supplies a contentful attitude event: `Examples.ex247b`'s aspect-bound LF
reports Jane's past belief state, its speech-bound LF the speaker's
evidence. -/

/-- Two worlds for the (247b) scenario. -/
inductive DarcyWorld where | loves | lovesNot
  deriving DecidableEq, Repr

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

/-- Bound to Jane's thinking event, `loves` is necessary — an epistemic
necessity for Jane. -/
theorem aspect_bound_epistemic_necessity :
    simpleNecessity (fPenser .thinking) (· = .loves) .lovesNot :=
  fun _ h => h _ (List.Mem.head _)

/-- Bound to the speech event, both worlds remain possible for the
speaker. -/
theorem speech_bound_both_possible :
    simplePossibility (fPenser .speech) (· = .loves) .lovesNot ∧
    simplePossibility (fPenser .speech) (· = .lovesNot) .lovesNot :=
  ⟨⟨.loves, fun _ h => (List.not_mem_nil h).elim, rfl⟩,
   ⟨.lovesNot, fun _ h => (List.not_mem_nil h).elim, rfl⟩⟩

/-- The lovesNot-world is accessible from the speech event but not from
Jane's thinking event. -/
theorem binding_determines_epistemic_domain :
    kratzerR (fPenser .speech) .lovesNot .lovesNot ∧
    ¬ kratzerR (fPenser .thinking) .lovesNot .lovesNot :=
  ⟨fun _ h => (List.not_mem_nil h).elim,
   fun h => nomatch h _ (List.Mem.head _)⟩

/-! ### Actuality entailments

Root modals entail their complement under perfective aspect but not
imperfective ([bhatt-1999]; French/Italian extensions in [hacquard-2006]).
No Hindi or Greek rows: the dissertation reproduces neither (fn. 7) and
defers Greek's complement-internal aspect (318). -/

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
