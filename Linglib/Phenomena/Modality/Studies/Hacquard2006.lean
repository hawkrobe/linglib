import Linglib.Core.Modality.TemporalAxes
import Linglib.Theories.Semantics.Modality.EventRelativity
import Linglib.Theories.Semantics.Modality.Temporal
import Mathlib.Data.List.Defs
import Linglib.Theories.Semantics.Tense.Aspect.Core
import Linglib.Theories.Semantics.Modality.ActualityEntailments
import Linglib.Phenomena.Modality.Studies.Condoravdi2002

/-!
# Event Projection → Temporal Orientation

@cite{hacquard-2006} @cite{hacquard-2010} @cite{condoravdi-2002} @cite{kratzer-2012}Derives the temporal orientation of modals from event projection. High modals get the speech time (present
perspective); low modals get the event time (past perspective).

## The Pattern

| Position | Event binder | holder(e) | τ(e) | Temporal orientation |
|----------|-------------|-----------|------|---------------------|
| High (above Asp) | speech act e₀ | speaker | speech time (now) | Present |
| Low (below Asp) | VP event e₂ | agent | event time (then) | Past/event-local |

## Hacquard's Derivation

Individual-time pairs are DERIVED from events via projection functions
`holder(e)` and `τ(e)`. Since high modals bind to the speech event and
low modals bind to the VP event, their temporal parameters differ:

- "Jane a dû prendre le train" (@cite{hacquard-2006}, (201)):
  - Epistemic (high): τ(e₀) = now → "Given my evidence NOW,..."
  - Root (low): τ(e₂) = then → "Given Jane's circumstances THEN,..."

This connects `EventProjection` (EventRelativity §11) to the temporal
modal evaluation framework in `Temporal.lean`.

-/

namespace Hacquard2006

open Semantics.Modality.EventRelativity
open Semantics.Modality.Temporal
open Core.Modality (TemporalOrientation)


-- ════════════════════════════════════════════════════
-- § 1. Temporal Orientation Type
-- ════════════════════════════════════════════════════

/-! @cite{hacquard-2006} derives present vs. past from modal position
(§ 3). @cite{klecha-2016} adds future: derived not from position but
from the modal base kind (CIR permits future orientation). The
canonical 3-value `TemporalOrientation` lives in
`Core/Modality/TemporalAxes.lean` and is opened above. -/

/-- A time type for the orientation examples. -/
inductive OTime where
  /-- Speech time (= utterance time) -/
  | now
  /-- Past event time -/
  | then_
  deriving DecidableEq, Repr


-- ════════════════════════════════════════════════════
-- § 2. Event Projection Determines Temporal Orientation
-- ════════════════════════════════════════════════════

/-- Two events: speech act and VP event. -/
inductive OrientationEvent where
  /-- The speech event (e₀) -/
  | speech
  /-- The VP event (e₂) -/
  | vpEvent
  deriving DecidableEq, Repr

/-- Individuals: speaker and the described event's agent. -/
inductive OrientationPerson where
  | speaker
  | agent
  deriving DecidableEq, Repr

/-- Event projection for the temporal orientation scenario.
Speech events project to (speaker, now); VP events project to (agent, then). -/
def orientationProjection : EventProjection OrientationEvent OrientationPerson OTime where
  holder
    | .speech => .speaker
    | .vpEvent => .agent
  time
    | .speech => .now
    | .vpEvent => .then_

/-- Speech event projects to speech time (now). -/
theorem speech_projects_to_now :
    orientationProjection.time .speech = .now := rfl

/-- VP event projects to event time (then). -/
theorem vp_projects_to_then :
    orientationProjection.time .vpEvent = .then_ := rfl


-- ════════════════════════════════════════════════════
-- § 3. Position → Temporal Orientation
-- ════════════════════════════════════════════════════

/-- Derive temporal orientation from modal position, via event binding.

High modals (above Asp) bind to the speech event → τ(e₀) = now → present.
Low modals (below Asp) bind to the VP event → τ(e₂) = then → past. -/
def positionToOrientation (pos : ModalPosition) : TemporalOrientation :=
  match pos with
  | .aboveAsp => .present    -- speech event time
  | .belowAsp => .past       -- VP event time

/-- High modals have present temporal orientation. -/
theorem high_present :
    positionToOrientation .aboveAsp = .present := rfl

/-- Low modals have past temporal orientation. -/
theorem low_past :
    positionToOrientation .belowAsp = .past := rfl

/-- The same modal (*devoir*, *pouvoir*) has different temporal perspectives
depending on its structural position — derived from event projection,
not stipulated. -/
theorem position_determines_orientation :
    positionToOrientation .aboveAsp ≠ positionToOrientation .belowAsp := by decide


-- ════════════════════════════════════════════════════
-- § 4. Bridge to Temporal.lean
-- ════════════════════════════════════════════════════

/-- The temporal orientation derived from event projection connects to
`Temporal.lean`'s time-indexed conversational backgrounds.

When the modal binds to event e with τ(e) = t, the conversational
background is evaluated at time t: `f(w,t)`. The time IS the event's
temporal trace. Event projection subsumes time-indexing: rather than
stipulating which time to evaluate at, the time is projected from
whichever event binds the modal. -/
theorem event_projection_subsumes_temporal :
    -- Speech event → t = now
    orientationProjection.time .speech = .now ∧
    -- VP event → t = then
    orientationProjection.time .vpEvent = .then_ ∧
    -- Different events → different times → different backgrounds
    orientationProjection.time .speech ≠ orientationProjection.time .vpEvent := by
  exact ⟨rfl, rfl, by decide⟩


-- ════════════════════════════════════════════════════
-- § 5. Worked Example: "Jane a dû prendre le train"
-- ════════════════════════════════════════════════════

/-! (@cite{hacquard-2006}, (201)): two readings of the same sentence with
different temporal perspectives, derived from event binding.

Epistemic (high): "Given MY evidence NOW, Jane must have taken the train."
  → modal bound to speech event → τ(e₀) = speech time = now
  → background evaluated at speech time

Root (low): "Given JANE'S circumstances THEN, Jane had to take the train."
  → modal bound to VP event → τ(e₂) = event time = then
  → background evaluated at event time -/

/-- The full derivation chain for "Jane a dû prendre le train":
event binding → event projection → temporal orientation.

This is the payoff of event-relative modality: the same modal gets
different temporal perspectives from different event bindings,
without any stipulation about temporal orientation. -/
theorem jane_train_orientation :
    -- Epistemic reading: speech event → present orientation
    orientationProjection.time .speech = .now ∧
    positionToOrientation .aboveAsp = .present ∧
    -- Root reading: VP event → past orientation
    orientationProjection.time .vpEvent = .then_ ∧
    positionToOrientation .belowAsp = .past :=
  ⟨rfl, rfl, rfl, rfl⟩


-- ════════════════════════════════════════════════════
-- § 6. Hacquard ↔ Klecha comparison
-- ════════════════════════════════════════════════════

/-! @cite{hacquard-2006} and @cite{klecha-2016} explain different aspects of
temporal orientation:

- **Hacquard**: Position (high/low) determines whether the conversational
  background is evaluated at speech time (present) or event time (past).
  This explains the epistemic/root contrast.

- **Klecha**: Modal base kind (DOX/CIR) determines whether future-oriented
  readings are available. DOX (doxastic) constrains RT ≤ EvalT (upper limit);
  CIR (circumstantial) permits RT > EvalT (future orientation).

The two theories are complementary: Hacquard tells you WHAT time the modal
base is evaluated at; Klecha tells you WHICH DIRECTION of temporal reference
is available from that time. -/

/-- Hacquard's derivation covers present and past orientation.
    Future orientation is NOT derived from position — it requires
    @cite{klecha-2016}'s modal base analysis. -/
theorem position_covers_present_past :
    positionToOrientation .aboveAsp = .present ∧
    positionToOrientation .belowAsp = .past :=
  ⟨rfl, rfl⟩

/-- Hacquard's positional analysis does not derive future orientation.
    Future orientation is orthogonal to position — it is determined by the
    modal base kind (CIR), not by where the modal is merged. -/
theorem future_not_from_position :
    positionToOrientation .aboveAsp ≠ .future ∧
    positionToOrientation .belowAsp ≠ .future := by
  exact ⟨by decide, by decide⟩


/-! ## Bridge: Hacquard ↔ @cite{condoravdi-2002}

@cite{hacquard-2006} determines which time the modal base is evaluated at
(via event projection); @cite{condoravdi-2002} determines what modal base
types are available at that time (via settledness and diversity).

The bridge: position determines perspective (Hacquard), and perspective
determines available modal base types (Condoravdi). High modals get
present perspective → MODAL > PERF scope → `settled_not_diverse` blocks
metaphysical. Low modals get past perspective → PERF > MODAL scope →
`counterfactual_widens_domain` widens the metaphysical domain. -/

open Condoravdi2002 (Perspective)
open Semantics.Modality.ActualityEntailments (AspectModalScope toAspectScope)

/-- Map Hacquard's temporal orientation to Condoravdi's temporal
    perspective. Future orientation (Klecha 2016) has no Condoravdi
    analogue — it is orthogonal to the scope–modality correlation. -/
def toPerspective : TemporalOrientation → Option Perspective
  | .present => some .present
  | .past    => some .past
  | .future  => none

/-- High modals (above Asp) have Condoravdi's present perspective. -/
theorem high_modal_present_perspective :
    toPerspective (positionToOrientation .aboveAsp) = some .present := rfl

/-- Low modals (below Asp) have Condoravdi's past perspective. -/
theorem low_modal_past_perspective :
    toPerspective (positionToOrientation .belowAsp) = some .past := rfl

/-- The key derivation chain: position determines both perspective AND
    aspect scope, and these two together determine which modal base
    types are available.

    - High (above Asp): present perspective + modal over aspect.
      MODAL > PERF scoping → the property under the modal is past →
      settled → diversity fails → metaphysical blocked → epistemic only.

    - Low (below Asp): past perspective + aspect over modal.
      PERF > MODAL scoping → the property under the modal is future
      (of the past event time) → not settled → diversity satisfiable →
      metaphysical available.

    This connects Hacquard's structural account to Condoravdi's temporal
    one without either stipulating anything. -/
theorem position_determines_modal_base_type :
    -- High → present perspective + MODAL > ASP (= epistemic scope)
    (toPerspective (positionToOrientation .aboveAsp) = some .present ∧
     toAspectScope .aboveAsp = .modalOverAspect) ∧
    -- Low → past perspective + ASP > MODAL (= root scope)
    (toPerspective (positionToOrientation .belowAsp) = some .past ∧
     toAspectScope .belowAsp = .aspectOverModal) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end Hacquard2006

/-! ## Bridge content (merged from ActualityInferencesBridge.lean) -/

/-!
# Actuality Inference Data (Cross-Linguistic)
@cite{bhatt-1999} @cite{hacquard-2006} @cite{nadathur-2023}

Cross-linguistic empirical data on actuality inferences with ability modals,
following the pattern of `Phenomena/Causation/Data.lean`.

## Key Generalization (@cite{nadathur-2023}, Chapter 1)

Across languages, ability modals with **perfective** aspect entail the
complement, while those with **imperfective** aspect do not.

| Language | Modal | PFV entails? | IMPF entails? |
|----------|-------|-------------|---------------|
| Greek | *boro* | Yes | No |
| Hindi | *saknaa* | Yes | No |
| French | *pouvoir* | Yes | No |
| English | *be able* | Yes (episodic) | No (habitual) |

-/

namespace Phenomena.Modality.ActualityInferencesBridge

open Semantics.Tense.Aspect.Core (ViewpointAspectB)

/-- A single cross-linguistic data point for actuality inferences. -/
structure ActualityDatum where
  /-- Language name -/
  language : String
  /-- The modal form in that language -/
  modalForm : String
  /-- Viewpoint aspect of the sentence -/
  aspect : ViewpointAspectB
  /-- Does the complement entailment hold? -/
  complementEntailed : Bool
  /-- Example sentence gloss -/
  gloss : String
  deriving Repr, DecidableEq

-- ════════════════════════════════════════════════════
-- Greek: boro 'can/be able'
-- ════════════════════════════════════════════════════

/-- Greek *boro* + perfective (aorist): "She was-able.PFV to swim across"
    → She swam across. -/
def greek_pfv : ActualityDatum where
  language := "Greek"
  modalForm := "boro"
  aspect := .perfective
  complementEntailed := true
  gloss := "Borese na kolimbisi apenant (She was-able.AOR to swim across)"

/-- Greek *boro* + imperfective: "She was-able.IMPF to swim across"
    ↛ She swam across. -/
def greek_impf : ActualityDatum where
  language := "Greek"
  modalForm := "boro"
  aspect := .imperfective
  complementEntailed := false
  gloss := "Boruse na kolimbisi apenant (She was-able.IMPF to swim across)"

-- ════════════════════════════════════════════════════
-- Hindi: saknaa 'can/be able'
-- ════════════════════════════════════════════════════

/-- Hindi *saknaa* + perfective: "She was-able.PFV to swim across"
    → She swam across. -/
def hindi_pfv : ActualityDatum where
  language := "Hindi"
  modalForm := "saknaa"
  aspect := .perfective
  complementEntailed := true
  gloss := "Voh pair ke tair sakii (She was-able.PFV to swim across)"

/-- Hindi *saknaa* + imperfective: "She was-able.IMPF to swim across"
    ↛ She swam across. -/
def hindi_impf : ActualityDatum where
  language := "Hindi"
  modalForm := "saknaa"
  aspect := .imperfective
  complementEntailed := false
  gloss := "Voh pair ke tair saktii thii (She was-able.IMPF to swim across)"

-- ════════════════════════════════════════════════════
-- French: pouvoir 'can/be able'
-- ════════════════════════════════════════════════════

/-- French *pouvoir* + passé composé (perfective): "She was-able.PFV to swim across"
    → She swam across. -/
def french_pfv : ActualityDatum where
  language := "French"
  modalForm := "pouvoir"
  aspect := .perfective
  complementEntailed := true
  gloss := "Elle a pu traverser à la nage (She was-able.PC to swim across)"

/-- French *pouvoir* + imparfait (imperfective): "She was-able.IMPF to swim across"
    ↛ She swam across. -/
def french_impf : ActualityDatum where
  language := "French"
  modalForm := "pouvoir"
  aspect := .imperfective
  complementEntailed := false
  gloss := "Elle pouvait traverser à la nage (She was-able.IMP to swim across)"

-- ════════════════════════════════════════════════════
-- English: be able (episodic vs habitual)
-- ════════════════════════════════════════════════════

/-- English *be able* + episodic (perfective-like): "She was able to swim across"
    → She swam across. -/
def english_pfv : ActualityDatum where
  language := "English"
  modalForm := "be able"
  aspect := .perfective
  complementEntailed := true
  gloss := "She was able to swim across (episodic reading)"

/-- English *be able* + habitual (imperfective-like): "She was able to swim across"
    ↛ She swam across on that occasion. -/
def english_impf : ActualityDatum where
  language := "English"
  modalForm := "be able"
  aspect := .imperfective
  complementEntailed := false
  gloss := "She was able to swim across (habitual/generic reading)"

-- ════════════════════════════════════════════════════
-- Dataset
-- ════════════════════════════════════════════════════

/-- All actuality inference data points. -/
def allData : List ActualityDatum :=
  [greek_pfv, greek_impf, hindi_pfv, hindi_impf,
   french_pfv, french_impf, english_pfv, english_impf]

/-- The perfective subset. -/
def perfData : List ActualityDatum :=
  allData.filter (·.aspect == .perfective)

/-- The imperfective subset. -/
def impfData : List ActualityDatum :=
  allData.filter (·.aspect == .imperfective)

-- ════════════════════════════════════════════════════
-- Verification Theorems
-- ════════════════════════════════════════════════════

/-- All 4 perfective data points have `complementEntailed = true`. -/
theorem perfective_entails :
    perfData.all (·.complementEntailed) = true := by native_decide

/-- All 4 imperfective data points have `complementEntailed = false`. -/
theorem imperfective_no_entailment :
    impfData.all (·.complementEntailed == false) = true := by native_decide

/-- **Central empirical generalization**: across all 8 data points,
    `complementEntailed` tracks `aspect ==.perfective` exactly.

    This is the empirical observation that @cite{nadathur-2023} explains
    via the causal sufficiency + aspect interaction. -/
theorem empirical_matches_theory :
    allData.all (λ d => (d.aspect == .perfective) == d.complementEntailed) = true := by
  native_decide

/-- We have data from 4 distinct languages. -/
theorem four_languages :
    (allData.map (·.language)).dedup.length = 4 := by native_decide

/-- Each language contributes exactly one perfective and one imperfective datum. -/
theorem balanced_design :
    perfData.length = 4 ∧ impfData.length = 4 := by
  constructor <;> native_decide


-- ════════════════════════════════════════════════════
-- Bridge: Data → Position × Aspect Theory
-- (@cite{hacquard-2006}, via ActualityEntailments.lean)
-- ════════════════════════════════════════════════════

open Semantics.Modality.ActualityEntailments (actualityEntailmentPredicted)
open Semantics.Modality.EventRelativity (ModalPosition)

/-- Every datum's `complementEntailed` field matches the position × aspect
prediction for root modals. All data involves root/ability modals
(below AspP), so the prediction is `actualityEntailmentPredicted.belowAsp d.aspect`.

This connects the theory-neutral empirical data (§§ above) to
@cite{hacquard-2006}'s structural explanation: root modals are below Asp,
so perfective forces actualization. -/
theorem data_matches_position_theory :
    allData.all (λ d =>
      d.complementEntailed == actualityEntailmentPredicted .belowAsp d.aspect
    ) = true := by native_decide

/-- Per-language bridge: Greek data matches position theory. -/
theorem greek_matches_theory :
    greek_pfv.complementEntailed = actualityEntailmentPredicted .belowAsp .perfective ∧
    greek_impf.complementEntailed = actualityEntailmentPredicted .belowAsp .imperfective :=
  ⟨rfl, rfl⟩

/-- Per-language bridge: Hindi data matches position theory. -/
theorem hindi_matches_theory :
    hindi_pfv.complementEntailed = actualityEntailmentPredicted .belowAsp .perfective ∧
    hindi_impf.complementEntailed = actualityEntailmentPredicted .belowAsp .imperfective :=
  ⟨rfl, rfl⟩

/-- Per-language bridge: French data matches position theory. -/
theorem french_matches_theory :
    french_pfv.complementEntailed = actualityEntailmentPredicted .belowAsp .perfective ∧
    french_impf.complementEntailed = actualityEntailmentPredicted .belowAsp .imperfective :=
  ⟨rfl, rfl⟩

/-- Per-language bridge: English data matches position theory. -/
theorem english_matches_theory :
    english_pfv.complementEntailed = actualityEntailmentPredicted .belowAsp .perfective ∧
    english_impf.complementEntailed = actualityEntailmentPredicted .belowAsp .imperfective :=
  ⟨rfl, rfl⟩

end Phenomena.Modality.ActualityInferencesBridge
