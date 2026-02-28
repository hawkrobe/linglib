import Linglib.Theories.Semantics.Causation.PsychCausation
import Linglib.Theories.Semantics.Causation.PsychCausalLink

/-!
# Psych Verb Denotation via Cognitive Situation Models

@cite{kim-2024}

A psych verb denotes a relation evaluated over a **cognitive situation** — a
model of the experiencer's mind decomposed into BToM layers (Baker et al. 2017).
The `CausalPathway` (perceptual vs representational) determines which layer of
the cognitive architecture the stimulus connects through:

- **Perceptual** (frighten-class): stimulus evaluated via perception
  (extensional, world-driven)
- **Representational** (concern-class): stimulus evaluated via belief
  (intensional, mind-internal)

From this single denotation, key properties are **derived**, not stipulated:

| Property | Perceptual | Representational |
|----------|-----------|------------------|
| Opacity | extensional (co-referential stimuli agree) | can be intensional (Cicero ≠ Tully) |
| Temporal | cause precedes effect (eventiveLink) | cause overlaps effect (maintenanceLink) |
| Aspect | eventive (BECOME + state) | stative (state only) |
| UPH | same type signature | same type signature |

The UPH (Uniform Projection Hypothesis) is a type-level guarantee: both
pathways take `(stimulus, experiencer-state)` in the same positions. No theorem
needed — it's built into the type signature of `psychVerbSem`.

## Connection to BToM (Baker et al. 2017)

`ExperiencerState` is a lightweight projection of the BToM cognitive
architecture. The formal correspondence:

- `perceives` = BToM's `perceptModel` layer (World → Percept → F)
- `represents` = BToM's `beliefModel` layer (Percept → Belief → F)
- Extensionality follows from perception being world-driven
- Intensionality follows from belief being representation-driven

A formal bridge (`ExperiencerState.fromBToM`) is deferred to avoid Mathlib
imports required by `BToM.lean`.

## References

- Baker, C., Jara-Ettinger, J., Saxe, R. & Tenenbaum, J. (2017). Rational
  quantitative attribution of beliefs, desires and percepts in human
  mentalizing. Nature Human Behaviour 1, 0064.
- Kim, Y. (2024). On the argument structure of object experiencer verbs.
- Pesetsky, D. (1995). Zero Syntax.
- Landau, I. (2010). The Locative Syntax of Experiencers.
-/

namespace Semantics.Causation.PsychVerbSem

open Semantics.Causation.PsychCausation (CausalSource)
open Semantics.Causation.PsychCausalLink (PsychCausalLink eventiveLink maintenanceLink)

-- ════════════════════════════════════════════════════
-- § 1. ExperiencerState — Cognitive Situation Model
-- ════════════════════════════════════════════════════

/-- The evaluation domain for psych verb denotations. Models the experiencer's
    cognitive state decomposed into BToM layers (Baker et al. 2017).

    Each field corresponds to a level of the perception → belief → mental state
    causal chain. A psych verb's denotation evaluates the stimulus at one of
    these levels (determined by `CausalPathway`), then checks whether the
    appropriate causal connection to the target mental state holds. -/
structure ExperiencerState (Stimulus MState : Type*) where
  /-- Perceptual layer: world-driven, extensional.
      Maps to BToM's `perceptModel : World → Percept → F`. -/
  perceives : Stimulus → Bool
  /-- Belief layer: mind-internal, potentially intensional.
      Maps to BToM's `beliefModel : Percept → Belief → F`. -/
  represents : Stimulus → Bool
  /-- Mental state layer: what psychological states are active. -/
  inMentalState : MState → Bool
  /-- Perceptual causation: perceiving s triggers mental state m.
      This is the percept → state link in the BToM causal chain. -/
  perceptCauses : Stimulus → MState → Bool
  /-- Representational maintenance: representing s maintains mental state m.
      This is Kim's (2024) maintenance relation at the belief layer. -/
  beliefMaintains : Stimulus → MState → Bool

-- ════════════════════════════════════════════════════
-- § 2. CausalPathway
-- ════════════════════════════════════════════════════

/-- Which layer of the cognitive architecture the stimulus connects through.

    - `.perceptual`: World → Percept → MentalState (external causation).
      The stimulus is perceived in the world and that perception triggers
      a mental state change. Extensional — determined by the actual world.
    - `.representational`: Belief → MentalState (maintenance causation).
      The stimulus is mentally represented and that representation maintains
      a mental state. Potentially intensional — determined by the experiencer's
      belief state, not the world directly. -/
inductive CausalPathway where
  | perceptual
  | representational
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 3. The Denotation
-- ════════════════════════════════════════════════════

/-- The core psych verb denotation.

    Given a causal pathway, a target mental state (the verb's "root"), a
    stimulus, and an experiencer's cognitive state, returns whether the
    psych verb relation holds.

    Both pathways require:
    1. The experiencer is in the target mental state
    2. The stimulus is connected to that mental state through the appropriate
       cognitive layer

    The UPH is a type-level guarantee: both pathways take
    `(stimulus, experiencer-state)` in the same argument positions. -/
def psychVerbSem {Stimulus MState : Type*}
    (pathway : CausalPathway) (root : MState)
    (stimulus : Stimulus) (es : ExperiencerState Stimulus MState) : Bool :=
  es.inMentalState root &&
  match pathway with
  | .perceptual => es.perceives stimulus && es.perceptCauses stimulus root
  | .representational => es.represents stimulus && es.beliefMaintains stimulus root

-- ════════════════════════════════════════════════════
-- § 4. Coreference and Extensionality
-- ════════════════════════════════════════════════════

/-- Perceptual extensionality: co-referential stimuli have the same perceptual
    status and causal effects. Guaranteed by the BToM perception layer —
    the actual world determines what is perceived, so co-referential expressions
    (which pick out the same worldly entity) must agree. -/
def ExperiencerState.perceptuallyExtensional
    {Stimulus MState : Type*}
    (es : ExperiencerState Stimulus MState)
    (coref : Stimulus → Stimulus → Bool) : Prop :=
  ∀ a b, coref a b = true →
    es.perceives a = es.perceives b ∧
    ∀ m, es.perceptCauses a m = es.perceptCauses b m

/-- Representational intensionality: co-referential stimuli CAN have
    different belief status. The experiencer may represent Cicero without
    representing Tully, even though they are the same individual, because
    belief is representation-driven, not world-driven. -/
def ExperiencerState.representationallyIntensional
    {Stimulus MState : Type*}
    (es : ExperiencerState Stimulus MState)
    (coref : Stimulus → Stimulus → Bool) : Prop :=
  ∃ a b, coref a b = true ∧ es.represents a ≠ es.represents b

-- ════════════════════════════════════════════════════
-- § 5. Opacity Derivation
-- ════════════════════════════════════════════════════

/-- **General extensionality theorem**: the perceptual pathway is invariant
    under coreference. If stimuli a and b are co-referential, and the
    experiencer state is perceptually extensional with respect to that
    coreference relation, then the psych verb denotation agrees on a and b.

    This derives opacity from the cognitive architecture: perceptual verbs
    (frighten-class) are extensional because perception is world-driven. -/
theorem perceptual_extensional {Stimulus MState : Type*}
    (root : MState) (a b : Stimulus)
    (coref : Stimulus → Stimulus → Bool)
    (es : ExperiencerState Stimulus MState)
    (hExt : es.perceptuallyExtensional coref)
    (hab : coref a b = true) :
    psychVerbSem .perceptual root a es = psychVerbSem .perceptual root b es := by
  unfold psychVerbSem
  obtain ⟨hPerc, hCause⟩ := hExt a b hab
  rw [hPerc, hCause root]

-- ─────────────────────────────────────────────────────
-- § 5a. Concrete Cicero/Tully Example
-- ─────────────────────────────────────────────────────

/-- Stimulus type for the Cicero/Tully opacity example.
    Cicero and Tully are co-referential (same individual), but
    an experiencer may have different cognitive access to each. -/
inductive CiceroStimulus where
  | cicero
  | tully
  deriving DecidableEq, BEq, Repr

/-- Mental states for the opacity example. -/
inductive ConcernState where
  | concerned
  deriving DecidableEq, BEq, Repr

/-- A cognitive state where:
    - Both Cicero and Tully are perceived (same worldly individual)
    - Only Cicero is mentally represented (experiencer knows "Cicero"
      but doesn't connect "Tully" to the same mental file)
    - Perception of either triggers concern
    - Only the Cicero-representation maintains concern -/
def ciceroTullyState : ExperiencerState CiceroStimulus ConcernState where
  perceives := fun _ => true   -- both perceived (same worldly entity)
  represents := fun
    | .cicero => true          -- represented as "Cicero"
    | .tully => false          -- "Tully" not in belief state
  inMentalState := fun _ => true  -- experiencer is concerned
  perceptCauses := fun _ _ => true  -- perception triggers concern
  beliefMaintains := fun
    | .cicero, _ => true       -- Cicero-representation maintains concern
    | .tully, _ => false       -- no Tully-representation to maintain

/-- Coreference relation: Cicero and Tully refer to the same individual. -/
def ciceroCoref : CiceroStimulus → CiceroStimulus → Bool
  | .cicero, .tully => true
  | .tully, .cicero => true
  | .cicero, .cicero => true
  | .tully, .tully => true

-- Perceptual pathway: BOTH Cicero and Tully frighten the experiencer.
-- Co-referential stimuli agree — extensional.

theorem cicero_frightens :
    psychVerbSem .perceptual .concerned .cicero ciceroTullyState = true := rfl

theorem tully_frightens :
    psychVerbSem .perceptual .concerned .tully ciceroTullyState = true := rfl

-- Representational pathway: Cicero concerns the experiencer, but Tully
-- does NOT — even though they are the same individual. Intensional.

theorem cicero_concerns :
    psychVerbSem .representational .concerned .cicero ciceroTullyState = true := rfl

theorem tully_not_concerns :
    psychVerbSem .representational .concerned .tully ciceroTullyState = false := rfl

/-- The representational pathway CAN distinguish co-referential stimuli.
    Witnessed by Cicero/Tully: same individual, different denotation. -/
theorem representational_can_be_intensional :
    ∃ (es : ExperiencerState CiceroStimulus ConcernState)
      (coref : CiceroStimulus → CiceroStimulus → Bool)
      (root : ConcernState) (a b : CiceroStimulus),
      coref a b = true ∧
      psychVerbSem .representational root a es ≠
      psychVerbSem .representational root b es :=
  ⟨ciceroTullyState, ciceroCoref, .concerned, .cicero, .tully,
   rfl, by decide⟩

-- ════════════════════════════════════════════════════
-- § 6. CausalSource ↔ CausalPathway Isomorphism
-- ════════════════════════════════════════════════════

/-- Map CausalPathway to CausalSource (Kim 2024).
    Perceptual = external (world-driven), representational = internal (mind-driven). -/
def CausalPathway.toCausalSource : CausalPathway → CausalSource
  | .perceptual => .external
  | .representational => .internal

/-- Map CausalSource to CausalPathway.
    External = perceptual, internal = representational. -/
def CausalSource.toPathway : CausalSource → CausalPathway
  | .external => .perceptual
  | .internal => .representational

theorem pathway_source_roundtrip (p : CausalPathway) :
    CausalSource.toPathway p.toCausalSource = p := by cases p <;> rfl

theorem source_pathway_roundtrip (s : CausalSource) :
    (CausalSource.toPathway s).toCausalSource = s := by cases s <;> rfl

-- ════════════════════════════════════════════════════
-- § 7. Temporal Connection via PsychCausalLink
-- ════════════════════════════════════════════════════

/-- Map CausalPathway to PsychCausalLink for temporal predictions.

    - Perceptual → eventiveLink (cause precedes effect, involves BECOME)
    - Representational → maintenanceLink (cause overlaps effect, no BECOME)

    This bridges the cognitive architecture (which layer processes the
    stimulus) to the temporal behavior (when the mental state arises). -/
def CausalPathway.toLink (Time : Type*) [LinearOrder Time] :
    CausalPathway → PsychCausalLink Time
  | .perceptual => eventiveLink Time
  | .representational => maintenanceLink Time

/-- Perceptual pathway yields eventive temporal profile:
    cause precedes effect and involves a transition (BECOME). -/
theorem perceptual_is_eventive (Time : Type*) [LinearOrder Time] :
    (CausalPathway.perceptual.toLink Time).involvesTransition = true := rfl

/-- Representational pathway yields stative temporal profile:
    cause overlaps effect with no transition. -/
theorem representational_is_stative (Time : Type*) [LinearOrder Time] :
    (CausalPathway.representational.toLink Time).involvesTransition = false := rfl

/-- The pathway → link mapping agrees with CausalSource → link (Kim 2024).
    This ensures the cognitive architecture (CausalPathway) and the
    event-structural classification (CausalSource) make the same
    temporal predictions. -/
theorem pathway_link_agrees_with_source (Time : Type*) [LinearOrder Time]
    (p : CausalPathway) :
    p.toLink Time = Semantics.Causation.PsychCausalLink.CausalSource.toLink Time p.toCausalSource := by
  cases p <;> rfl

end Semantics.Causation.PsychVerbSem
