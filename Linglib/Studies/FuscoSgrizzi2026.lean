import Linglib.Semantics.Modality.Kratzer.Flavor
import Linglib.Semantics.Attitudes.RationalAttitude
import Linglib.Semantics.Events.Basic

/-!
# Inertial modality for Italian non-finite belief/action readings
[fusco-sgrizzi-2026] [dowty-1979] [kratzer-2012]

[fusco-sgrizzi-2026] analyse the belief/action ambiguity of Italian
non-finite complements (*convincere a* + INF, *promettere di* + INF) via
inertial modality in the [dowty-1979] sense, recast as a Kratzer
circumstantial-base + inertial-ordering pair.

## Main declarations

* `InertialParams`: bundles a circumstantial modal base with an inertial
  ordering source.
* `inertialNecessity`, `inertialPossibility`: `□`/`◇` over the
  best-inertial-continuation worlds.
* `inertial_duality`: modal duality, delegated to `Kratzer.duality`.
* `empty_inertia_is_simple`: with an empty ordering source, inertial
  necessity collapses to circumstantial `simpleNecessity`.
* `CausativeAttitude`: the single denotation of *convincere*-type
  verbs (their ex. 24), with `beliefReading`/`intentionReading` the
  two complement-size construals and the reading diagnostics.

## Implementation notes

[dowty-1979]: w' is an inertia world of w iff w' matches w up to the
reference time and the course of events in w continues without interruption.
In Kratzer's framework this is a circumstantial modal base paired with an
ordering source whose propositions describe normal continuation.
-/

namespace FuscoSgrizzi2026

open Modality Modality.Kratzer

variable {W : Type*}

/-- Inertial modal parameters: circumstantial base + inertial ordering. -/
structure InertialParams (W : Type*) where
  /-- Circumstantial modal base: facts holding at the evaluation world. -/
  circumstances : ModalBase W
  /-- Inertial ordering: propositions describing normal continuation. -/
  inertia : OrderingSource W

/-- Extract Kratzer parameters from inertial parameters. -/
def InertialParams.toKratzer (p : InertialParams W) : KratzerParams W where
  base := p.circumstances
  ordering := p.inertia

/-- Inertial necessity: `p` holds in all best (most inertial) circumstantially
    accessible worlds. For intention readings: in all worlds where the
    experiencer's current course of action continues uninterrupted, the
    intended event obtains. -/
def inertialNecessity (p : InertialParams W) (prop : W → Prop) (w : W) : Prop :=
  necessity p.circumstances p.inertia prop w

/-- Inertial possibility: `p` holds in some best circumstantially accessible
    world. -/
def inertialPossibility (p : InertialParams W) (prop : W → Prop) (w : W) : Prop :=
  possibility p.circumstances p.inertia prop w

/-- Inertial modality satisfies modal duality: `□p ↔ ¬◇¬p`. -/
theorem inertial_duality (p : InertialParams W) (prop : W → Prop) (w : W) :
    inertialNecessity p prop w ↔ ¬ inertialPossibility p (fun w' => ¬ prop w') w :=
  Kratzer.duality p.circumstances p.inertia prop w

/-- With empty inertial ordering, inertial modality reduces to simple
    circumstantial necessity (no preference among accessible worlds). -/
theorem empty_inertia_is_simple (circ : ModalBase W) (prop : W → Prop) (w : W) :
    inertialNecessity ⟨circ, emptyBackground⟩ prop w ↔
    simpleNecessity circ prop w := by
  simp only [inertialNecessity, necessity, simpleNecessity,
             ModalLogic.box]
  constructor
  · intro h j hj
    exact h j ((kratzerBestR_empty circ w j).mpr hj)
  · intro h j hj
    exact h j ((kratzerBestR_empty circ w j).mp hj)

/-- Inertial modality maps to the circumstantial flavor tag. Both inertial
    and teleological modality concern what happens given the facts — they
    differ only in ordering source, not modal base. -/
def InertialParams.flavorTag : ModalFlavor := .circumstantial

/-! ## The single denotation of *convincere* (ex. 24)

⟦convincere⟧ = λP.λx.λy.λe. ∃e'. Convince(e) ∧ Agent(e,y) ∧ Patient(e,x)
∧ CAUSE(e,e') ∧ RATIONAL-ATTITUDE(e') ∧ Experiencer(x,e') ∧ P(e').
The parameter P is supplied by the complement: a *di*-infinitive (CP)
is existentially closed, yielding the belief reading; an
*a*-infinitive (aP) leaves the event variable open, yielding the
intention reading. The belief/intention split is compositional — one
verb, two complement sizes. -/

/-- A causative attitude verb: the agent causes the experiencer to
    enter a rational attitude state whose content is the complement
    predicate. -/
structure CausativeAttitude (E Time : Type*) [LinearOrder Time] where
  /-- The verb's descriptive predicate (Convince). -/
  verbPred : Event Time → Prop
  /-- The agent of the matrix event. -/
  agent : E
  /-- The patient of the matrix event and experiencer of the attitude. -/
  experiencer : E
  /-- Agent thematic role. -/
  isAgent : Event Time → E → Prop
  /-- Patient thematic role. -/
  isPatient : Event Time → E → Prop
  /-- Experiencer thematic role, on the attitude event. -/
  isExperiencer : Event Time → E → Prop
  /-- The matrix event causally brings about the attitude state. -/
  cause : Event Time → Event Time → Prop

variable {E Time : Type*} [LinearOrder Time]

/-- The verb applied to a complement predicate `P`: some matrix event
    causes a stative rational-attitude event satisfying `P`. -/
def CausativeAttitude.denote (v : CausativeAttitude E Time)
    (P : Event Time → Prop) : Prop :=
  ∃ e e' : Event Time,
    v.verbPred e ∧ v.isAgent e v.agent ∧ v.isPatient e v.experiencer ∧
    v.cause e e' ∧ e'.sort = .stative ∧
    v.isExperiencer e' v.experiencer ∧ P e'

/-- Belief reading: the CP complement is existentially closed into a
    proposition, evaluated against doxastic content. -/
def CausativeAttitude.beliefReading (v : CausativeAttitude E Time)
    (embeddedVP : Event Time → Prop) : Prop :=
  v.denote (fun _ => ∃ e : Event Time, embeddedVP e)

/-- Intention reading: the sub-CP complement is applied directly as an
    event predicate, evaluated against inertial continuation. -/
def CausativeAttitude.intentionReading (v : CausativeAttitude E Time)
    (embeddedVP : Event Time → Prop) : Prop :=
  v.denote embeddedVP

/-- The paper's central claim (ex. 24): both readings are the one
    `denote` applied to different complement predicates — the
    belief/intention split is compositional, not lexical. -/
theorem CausativeAttitude.readings_from_single_denote
    (v : CausativeAttitude E Time) (VP : Event Time → Prop) :
    v.beliefReading VP = v.denote (fun _ => ∃ e, VP e) ∧
    v.intentionReading VP = v.denote VP :=
  ⟨rfl, rfl⟩

/-! ## Reading diagnostics

The paper's empirical differentiators of the two construals: belief
readings are truth-assessable and host modal auxiliaries; intention
readings are obligatorily future-oriented and object-control. -/

open RationalAttitude (Reading)

/-- "It's true/false" can felicitously evaluate a belief but not an
    intention. -/
def truthAssessable : Reading → Bool
  | .belief => true
  | .intention => false

/-- CP complements host modal auxiliary heads; sub-CP complements
    lack the structural space. -/
def allowsModalAux : Reading → Bool
  | .belief => true
  | .intention => false

/-- The intended event is projected into inertia worlds, so intention
    readings are obligatorily future-oriented. -/
def forcedFutureOrientation : Reading → Bool
  | .belief => false
  | .intention => true

/-- The experiencer must be the agent of the intended event, so
    intention readings are obligatorily object-control. -/
def objectControlOnly : Reading → Bool
  | .belief => false
  | .intention => true

end FuscoSgrizzi2026
