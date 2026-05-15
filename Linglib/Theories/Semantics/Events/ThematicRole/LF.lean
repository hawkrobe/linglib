import Linglib.Theories.Semantics.Events.ThematicRole.Defs

/-!
# Thematic Roles — Davidsonian logical forms + axioms

API on top of `ThematicRole/Defs.lean`: thematic axioms (Aktionsart
selection + uniqueness), neo-Davidsonian logical forms, adverbial
modification (Davidson's key payoff).

## Main definitions

* per-role `*_toRel` retrieval theorems (drift sentries)
* `ThematicAxioms` — Aktionsart selection + uniqueness constraints
* `agent_holder_disjoint` — derived from the axioms
* `transitiveLogicalForm` / `intransitiveLogicalForm` /
  `ditransitiveLogicalForm` — neo-Davidsonian LFs
* `EventModifier` + `modify` + `modify_comm` + `modify_assoc` —
  adverbial modification as predicate conjunction (@cite{davidson-1967})
* `stativeLogicalForm` / `modifiedStativeLogicalForm` /
  `modified_stative_is_pm` — stative LFs with `holder`
  (@cite{wellwood-2015} §3.2)

## References

* @cite{davidson-1967} (adverbial modification = predicate conjunction)
* @cite{parsons-1990} (thematic roles as separate conjuncts)
* @cite{wellwood-2015} §3.2 (gradable adjectives over states)
-/

namespace Semantics.Events.ThematicRoles

open Semantics.Events
open Core.Time

/-! ### Per-role retrieval verification -/

variable {Entity Time : Type*} [LinearOrder Time] (frame : ThematicFrame Entity Time)

theorem agent_toRel : ThetaRole.toRel .agent frame = frame.agent := rfl
theorem patient_toRel : ThetaRole.toRel .patient frame = frame.patient := rfl
theorem theme_toRel : ThetaRole.toRel .theme frame = frame.theme := rfl
theorem experiencer_toRel : ThetaRole.toRel .experiencer frame = frame.experiencer := rfl
theorem goal_toRel : ThetaRole.toRel .goal frame = frame.goal := rfl
theorem source_toRel : ThetaRole.toRel .source frame = frame.source := rfl
theorem instrument_toRel : ThetaRole.toRel .instrument frame = frame.instrument := rfl
theorem stimulus_toRel : ThetaRole.toRel .stimulus frame = frame.stimulus := rfl

/-! ### Thematic axioms (Aktionsart selection + uniqueness) -/

/-- Semantic constraints on thematic roles.

    - `agent_selects_action`: agents only participate in actions
    - `holder_selects_state`: holders only participate in states
    - `agent_unique`: each event has at most one agent
    - `patient_unique`: each event has at most one patient -/
class ThematicAxioms (Entity Time : Type*) [LinearOrder Time]
    (frame : ThematicFrame Entity Time) where
  /-- Agents only participate in actions (dynamic events). -/
  agent_selects_action : ∀ (x : Entity) (e : Event Time),
    frame.agent x e → e.sort = .action
  /-- Holders only participate in states. -/
  holder_selects_state : ∀ (x : Entity) (e : Event Time),
    frame.holder x e → e.sort = .state
  /-- Each event has at most one agent. -/
  agent_unique : ∀ (x y : Entity) (e : Event Time),
    frame.agent x e → frame.agent y e → x = y
  /-- Each event has at most one patient. -/
  patient_unique : ∀ (x y : Entity) (e : Event Time),
    frame.patient x e → frame.patient y e → x = y

/-- Agent and holder cannot both hold of the same entity and event,
    since agents require actions and holders require states. -/
theorem agent_holder_disjoint {Entity Time : Type*} [LinearOrder Time]
    {frame : ThematicFrame Entity Time} [ax : ThematicAxioms Entity Time frame]
    (x : Entity) (e : Event Time) :
    frame.agent x e → frame.holder x e → False := by
  intro hAgent hHolder
  have hAction := ax.agent_selects_action x e hAgent
  have hState := ax.holder_selects_state x e hHolder
  rw [hAction] at hState
  exact absurd hState (by decide)

/-! ### Neo-Davidsonian logical forms -/

/-- "x V-ed y" ↦ ∃e. V(e) ∧ Agent(x, e) ∧ Patient(y, e).
    @cite{parsons-1990}: thematic roles are separate conjuncts, not
    part of the verb's argument structure. -/
def transitiveLogicalForm {Entity Time : Type*} [LinearOrder Time]
    (V : EvPred Time) (frame : ThematicFrame Entity Time)
    (subj obj : Entity) : Prop :=
  ∃ e : Event Time, V e ∧ frame.agent subj e ∧ frame.patient obj e

/-- "x V-ed" ↦ ∃e. V(e) ∧ Agent(x, e) -/
def intransitiveLogicalForm {Entity Time : Type*} [LinearOrder Time]
    (V : EvPred Time) (frame : ThematicFrame Entity Time)
    (subj : Entity) : Prop :=
  ∃ e : Event Time, V e ∧ frame.agent subj e

/-- "x V-ed y z" ↦ ∃e. V(e) ∧ Agent(x, e) ∧ Theme(y, e) ∧ Goal(z, e) -/
def ditransitiveLogicalForm {Entity Time : Type*} [LinearOrder Time]
    (V : EvPred Time) (frame : ThematicFrame Entity Time)
    (subj directObj indirectObj : Entity) : Prop :=
  ∃ e : Event Time, V e ∧ frame.agent subj e ∧
    frame.theme directObj e ∧ frame.goal indirectObj e

/-! ### Adverbial modification (Davidson's key payoff) -/

/-- An event modifier: a predicate on events (e.g., "quickly", "in the park"). -/
abbrev EventModifier (Time : Type*) [LinearOrder Time] := EvPred Time

/-- Apply a modifier to an event predicate via conjunction.
    @cite{davidson-1967}: adverbial modification is conjunction of event
    predicates. "John kicked the ball quickly" = ∃e. kick(e) ∧
    Agent(j,e) ∧ Patient(b,e) ∧ quickly(e). -/
def modify {Time : Type*} [LinearOrder Time]
    (P : EvPred Time) (M : EventModifier Time) : EvPred Time :=
  λ e => P e ∧ M e

/-- Modification is commutative: "quickly and loudly" = "loudly and quickly". -/
theorem modify_comm {Time : Type*} [LinearOrder Time]
    (P : EvPred Time) (M₁ M₂ : EventModifier Time) :
    modify (modify P M₁) M₂ = modify (modify P M₂) M₁ := by
  funext e
  simp only [modify]
  exact propext ⟨λ ⟨⟨hp, hm1⟩, hm2⟩ => ⟨⟨hp, hm2⟩, hm1⟩,
                λ ⟨⟨hp, hm2⟩, hm1⟩ => ⟨⟨hp, hm1⟩, hm2⟩⟩

/-- Modification is associative. -/
theorem modify_assoc {Time : Type*} [LinearOrder Time]
    (P : EvPred Time) (M₁ M₂ : EventModifier Time) :
    modify (modify P M₁) M₂ = modify P (λ e => M₁ e ∧ M₂ e) := by
  funext e
  simp only [modify]
  exact propext ⟨λ ⟨⟨hp, hm1⟩, hm2⟩ => ⟨hp, hm1, hm2⟩,
                λ ⟨hp, hm1, hm2⟩ => ⟨⟨hp, hm1⟩, hm2⟩⟩

/-! ### Stative logical forms (@cite{wellwood-2015} §3.2) -/

/-- "x is happy" ↦ ∃s. P(s) ∧ Holder(x, s). Parallel to
    `intransitiveLogicalForm` but using `holder` instead of `agent`,
    reflecting that states select for holders. -/
def stativeLogicalForm {Entity Time : Type*} [LinearOrder Time]
    (P : EvPred Time) (frame : ThematicFrame Entity Time)
    (x : Entity) : Prop :=
  ∃ s : Event Time, P s ∧ frame.holder x s

/-- "x is happy in the morning" ↦ ∃s. P(s) ∧ Holder(x, s) ∧ M(s).
    State modification = event modification applied to states. -/
def modifiedStativeLogicalForm {Entity Time : Type*} [LinearOrder Time]
    (P : EvPred Time) (frame : ThematicFrame Entity Time)
    (x : Entity) (M : EventModifier Time) : Prop :=
  ∃ s : Event Time, P s ∧ frame.holder x s ∧ M s

/-- Modified stative = stative of modified predicate (Predicate Modification):
    state modification is an instance of Davidson's conjunction-based
    event modification. -/
theorem modified_stative_is_pm {Entity Time : Type*} [LinearOrder Time]
    (P : EvPred Time) (frame : ThematicFrame Entity Time)
    (x : Entity) (M : EventModifier Time) :
    modifiedStativeLogicalForm P frame x M ↔
      stativeLogicalForm (modify P M) frame x := by
  simp only [modifiedStativeLogicalForm, stativeLogicalForm, modify]
  exact ⟨fun ⟨s, hp, hh, hm⟩ => ⟨s, ⟨hp, hm⟩, hh⟩,
         fun ⟨s, ⟨hp, hm⟩, hh⟩ => ⟨s, hp, hh, hm⟩⟩

end Semantics.Events.ThematicRoles
