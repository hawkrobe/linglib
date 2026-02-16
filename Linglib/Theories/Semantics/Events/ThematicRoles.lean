/-
# Thematic Roles (Neo-Davidsonian)

Neo-Davidsonian thematic roles as two-place predicates relating entities
to events (Parsons 1990). This module provides:

- `ThematicRel`: the type `Entity → Ev Time → Prop`
- `ThematicFrame`: a model's assignment of role relations
- Bridge from `ThetaRole` enum (Fragment layer) to `ThematicFrame` fields
- `ThematicAxioms`: Aktionsart selection + uniqueness constraints
- Neo-Davidsonian logical forms for transitive/intransitive/ditransitive
- Davidson's key payoff: adverbial modification as predicate conjunction
- VerbEntry grounding theorems

## References

- Parsons, T. (1990). Events in the Semantics of English.
- Davidson, D. (1967). The logical form of action sentences.
- Dowty, D. (1991). Thematic proto-roles and argument selection.
- Kratzer, A. (1996). Severing the external argument from its verb.
-/

import Linglib.Theories.Semantics.Events.Basic
import Linglib.Core.Basic

namespace Semantics.Events.ThematicRoles

open Semantics.Events
open Core.Time

-- ════════════════════════════════════════════════════
-- § 1. Thematic Relations
-- ════════════════════════════════════════════════════

/-- A thematic relation: a two-place predicate relating an entity to an event.
    The core neo-Davidsonian type (Parsons 1990).
    Agent(j, e) means "j is the agent of event e". -/
abbrev ThematicRel (Entity Time : Type*) [LE Time] :=
  Entity → Ev Time → Prop

-- ════════════════════════════════════════════════════
-- § 2. ThematicFrame
-- ════════════════════════════════════════════════════

/-- A thematic frame bundles thematic relations for a given model.
    Each field provides the semantic content for one role.

    Note: `holder` is a Theory-level role (Parsons 1990) distinct from
    `agent` — it selects for states, not actions. The Fragment-layer
    `ThetaRole` enum does not include `holder` since `VendlerClass`
    already encodes dynamicity. -/
structure ThematicFrame (Entity Time : Type*) [LE Time] where
  /-- Agent: volitional causer -/
  agent : ThematicRel Entity Time
  /-- Patient: affected entity -/
  patient : ThematicRel Entity Time
  /-- Theme: entity in a state/location -/
  theme : ThematicRel Entity Time
  /-- Experiencer: perceiver/cognizer -/
  experiencer : ThematicRel Entity Time
  /-- Goal: recipient/target -/
  goal : ThematicRel Entity Time
  /-- Source: origin -/
  source : ThematicRel Entity Time
  /-- Instrument: means -/
  instrument : ThematicRel Entity Time
  /-- Stimulus: cause of experience -/
  stimulus : ThematicRel Entity Time
  /-- Holder: entity in a state (Parsons 1990).
      Distinct from Agent: selects for states, not actions. -/
  holder : ThematicRel Entity Time

-- ════════════════════════════════════════════════════
-- § 3. ThetaRole Bridge (Fragment → Theory)
-- ════════════════════════════════════════════════════

/-- Map the Fragment-layer ThetaRole enum to the corresponding
    ThematicFrame field. This bridges lexical annotations to
    semantic content. -/
def ThetaRole.toRel {Entity Time : Type*} [LE Time]
    (θ : ThetaRole) (frame : ThematicFrame Entity Time) : ThematicRel Entity Time :=
  match θ with
  | .agent       => frame.agent
  | .patient     => frame.patient
  | .theme       => frame.theme
  | .experiencer => frame.experiencer
  | .goal        => frame.goal
  | .source      => frame.source
  | .instrument  => frame.instrument
  | .stimulus    => frame.stimulus

-- ════════════════════════════════════════════════════
-- § 4. Per-Role Retrieval Verification
-- ════════════════════════════════════════════════════

variable {Entity Time : Type*} [LE Time] (frame : ThematicFrame Entity Time)

theorem agent_toRel : ThetaRole.toRel .agent frame = frame.agent := rfl
theorem patient_toRel : ThetaRole.toRel .patient frame = frame.patient := rfl
theorem theme_toRel : ThetaRole.toRel .theme frame = frame.theme := rfl
theorem experiencer_toRel : ThetaRole.toRel .experiencer frame = frame.experiencer := rfl
theorem goal_toRel : ThetaRole.toRel .goal frame = frame.goal := rfl
theorem source_toRel : ThetaRole.toRel .source frame = frame.source := rfl
theorem instrument_toRel : ThetaRole.toRel .instrument frame = frame.instrument := rfl
theorem stimulus_toRel : ThetaRole.toRel .stimulus frame = frame.stimulus := rfl

-- ════════════════════════════════════════════════════
-- § 5. Thematic Axioms (Aktionsart selection + uniqueness)
-- ════════════════════════════════════════════════════

/-- Semantic constraints on thematic roles (Parsons 1990, Kratzer 1996).

    - `agent_selects_action`: agents only participate in actions
    - `holder_selects_state`: holders only participate in states
    - `agent_unique`: each event has at most one agent
    - `patient_unique`: each event has at most one patient -/
class ThematicAxioms (Entity Time : Type*) [LE Time]
    (frame : ThematicFrame Entity Time) where
  /-- Agents only participate in actions (dynamic events). -/
  agent_selects_action : ∀ (x : Entity) (e : Ev Time),
    frame.agent x e → e.sort = .action
  /-- Holders only participate in states. -/
  holder_selects_state : ∀ (x : Entity) (e : Ev Time),
    frame.holder x e → e.sort = .state
  /-- Each event has at most one agent. -/
  agent_unique : ∀ (x y : Entity) (e : Ev Time),
    frame.agent x e → frame.agent y e → x = y
  /-- Each event has at most one patient. -/
  patient_unique : ∀ (x y : Entity) (e : Ev Time),
    frame.patient x e → frame.patient y e → x = y

-- ════════════════════════════════════════════════════
-- § 6. Derived Properties
-- ════════════════════════════════════════════════════

/-- Agent and holder cannot both hold of the same entity and event,
    since agents require actions and holders require states. -/
theorem agent_holder_disjoint {Entity Time : Type*} [LE Time]
    {frame : ThematicFrame Entity Time} [ax : ThematicAxioms Entity Time frame]
    (x : Entity) (e : Ev Time) :
    frame.agent x e → frame.holder x e → False := by
  intro hAgent hHolder
  have hAction := ax.agent_selects_action x e hAgent
  have hState := ax.holder_selects_state x e hHolder
  rw [hAction] at hState
  exact absurd hState (by decide)

-- ════════════════════════════════════════════════════
-- § 7. Neo-Davidsonian Logical Forms
-- ════════════════════════════════════════════════════

/-- Neo-Davidsonian logical form for a transitive sentence:
    "x V-ed y" ↦ ∃e. V(e) ∧ Agent(x, e) ∧ Patient(y, e)

    The key Parsons (1990) insight: thematic roles are separate
    conjuncts, not part of the verb's argument structure. -/
def transitiveLogicalForm {Entity Time : Type*} [LE Time]
    (V : EvPred Time) (frame : ThematicFrame Entity Time)
    (subj obj : Entity) : Prop :=
  ∃ e : Ev Time, V e ∧ frame.agent subj e ∧ frame.patient obj e

/-- Neo-Davidsonian logical form for an intransitive sentence:
    "x V-ed" ↦ ∃e. V(e) ∧ Agent(x, e) -/
def intransitiveLogicalForm {Entity Time : Type*} [LE Time]
    (V : EvPred Time) (frame : ThematicFrame Entity Time)
    (subj : Entity) : Prop :=
  ∃ e : Ev Time, V e ∧ frame.agent subj e

/-- Neo-Davidsonian logical form for a ditransitive sentence:
    "x V-ed y z" ↦ ∃e. V(e) ∧ Agent(x, e) ∧ Theme(y, e) ∧ Goal(z, e) -/
def ditransitiveLogicalForm {Entity Time : Type*} [LE Time]
    (V : EvPred Time) (frame : ThematicFrame Entity Time)
    (subj directObj indirectObj : Entity) : Prop :=
  ∃ e : Ev Time, V e ∧ frame.agent subj e ∧
    frame.theme directObj e ∧ frame.goal indirectObj e

-- ════════════════════════════════════════════════════
-- § 8. Adverbial Modification (Davidson's key payoff)
-- ════════════════════════════════════════════════════

/-- An event modifier: a predicate on events (e.g., "quickly", "in the park"). -/
abbrev EventModifier (Time : Type*) [LE Time] := EvPred Time

/-- Apply a modifier to an event predicate via conjunction.
    This is Davidson's (1967) key insight: adverbial modification is
    simply conjunction of event predicates.
    "John kicked the ball quickly" = ∃e. kick(e) ∧ Agent(j,e) ∧ Patient(b,e) ∧ quickly(e) -/
def modify {Time : Type*} [LE Time]
    (P : EvPred Time) (M : EventModifier Time) : EvPred Time :=
  λ e => P e ∧ M e

/-- Modification is commutative: "quickly and loudly" = "loudly and quickly". -/
theorem modify_comm {Time : Type*} [LE Time]
    (P : EvPred Time) (M₁ M₂ : EventModifier Time) :
    modify (modify P M₁) M₂ = modify (modify P M₂) M₁ := by
  funext e
  simp only [modify]
  exact propext ⟨λ ⟨⟨hp, hm1⟩, hm2⟩ => ⟨⟨hp, hm2⟩, hm1⟩,
                λ ⟨⟨hp, hm2⟩, hm1⟩ => ⟨⟨hp, hm1⟩, hm2⟩⟩

/-- Modification is associative. -/
theorem modify_assoc {Time : Type*} [LE Time]
    (P : EvPred Time) (M₁ M₂ : EventModifier Time) :
    modify (modify P M₁) M₂ = modify P (λ e => M₁ e ∧ M₂ e) := by
  funext e
  simp only [modify]
  exact propext ⟨λ ⟨⟨hp, hm1⟩, hm2⟩ => ⟨hp, hm1, hm2⟩,
                λ ⟨hp, hm1, hm2⟩ => ⟨⟨hp, hm1⟩, hm2⟩⟩

end Semantics.Events.ThematicRoles
