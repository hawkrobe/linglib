import Linglib.Semantics.ArgumentStructure.Thematic.Defs
import Linglib.Semantics.Modification.Basic

/-!
# Thematic Roles — Davidsonian logical forms + axioms

API on top of `Thematic/Defs.lean`: thematic axioms
(Aktionsart selection + uniqueness), neo-Davidsonian stative logical
forms, and adverbial modification (Davidson's key payoff).

## Main definitions

* `ThematicAxioms` — Aktionsart selection + uniqueness constraints
* `agent_holder_disjoint` — derived from the axioms
* `EventModifier` + `modify` + `modify_comm` + `modify_assoc` —
  adverbial modification as predicate conjunction ([davidson-1967])
* `stativeLogicalForm` / `modifiedStativeLogicalForm` /
  `modified_stative_is_pm` — stative LFs with `holder`
  ([wellwood-2015] §3.2)

## References

* [davidson-1967] (adverbial modification = predicate conjunction)
* [parsons-1990] (thematic roles as separate conjuncts)
* [wellwood-2015] §3.2 (gradable adjectives over states)
-/

namespace ArgumentStructure

open Modifier (intersective intersective_apply)

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
    frame.agent x e → e.sort = .dynamic
  /-- Holders only participate in states. -/
  holder_selects_state : ∀ (x : Entity) (e : Event Time),
    frame.holder x e → e.sort = .stative
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

/-! ### Adverbial modification (Davidson's key payoff) -/

/-- An event modifier: a predicate on events (e.g., "quickly", "in the park"). -/
abbrev EventModifier (Time : Type*) [LinearOrder Time] := Event Time → Prop

/-- Apply a modifier to an event predicate via conjunction.
    [davidson-1967]: adverbial modification is conjunction of event
    predicates. "John kicked the ball quickly" = ∃e. kick(e) ∧
    Agent(j,e) ∧ Patient(b,e) ∧ quickly(e).

    Davidson's adverbial modification is the intersective modifier
    (`Semantics.Modification.intersective`) at event-predicate type. -/
def modify {Time : Type*} [LinearOrder Time]
    (P : Event Time → Prop) (M : EventModifier Time) : Event Time → Prop :=
  intersective P M

/-- Modification is commutative: "quickly and loudly" = "loudly and quickly". -/
theorem modify_comm {Time : Type*} [LinearOrder Time]
    (P : Event Time → Prop) (M₁ M₂ : EventModifier Time) :
    modify (modify P M₁) M₂ = modify (modify P M₂) M₁ := by
  funext e
  simp only [modify, intersective_apply]
  exact propext ⟨λ ⟨⟨hp, hm1⟩, hm2⟩ => ⟨⟨hp, hm2⟩, hm1⟩,
                λ ⟨⟨hp, hm2⟩, hm1⟩ => ⟨⟨hp, hm1⟩, hm2⟩⟩

/-- Modification is associative. -/
theorem modify_assoc {Time : Type*} [LinearOrder Time]
    (P : Event Time → Prop) (M₁ M₂ : EventModifier Time) :
    modify (modify P M₁) M₂ = modify P (λ e => M₁ e ∧ M₂ e) := by
  funext e
  simp only [modify, intersective_apply]
  exact propext ⟨λ ⟨⟨hp, hm1⟩, hm2⟩ => ⟨hp, hm1, hm2⟩,
                λ ⟨hp, hm1, hm2⟩ => ⟨⟨hp, hm1⟩, hm2⟩⟩

/-! ### Stative logical forms ([wellwood-2015] §3.2) -/

/-- "x is happy" ↦ ∃s. P(s) ∧ Holder(x, s). Parallel to
    `intransitiveLogicalForm` but using `holder` instead of `agent`,
    reflecting that states select for holders. -/
def stativeLogicalForm {Entity Time : Type*} [LinearOrder Time]
    (P : Event Time → Prop) (frame : ThematicFrame Entity Time)
    (x : Entity) : Prop :=
  ∃ s : Event Time, P s ∧ frame.holder x s

/-- "x is happy in the morning" ↦ ∃s. P(s) ∧ Holder(x, s) ∧ M(s).
    State modification = event modification applied to states. -/
def modifiedStativeLogicalForm {Entity Time : Type*} [LinearOrder Time]
    (P : Event Time → Prop) (frame : ThematicFrame Entity Time)
    (x : Entity) (M : EventModifier Time) : Prop :=
  ∃ s : Event Time, P s ∧ frame.holder x s ∧ M s

/-- Modified stative = stative of modified predicate (Predicate Modification):
    state modification is an instance of Davidson's conjunction-based
    event modification. -/
theorem modified_stative_is_pm {Entity Time : Type*} [LinearOrder Time]
    (P : Event Time → Prop) (frame : ThematicFrame Entity Time)
    (x : Entity) (M : EventModifier Time) :
    modifiedStativeLogicalForm P frame x M ↔
      stativeLogicalForm (modify P M) frame x := by
  simp only [modifiedStativeLogicalForm, stativeLogicalForm, modify, intersective_apply]
  exact ⟨fun ⟨s, hp, hh, hm⟩ => ⟨s, ⟨hp, hm⟩, hh⟩,
         fun ⟨s, ⟨hp, hm⟩, hh⟩ => ⟨s, hp, hh, hm⟩⟩

end ArgumentStructure
