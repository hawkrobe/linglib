import Linglib.Theories.Semantics.Causation.PsychCausation
import Linglib.Core.Temporal.Time
import Linglib.Theories.Semantics.Events.Basic
import Linglib.Theories.Semantics.Conditionals.Counterfactual

/-!
# Psych Verb Causal Links

@cite{kim-2024} @cite{allen-1983} @cite{bach-1986} @cite{kratzer-2000}Formal integration of @cite{kim-2024}'s maintenance relation with existing @cite{lewis-1973}
infrastructure: temporal intervals, event sorts,
and counterfactual semantics.

Kim's core claim (§3.3): stative Class II psych verbs involve a
**maintenance** causal relation, not eventive causation. The two flavors
differ along three dimensions:

| Property | Eventive | Maintenance |
|----------|----------|-------------|
| Cause sort | event (external percept) | state (mental representation) |
| Effect | BECOME + state (transition) | state only (no transition) |
| Temporal | cause precedes effect | cause and effect contemporaneous |
| Counterfactual | effect persists after cause ceases | effect ceases with cause |

The first three properties are formalized using existing Linglib types:
`EventSort`, `Interval.precedes`/`.overlaps`.
The fourth uses `universalCounterfactualB` from `Counterfactual.lean`.

## Key results

- Maintenance is temporally symmetric (states overlap); eventive is asymmetric
- Temporal precedence and overlap are mutually exclusive (the two flavors
  can't hold simultaneously for the same pair of eventualities)
- `CausalSource.toLink` grounds the two-constructor enum in event structure

-/

namespace Semantics.Causation.PsychCausalLink

open Core.Time (Interval)
open Semantics.Events (EventSort)
open Semantics.Causation.PsychCausation (CausalSource)
open Semantics.Conditionals.Counterfactual (universalCounterfactualB closestWorldsB)

-- ════════════════════════════════════════════════════
-- § 1. PsychCausalLink
-- ════════════════════════════════════════════════════

/-- A causal link between two eventualities in psych verb semantics.

    Bundles event-structural and temporal properties that distinguish
    eventive causation (percept → state change) from maintenance
    causation (representation → state persistence). -/
structure PsychCausalLink (Time : Type*) [LinearOrder Time] where
  /-- Ontological sort of the causing eventuality -/
  causeSort : EventSort
  /-- Ontological sort of the caused eventuality -/
  effectSort : EventSort
  /-- Does the effect involve a transition (BECOME in @cite{rappaport-hovav-levin-1998})?
      Eventive: [CAUSE [BECOME [STATE]]] — yes.
      Maintenance: [CAUSE [STATE]] — no. -/
  involvesTransition : Bool
  /-- Temporal constraint on the runtimes of cause and effect -/
  temporalConstraint : Interval Time → Interval Time → Prop

-- ════════════════════════════════════════════════════
-- § 2. Eventive and Maintenance Links
-- ════════════════════════════════════════════════════

/-- Eventive causation: an external percept/event CAUSES a change of
    mental state. The cause temporally precedes the effect.

    Event structure: [[percept ACT] CAUSE [BECOME [experiencer STATE]]]
    Example: "The noise frightened John" — the noise event happens,
    THEN John enters the frightened state. -/
def eventiveLink (Time : Type*) [LinearOrder Time] : PsychCausalLink Time :=
  { causeSort := .action
    effectSort := .action
    involvesTransition := true
    temporalConstraint := Interval.precedes }

/-- Maintenance causation: a mental representation MAINTAINS a
    psychological state. Cause and effect are temporally contemporaneous.

    Event structure: [[representation STATE] CAUSE [experiencer STATE]]
    Example: "The problem concerns John" — the problem's mental
    representation and John's concern state coexist; if the representation
    ceased, the concern would cease.

    @cite{kim-2024} identifies three defining properties:
    (a) Relates two eventualities (both states)
    (b) Temporal contemporaneity (τ(cause) overlaps τ(effect))
    (c) Counterfactual dependence (effect ceases when cause ceases) -/
def maintenanceLink (Time : Type*) [LinearOrder Time] : PsychCausalLink Time :=
  { causeSort := .state
    effectSort := .state
    involvesTransition := false
    temporalConstraint := Interval.overlaps }

-- ════════════════════════════════════════════════════
-- § 3. CausalSource → PsychCausalLink
-- ════════════════════════════════════════════════════

/-- Ground `CausalSource` (a two-constructor enum) in the richer
    `PsychCausalLink` structure. External source = eventive causation;
    internal source = maintenance causation. -/
def CausalSource.toLink (Time : Type*) [LinearOrder Time] :
    CausalSource → PsychCausalLink Time
  | .external => eventiveLink Time
  | .internal => maintenanceLink Time

-- ════════════════════════════════════════════════════
-- § 4. Temporal Theorems
-- ════════════════════════════════════════════════════

/-- Maintenance is temporally symmetric: if cause overlaps effect,
    effect overlaps cause. This follows from `Interval.overlaps`
    being symmetric. -/
theorem maintenance_temporal_symmetric {Time : Type*} [LinearOrder Time]
    (i₁ i₂ : Interval Time)
    (h : (maintenanceLink Time).temporalConstraint i₁ i₂) :
    (maintenanceLink Time).temporalConstraint i₂ i₁ :=
  ⟨h.2, h.1⟩

/-- Eventive causation is temporally irreflexive: no eventuality
    can precede itself. Follows from `Interval.precedes` requiring
    `i.finish < i.start`, contradicting `i.valid : i.start ≤ i.finish`. -/
theorem eventive_temporal_irrefl {Time : Type*} [LinearOrder Time]
    (i : Interval Time) :
    ¬ (eventiveLink Time).temporalConstraint i i :=
  fun h => absurd (lt_of_lt_of_le h i.valid) (lt_irrefl _)

/-- Precedence and overlap are mutually exclusive: if cause precedes
    effect, they cannot overlap. This is the structural basis for the
    eventive/stative dichotomy — the two temporal configurations are
    incompatible for any given pair of eventualities. -/
theorem precedes_excludes_overlap {Time : Type*} [LinearOrder Time]
    (i₁ i₂ : Interval Time)
    (h : (eventiveLink Time).temporalConstraint i₁ i₂) :
    ¬ (maintenanceLink Time).temporalConstraint i₁ i₂ := by
  intro ⟨_, h2⟩
  exact absurd (lt_of_lt_of_le h h2) (lt_irrefl _)

-- ════════════════════════════════════════════════════
-- § 5. Event Sort Properties
-- ════════════════════════════════════════════════════

/-- Maintenance relates two states (Kim §3.3 property (a)). -/
theorem maintenance_both_states {Time : Type*} [LinearOrder Time] :
    (maintenanceLink Time).causeSort = .state ∧
    (maintenanceLink Time).effectSort = .state := ⟨rfl, rfl⟩

/-- Eventive causation relates two dynamic eventualities. -/
theorem eventive_both_dynamic {Time : Type*} [LinearOrder Time] :
    (eventiveLink Time).causeSort = .action ∧
    (eventiveLink Time).effectSort = .action := ⟨rfl, rfl⟩

/-- Maintenance involves no transition (no BECOME). -/
theorem maintenance_no_transition {Time : Type*} [LinearOrder Time] :
    (maintenanceLink Time).involvesTransition = false := rfl

/-- Eventive causation involves a transition (BECOME). -/
theorem eventive_has_transition {Time : Type*} [LinearOrder Time] :
    (eventiveLink Time).involvesTransition = true := rfl

/-- The two causal flavors assign opposite values on every dimension. -/
theorem flavors_differ_on_all_dimensions {Time : Type*} [LinearOrder Time] :
    (eventiveLink Time).causeSort = .action ∧
    (maintenanceLink Time).causeSort = .state ∧
    (eventiveLink Time).involvesTransition = true ∧
    (maintenanceLink Time).involvesTransition = false :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. Counterfactual Predicates
-- ════════════════════════════════════════════════════

/-- Counterfactual dependence: in the closest worlds where the cause
    doesn't hold, the effect doesn't hold either.

    ¬cause □→ ¬effect

    This characterizes maintenance causation (Kim §3.3 property (c)):
    "The problem concerns John" — in the closest worlds where John
    no longer has the mental representation, the concern ceases. -/
def counterfactuallyDependent {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W)
    (causeProp effectProp : W → Bool) (w : W) : Bool :=
  universalCounterfactualB closer domain
    (fun w => !causeProp w) (fun w => !effectProp w) w

/-- Counterfactual persistence: in the closest worlds where the cause
    doesn't hold, the effect STILL holds.

    ¬cause □→ effect

    This characterizes eventive causation: "The noise frightened John" —
    even if the noise hadn't occurred (in the closest worlds), the
    frightened state, once established by BECOME, persists independently. -/
def counterfactuallyPersistent {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W)
    (causeProp effectProp : W → Bool) (w : W) : Bool :=
  universalCounterfactualB closer domain
    (fun w => !causeProp w) effectProp w

/-- Counterfactual dependence and persistence are mutually exclusive
    when the set of closest ¬cause worlds is non-empty.

    If all closest ¬cause worlds satisfy ¬effect (dependence), then
    at least one closest world falsifies effect, so persistence fails.

    TODO: Proof via `List.all` reasoning — if `l.all (fun w => !f w)`
    and `l ≠ []`, then `l.all f = false`. -/
theorem dependent_excludes_persistent {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W)
    (causeProp effectProp : W → Bool) (w : W)
    (hDep : counterfactuallyDependent closer domain causeProp effectProp w = true)
    (hNonempty : (closestWorldsB closer domain w
      (domain.filter (fun w => !causeProp w))).length > 0) :
    counterfactuallyPersistent closer domain causeProp effectProp w = false := by
  sorry

-- ════════════════════════════════════════════════════
-- § 7. Kim §3.3: Three Properties of Maintenance
-- ════════════════════════════════════════════════════

/-- The three defining properties of maintenance causation from
    @cite{kim-2024}, formalized using existing infrastructure:

    (a) Relates two eventualities — both are states (`EventSort.state`)
    (b) Temporal contemporaneity — `Interval.overlaps`
    (c) No transition — effect is a persisting state, not a change

    Property (c) is formalized structurally (no BECOME) rather than
    via counterfactuals, because the counterfactual characterization
    ("effect ceases when cause ceases") requires a concrete world space
    and similarity ordering. The structural version — no BECOME means
    no independent grounding for the effect — is the deeper explanation
    for WHY maintenance-caused states are counterfactually dependent. -/
theorem maintenance_three_properties {Time : Type*} [LinearOrder Time] :
    -- (a) Both eventualities are states
    (maintenanceLink Time).causeSort = .state ∧
    (maintenanceLink Time).effectSort = .state ∧
    -- (b) Temporal contemporaneity (overlaps, not precedes)
    (maintenanceLink Time).temporalConstraint = Interval.overlaps ∧
    -- (c) No transition (no BECOME)
    (maintenanceLink Time).involvesTransition = false :=
  ⟨rfl, rfl, rfl, rfl⟩

end Semantics.Causation.PsychCausalLink
