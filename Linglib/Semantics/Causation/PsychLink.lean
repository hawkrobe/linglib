import Linglib.Semantics.Causation.Psych
import Linglib.Core.Order.Interval
import Linglib.Semantics.Events.Basic
import Linglib.Semantics.Conditionals.Counterfactual

/-!
# Psych Verb Causal Links

[kim-2024] [allen-1983] [bach-1986] Formal integration of [kim-2024]'s maintenance relation with existing [lewis-1973]
infrastructure: temporal intervals, event sorts,
and counterfactual semantics.

Kim's core claim: stative Class II psych verbs involve a
**maintenance** causal relation, not eventive causation. The two flavors
differ along three dimensions:

| Property | Eventive | Maintenance |
|----------|----------|-------------|
| Cause sort | event (external percept) | state (mental representation) |
| Effect | BECOME + state (transition) | state only (no transition) |
| Temporal | cause precedes effect | cause and effect contemporaneous |
| Counterfactual | effect persists after cause ceases | effect ceases with cause |

The first three properties are formalized using existing Linglib types:
`Features.Dynamicity`, `NonemptyInterval.precedes`/`.overlaps`.
The fourth uses `universalCounterfactual` from `Counterfactual.lean`.

## Key results

- Maintenance is temporally symmetric (states overlap); eventive is asymmetric
- Temporal precedence and overlap are mutually exclusive (the two flavors
  can't hold simultaneously for the same pair of eventualities)
- `CausalSource.toLink` grounds the two-constructor enum in event structure

-/

namespace Causation.PsychLink

open Causation.Psych (CausalSource)
open Core.Order (SimilarityOrdering)
open Semantics.Conditionals.Counterfactual (universalCounterfactual)

/-! ### PsychCausalLink -/

/-- A causal link between two eventualities in psych verb semantics.

    Bundles event-structural and temporal properties that distinguish
    eventive causation (percept → state change) from maintenance
    causation (representation → state persistence). -/
structure PsychCausalLink (Time : Type*) [LinearOrder Time] where
  /-- Ontological sort of the causing eventuality -/
  causeSort : Features.Dynamicity
  /-- Ontological sort of the caused eventuality -/
  effectSort : Features.Dynamicity
  /-- Does the effect involve a transition (BECOME in [rappaport-hovav-levin-1998])?
      Eventive: [CAUSE [BECOME [STATE]]] — yes.
      Maintenance: [CAUSE [STATE]] — no. -/
  involvesTransition : Bool
  /-- Temporal constraint on the runtimes of cause and effect -/
  temporalConstraint : NonemptyInterval Time → NonemptyInterval Time → Prop

/-! ### Eventive and Maintenance Links -/

/-- Eventive causation: an external percept/event CAUSES a change of
    mental state. The cause temporally precedes the effect.

    Event structure: [[percept ACT] CAUSE [BECOME [experiencer STATE]]]
    Example: "The noise frightened John" — the noise event happens,
    THEN John enters the frightened state. -/
def eventiveLink (Time : Type*) [LinearOrder Time] : PsychCausalLink Time :=
  { causeSort := .dynamic
    effectSort := .dynamic
    involvesTransition := true
    temporalConstraint := NonemptyInterval.precedes }

/-- Maintenance causation: a mental representation MAINTAINS a
    psychological state. Cause and effect are temporally contemporaneous.

    Event structure: [[representation STATE] CAUSE [experiencer STATE]]
    Example: "The problem concerns John" — the problem's mental
    representation and John's concern state coexist; if the representation
    ceased, the concern would cease.

    [kim-2024] identifies three defining properties:
    (a) Relates two eventualities (both states)
    (b) Temporal contemporaneity (τ(cause) overlaps τ(effect))
    (c) Counterfactual dependence (effect ceases when cause ceases) -/
def maintenanceLink (Time : Type*) [LinearOrder Time] : PsychCausalLink Time :=
  { causeSort := .stative
    effectSort := .stative
    involvesTransition := false
    temporalConstraint := NonemptyInterval.overlaps }

/-! ### CausalSource → PsychCausalLink -/

/-- Ground `CausalSource` (a two-constructor enum) in the richer
    `PsychCausalLink` structure. External source = eventive causation;
    internal source = maintenance causation. -/
def CausalSource.toLink (Time : Type*) [LinearOrder Time] :
    CausalSource → PsychCausalLink Time
  | .external => eventiveLink Time
  | .internal => maintenanceLink Time

/-! ### Temporal Theorems -/

/-- Maintenance is temporally symmetric: if cause overlaps effect,
    effect overlaps cause. Delegates to `NonemptyInterval.overlaps_symm`. -/
theorem maintenance_temporal_symmetric {Time : Type*} [LinearOrder Time]
    (i₁ i₂ : NonemptyInterval Time)
    (h : (maintenanceLink Time).temporalConstraint i₁ i₂) :
    (maintenanceLink Time).temporalConstraint i₂ i₁ :=
  NonemptyInterval.overlaps_symm h

/-- Eventive causation is temporally irreflexive: no eventuality
    can precede itself. Delegates to `NonemptyInterval.precedes_irrefl`. -/
theorem eventive_temporal_irrefl {Time : Type*} [LinearOrder Time]
    (i : NonemptyInterval Time) :
    ¬ (eventiveLink Time).temporalConstraint i i :=
  NonemptyInterval.precedes_irrefl i

/-- Precedence and overlap are mutually exclusive: if cause precedes
    effect, they cannot overlap. This is the structural basis for the
    eventive/stative dichotomy — the two temporal configurations are
    incompatible for any given pair of eventualities.
    Delegates to `NonemptyInterval.precedes_not_overlaps`. -/
theorem precedes_excludes_overlap {Time : Type*} [LinearOrder Time]
    (i₁ i₂ : NonemptyInterval Time)
    (h : (eventiveLink Time).temporalConstraint i₁ i₂) :
    ¬ (maintenanceLink Time).temporalConstraint i₁ i₂ :=
  NonemptyInterval.precedes_not_overlaps h

/-! ### Event Sort Properties -/

/-- Maintenance relates two states ([kim-2024] property (a)). -/
theorem maintenance_both_states {Time : Type*} [LinearOrder Time] :
    (maintenanceLink Time).causeSort = .stative ∧
    (maintenanceLink Time).effectSort = .stative := ⟨rfl, rfl⟩

/-- Eventive causation relates two dynamic eventualities. -/
theorem eventive_both_dynamic {Time : Type*} [LinearOrder Time] :
    (eventiveLink Time).causeSort = .dynamic ∧
    (eventiveLink Time).effectSort = .dynamic := ⟨rfl, rfl⟩

/-- Maintenance involves no transition (no BECOME). -/
theorem maintenance_no_transition {Time : Type*} [LinearOrder Time] :
    (maintenanceLink Time).involvesTransition = false := rfl

/-- Eventive causation involves a transition (BECOME). -/
theorem eventive_has_transition {Time : Type*} [LinearOrder Time] :
    (eventiveLink Time).involvesTransition = true := rfl

/-- The two causal flavors assign opposite values on every dimension. -/
theorem flavors_differ_on_all_dimensions {Time : Type*} [LinearOrder Time] :
    (eventiveLink Time).causeSort = .dynamic ∧
    (maintenanceLink Time).causeSort = .stative ∧
    (eventiveLink Time).involvesTransition = true ∧
    (maintenanceLink Time).involvesTransition = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Counterfactual Predicates -/

/-- Counterfactual dependence: in the closest worlds where the cause
    doesn't hold, the effect doesn't hold either.

    ¬cause □→ ¬effect

    This characterizes maintenance causation ([kim-2024] property (c)):
    "The problem concerns John" — in the closest worlds where John
    no longer has the mental representation, the concern ceases. -/
def counterfactuallyDependent {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W)
    (causeProp effectProp : W → Prop)
    [DecidablePred causeProp] [DecidablePred effectProp] (w : W) : Prop :=
  universalCounterfactual sim
    (fun w => ¬ causeProp w) (fun w => ¬ effectProp w) w

instance counterfactuallyDependent_decidable {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W)
    (causeProp effectProp : W → Prop)
    [DecidablePred causeProp] [DecidablePred effectProp] (w : W) :
    Decidable (counterfactuallyDependent sim causeProp effectProp w) :=
  inferInstanceAs (Decidable (universalCounterfactual _ _ _ _))

/-- Counterfactual persistence: in the closest worlds where the cause
    doesn't hold, the effect STILL holds.

    ¬cause □→ effect

    This characterizes eventive causation: "The noise frightened John" —
    even if the noise hadn't occurred (in the closest worlds), the
    frightened state, once established by BECOME, persists independently. -/
def counterfactuallyPersistent {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W)
    (causeProp effectProp : W → Prop)
    [DecidablePred causeProp] [DecidablePred effectProp] (w : W) : Prop :=
  universalCounterfactual sim
    (fun w => ¬ causeProp w) effectProp w

instance counterfactuallyPersistent_decidable {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W)
    (causeProp effectProp : W → Prop)
    [DecidablePred causeProp] [DecidablePred effectProp] (w : W) :
    Decidable (counterfactuallyPersistent sim causeProp effectProp w) :=
  inferInstanceAs (Decidable (universalCounterfactual _ _ _ _))

/-- Counterfactual dependence and persistence are mutually exclusive
    when the set of closest ¬cause worlds is non-empty.

    If all closest ¬cause worlds satisfy ¬effect (dependence), then
    at least one closest world falsifies effect, so persistence fails.

    Proved by extracting a witness from the non-empty closest-world
    list and showing it satisfies `¬ effectProp w` (from dependence)
    and `effectProp w` (from persistence), a contradiction. -/
theorem dependent_excludes_persistent {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W)
    (causeProp effectProp : W → Prop)
    [DecidablePred causeProp] [DecidablePred effectProp] (w : W)
    (hDep : counterfactuallyDependent sim causeProp effectProp w)
    (hNonempty : (sim.closestWorlds w
      (Finset.univ.filter (fun w => ¬ causeProp w))).Nonempty) :
    ¬ counterfactuallyPersistent sim causeProp effectProp w := by
  simp only [counterfactuallyDependent, universalCounterfactual] at hDep
  simp only [counterfactuallyPersistent, universalCounterfactual]
  intro hall
  obtain ⟨x, hx⟩ := hNonempty
  exact (hDep x hx) (hall x hx)

/-! ### [kim-2024]: Three Properties of Maintenance -/

/-- The three defining properties of maintenance causation from
    [kim-2024], formalized using existing infrastructure:

    (a) Relates two eventualities — both are states (`Features.Dynamicity.stative`)
    (b) Temporal contemporaneity — `NonemptyInterval.overlaps`
    (c) No transition — effect is a persisting state, not a change

    Property (c) is formalized structurally (no BECOME) rather than
    via counterfactuals, because the counterfactual characterization
    ("effect ceases when cause ceases") requires a concrete world space
    and similarity ordering. The structural version — no BECOME means
    no independent grounding for the effect — is the deeper explanation
    for WHY maintenance-caused states are counterfactually dependent. -/
theorem maintenance_three_properties {Time : Type*} [LinearOrder Time] :
    -- (a) Both eventualities are states
    (maintenanceLink Time).causeSort = .stative ∧
    (maintenanceLink Time).effectSort = .stative ∧
    -- (b) Temporal contemporaneity (overlaps, not precedes)
    (maintenanceLink Time).temporalConstraint = NonemptyInterval.overlaps ∧
    -- (c) No transition (no BECOME)
    (maintenanceLink Time).involvesTransition = false :=
  ⟨rfl, rfl, rfl, rfl⟩

end Causation.PsychLink
