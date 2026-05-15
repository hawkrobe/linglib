import Linglib.Core.Mereology
import Linglib.Core.Scales.MereoDim
import Linglib.Theories.Semantics.Events.Basic
import Linglib.Features.Aktionsart

/-!
# Event Mereology
@cite{bach-1986} @cite{champollion-2017}

Event-specific mereological infrastructure built on top of the generic
`Core.Mereology` definitions. Specializes `CUM`, `QUA`, `IsSumHom`, etc.
to event structures with `EventCEM`, thematic role homomorphisms, and
Vendler class bridges.

Generic mereological definitions (`CUM`, `DIV`, `QUA`, `Atom`, `AlgClosure`,
`IsSumHom`, `Overlap`, `ExtMeasure`, `QMOD`) live in `Core.Mereology`.

## Sections

1. Event CEM (Classical Extensional Mereology enrichment)
2. Lexical Cumulativity
3. Role Homomorphism (θ preserves ⊕)
4. τ Homomorphism (runtime preserves ⊕)
5. Bridges to existing types

-/

namespace Semantics.Events.CEM

open Semantics.Events
open Core.Time
open Features
open _root_.Mereology

-- Generic mereological vocabulary (CUM/QUA/AlgClosure/QMOD/ExtMeasure
-- /MereoDim/LaxMeasureSquare/...) lives in `Core.Mereology` and
-- `Core.Scales.MereoDim`. Consumers do `open Mereology` to bring it
-- into scope rather than relying on re-exports here.

-- ════════════════════════════════════════════════════
-- § 1. Event CEM (Classical Extensional Mereology)
-- ════════════════════════════════════════════════════

/-- Classical Extensional Mereology for events: enriches `EventMereology`
    with binary sum (⊔) via `SemilatticeSup (Event Time)`.
    @cite{champollion-2017} Ch. 2: event domain forms a join semilattice. -/
class EventCEM (Time : Type*) [LinearOrder Time]
    extends EventMereology Time where
  /-- Events form a join semilattice (binary sum ⊕ exists). -/
  evSemilatticeSup : SemilatticeSup (Event Time)
  /-- ≤ from SemilatticeSup agrees with partOf. -/
  le_eq_partOf : ∀ (e₁ e₂ : Event Time),
    @LE.le (Event Time) evSemilatticeSup.toLE e₁ e₂ ↔ partOf e₁ e₂
  /-- Intervals form a join semilattice (for τ homomorphism). -/
  intervalSemilatticeSup : SemilatticeSup (Interval Time)
  /-- τ is a sum homomorphism: τ(e₁ ⊕ e₂) = τ(e₁) ⊕ τ(e₂).
      @cite{champollion-2017} §2.5.1. -/
  τ_hom : ∀ (e₁ e₂ : Event Time),
    (@SemilatticeSup.sup _ evSemilatticeSup e₁ e₂).runtime =
     @SemilatticeSup.sup _ intervalSemilatticeSup e₁.runtime e₂.runtime

-- Provide the SemilatticeSup instance from EventCEM
noncomputable instance eventCEMSemilatticeSup (Time : Type*) [LinearOrder Time]
    [cem : EventCEM Time] : SemilatticeSup (Event Time) :=
  cem.evSemilatticeSup

-- ════════════════════════════════════════════════════
-- § 2. Lexical Cumulativity
-- ════════════════════════════════════════════════════

/-- Lexical cumulativity for event predicates: the event-specific
    instantiation of CUM. A verb predicate V is lexically cumulative
    iff for any two V-events, their sum is also a V-event.
    @cite{champollion-2017} §3.2: activities and states are lexically cumulative. -/
def LexCum (Time : Type*) [LinearOrder Time] [cem : EventCEM Time]
    (P : EvPred Time) : Prop :=
  ∀ (e₁ e₂ : Event Time), P e₁ → P e₂ →
    P (@SemilatticeSup.sup _ cem.evSemilatticeSup e₁ e₂)

/-- LexCum is exactly CUM specialized to EvPred.
    This bridges the abstract and event-specific formulations. -/
theorem cum_iff_lexCum (Time : Type*) [LinearOrder Time] [cem : EventCEM Time]
    (P : EvPred Time) :
    @CUM _ cem.evSemilatticeSup P ↔ LexCum Time P := by
  constructor
  · intro h e₁ e₂ h₁ h₂; exact h e₁ e₂ h₁ h₂
  · intro h x y hx hy; exact h x y hx hy

-- ════════════════════════════════════════════════════
-- § 3. Role Homomorphism (θ preserves ⊕)
-- ════════════════════════════════════════════════════

/-- A thematic-role sum homomorphism: the function mapping each event
    to its θ-role filler preserves ⊕.
    @cite{champollion-2017} §2.5.1 eq. 34–35: Agent(e₁ ⊕ e₂) = Agent(e₁) ⊕ Agent(e₂).

    This is stated as: given a function `θ : Event Time → Entity` extracting
    the unique role-filler, θ is a sum homomorphism. -/
class RoleHom (Entity Time : Type*) [LinearOrder Time] [cem : EventCEM Time]
    [SemilatticeSup Entity] where
  /-- Agent extraction function (partial: only defined for events with agents). -/
  agentOf : Event Time → Entity
  /-- Agent extraction preserves ⊕. -/
  agent_hom : @IsSumHom _ _ cem.evSemilatticeSup _ agentOf
  /-- Patient extraction function. -/
  patientOf : Event Time → Entity
  /-- Patient extraction preserves ⊕. -/
  patient_hom : @IsSumHom _ _ cem.evSemilatticeSup _ patientOf
  /-- Theme extraction function. -/
  themeOf : Event Time → Entity
  /-- Theme extraction preserves ⊕. -/
  theme_hom : @IsSumHom _ _ cem.evSemilatticeSup _ themeOf

-- ════════════════════════════════════════════════════
-- § 4. Trace Functions: τ, σ, θ as IsSumHom (@cite{champollion-2017} §2.5)
-- ════════════════════════════════════════════════════

/-! ### Trace functions = sum-homomorphisms on `Event T`

@cite{champollion-2017} §2.5 calls τ, σ, and the thematic-role extractors
"trace functions" — functions that trace each event into a different
domain (time, space, entities). The structural property they share is
**sum-homomorphism**: the trace of a sum equals the sum of the traces.
Linglib uses `Mereology.IsSumHom` as the unifying abstraction; any function
`f : Event Time → β` that admits an `IsSumHom` instance qualifies as a trace
function for substrate purposes.

The concrete trace functions in linglib are:
- **τ** (runtime): instance below, derived from `EventCEM.τ_hom`.
- **σ** (spatial extent): `instIsSumHomσ` in `SpatialTrace.lean`,
  derived from `SpatialTrace.σ_map_sup`.
- **agentOf / patientOf / themeOf**: instances below, derived from
  `RoleHom.agent_hom / patient_hom / theme_hom`.

This unification means SR theorems (`StratifiedReference.lean`) can be
stated dimension-polymorphically as
`(d : Event T → β) [IsSumHom d] → ...` and instantiate uniformly across all
five trace functions, rather than per-trace.
-/

/-- τ is a sum homomorphism: follows directly from EventCEM.τ_hom.
    τ(e₁ ⊕ e₂) = τ(e₁) ⊕ τ(e₂).
    @cite{champollion-2017} §2.5.1: the runtime function preserves sums. -/
theorem τ_is_sum_hom (Time : Type*) [LinearOrder Time] [cem : EventCEM Time] :
    ∀ (e₁ e₂ : Event Time),
      (@SemilatticeSup.sup _ cem.evSemilatticeSup e₁ e₂).runtime =
      @SemilatticeSup.sup _ cem.intervalSemilatticeSup e₁.runtime e₂.runtime :=
  cem.τ_hom

/-- τ (runtime extraction) as an `IsSumHom` instance, derived from `EventCEM.τ_hom`.
    Enables `cum_pullback` to work automatically for τ without manually
    threading the sum-homomorphism proof. -/
noncomputable instance instIsSumHomRuntime (Time : Type*) [LinearOrder Time]
    [cem : EventCEM Time] :
    @IsSumHom _ _ cem.evSemilatticeSup cem.intervalSemilatticeSup
      (fun e => e.runtime) :=
  @IsSumHom.mk _ _ cem.evSemilatticeSup cem.intervalSemilatticeSup
    (fun e => e.runtime) (fun e₁ e₂ => cem.τ_hom e₁ e₂)

/-- agentOf as an `IsSumHom` instance, derived from `RoleHom.agent_hom`.
    Parallels `instIsSumHomRuntime` for τ — same mathlib pattern of
    promoting a structure field to a resolvable typeclass instance. -/
instance instIsSumHomAgent (Entity Time : Type*) [LinearOrder Time]
    [cem : EventCEM Time] [SemilatticeSup Entity] [rh : RoleHom Entity Time] :
    @IsSumHom _ _ cem.evSemilatticeSup _ rh.agentOf :=
  rh.agent_hom

/-- patientOf as an `IsSumHom` instance, derived from `RoleHom.patient_hom`. -/
instance instIsSumHomPatient (Entity Time : Type*) [LinearOrder Time]
    [cem : EventCEM Time] [SemilatticeSup Entity] [rh : RoleHom Entity Time] :
    @IsSumHom _ _ cem.evSemilatticeSup _ rh.patientOf :=
  rh.patient_hom

/-- themeOf as an `IsSumHom` instance, derived from `RoleHom.theme_hom`. -/
instance instIsSumHomTheme (Entity Time : Type*) [LinearOrder Time]
    [cem : EventCEM Time] [SemilatticeSup Entity] [rh : RoleHom Entity Time] :
    @IsSumHom _ _ cem.evSemilatticeSup _ rh.themeOf :=
  rh.theme_hom

-- ════════════════════════════════════════════════════
-- § 5. Bridges to Existing Types
-- ════════════════════════════════════════════════════

/-- Atelic Vendler classes are exactly states, activities, and semelfactives. -/
theorem vendlerClass_atelic_cases
    (c : VendlerClass) (h : c.telicity = .atelic) :
    c = .state ∨ c = .activity ∨ c = .semelfactive := by
  cases c <;> simp [VendlerClass.telicity] at h <;> first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)

/-- Telic Vendler classes are exactly achievements and accomplishments. -/
theorem vendlerClass_telic_cases
    (c : VendlerClass) (h : c.telicity = .telic) :
    c = .achievement ∨ c = .accomplishment := by
  cases c <;> simp [VendlerClass.telicity] at h
  · exact Or.inl rfl
  · exact Or.inr rfl

end Semantics.Events.CEM
