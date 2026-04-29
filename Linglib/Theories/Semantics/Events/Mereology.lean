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

namespace Semantics.Events.Mereology

open Semantics.Events
open Core.Time
open Features
open _root_.Mereology

-- Re-export Core.Mereology definitions in this namespace so that
-- existing `open Semantics.Events.Mereology` continues to work.
-- §1–12 from Core/Mereology.lean (base algebra + pullback + bridges):
export _root_.Mereology (AlgClosure CUM DIV QUA Atom
  algClosure_cum subset_algClosure qua_cum_incompatible atom_qua
  div_closed_under_le cum_qua_disjoint algClosure_of_mem
  algClosure_mono algClosure_idempotent
  IsSumHom Overlap ExtMeasure extMeasure_qua
  QMOD qmod_sub
  qua_pullback cum_pullback extMeasure_strictMono singleton_qua
  extMeasure_qua' qua_pullback_comp
  IsSumHom.strictMono_of_injective qua_of_injective_sumHom
  cum_qua_dimension_disjoint
  -- §1–4 from Core/MereoDim.lean (Mereology ↔ MeasurementScale bridge):
  quaBoundedness cumBoundedness
  qua_boundedness_licensed cum_boundedness_blocked
  extMeasure_kennedy extMeasure_rouillard
  cum_sum_exceeds cum_sum_exceeds_both
  -- §5–8 from Core/MereoDim.lean (MereoDim typeclass):
  MereoDim instMereoDimOfExtMeasure MereoDim.ofInjSumHom MereoDim.comp
  qua_pullback_mereoDim qua_pullback_mereoDim_comp
  -- §9–10 from Core/MereoDim.lean (MeasureProportional + LaxMeasureSquare):
  MeasureProportional LaxMeasureSquare
  LaxMeasureSquare.laxCommutativity
  LaxMeasureSquare.mereoDim₁ LaxMeasureSquare.mereoDim₂
  LaxMeasureSquare.qua_pullback₂)

-- ════════════════════════════════════════════════════
-- § 1. Event CEM (Classical Extensional Mereology)
-- ════════════════════════════════════════════════════

/-- Classical Extensional Mereology for events: enriches `EventMereology`
    with binary sum (⊔) via `SemilatticeSup (Ev Time)`.
    @cite{champollion-2017} Ch. 2: event domain forms a join semilattice. -/
class EventCEM (Time : Type*) [LinearOrder Time]
    extends EventMereology Time where
  /-- Events form a join semilattice (binary sum ⊕ exists). -/
  evSemilatticeSup : SemilatticeSup (Ev Time)
  /-- ≤ from SemilatticeSup agrees with partOf. -/
  le_eq_partOf : ∀ (e₁ e₂ : Ev Time),
    @LE.le (Ev Time) evSemilatticeSup.toLE e₁ e₂ ↔ partOf e₁ e₂
  /-- Intervals form a join semilattice (for τ homomorphism). -/
  intervalSemilatticeSup : SemilatticeSup (Interval Time)
  /-- τ is a sum homomorphism: τ(e₁ ⊕ e₂) = τ(e₁) ⊕ τ(e₂).
      @cite{champollion-2017} §2.5.1. -/
  τ_hom : ∀ (e₁ e₂ : Ev Time),
    (@SemilatticeSup.sup _ evSemilatticeSup e₁ e₂).runtime =
     @SemilatticeSup.sup _ intervalSemilatticeSup e₁.runtime e₂.runtime

-- Provide the SemilatticeSup instance from EventCEM
noncomputable instance eventCEMSemilatticeSup (Time : Type*) [LinearOrder Time]
    [cem : EventCEM Time] : SemilatticeSup (Ev Time) :=
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
  ∀ (e₁ e₂ : Ev Time), P e₁ → P e₂ →
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

    This is stated as: given a function `θ : Ev Time → Entity` extracting
    the unique role-filler, θ is a sum homomorphism. -/
class RoleHom (Entity Time : Type*) [LinearOrder Time] [cem : EventCEM Time]
    [SemilatticeSup Entity] where
  /-- Agent extraction function (partial: only defined for events with agents). -/
  agentOf : Ev Time → Entity
  /-- Agent extraction preserves ⊕. -/
  agent_hom : @IsSumHom _ _ cem.evSemilatticeSup _ agentOf
  /-- Patient extraction function. -/
  patientOf : Ev Time → Entity
  /-- Patient extraction preserves ⊕. -/
  patient_hom : @IsSumHom _ _ cem.evSemilatticeSup _ patientOf
  /-- Theme extraction function. -/
  themeOf : Ev Time → Entity
  /-- Theme extraction preserves ⊕. -/
  theme_hom : @IsSumHom _ _ cem.evSemilatticeSup _ themeOf

-- ════════════════════════════════════════════════════
-- § 4. Trace Functions: τ, σ, θ as IsSumHom (@cite{champollion-2017} §2.5)
-- ════════════════════════════════════════════════════

/-! ### Trace functions = sum-homomorphisms on `Ev T`

@cite{champollion-2017} §2.5 calls τ, σ, and the thematic-role extractors
"trace functions" — functions that trace each event into a different
domain (time, space, entities). The structural property they share is
**sum-homomorphism**: the trace of a sum equals the sum of the traces.
Linglib uses `Mereology.IsSumHom` as the unifying abstraction; any function
`f : Ev Time → β` that admits an `IsSumHom` instance qualifies as a trace
function for substrate purposes.

The concrete trace functions in linglib are:
- **τ** (runtime): instance below, derived from `EventCEM.τ_hom`.
- **σ** (spatial extent): `instIsSumHomσ` in `SpatialTrace.lean`,
  derived from `SpatialTrace.σ_map_sup`.
- **agentOf / patientOf / themeOf**: instances below, derived from
  `RoleHom.agent_hom / patient_hom / theme_hom`.

This unification means SR theorems (`StratifiedReference.lean`) can be
stated dimension-polymorphically as
`(d : Ev T → β) [IsSumHom d] → ...` and instantiate uniformly across all
five trace functions, rather than per-trace.
-/

/-- τ is a sum homomorphism: follows directly from EventCEM.τ_hom.
    τ(e₁ ⊕ e₂) = τ(e₁) ⊕ τ(e₂).
    @cite{champollion-2017} §2.5.1: the runtime function preserves sums. -/
theorem τ_is_sum_hom (Time : Type*) [LinearOrder Time] [cem : EventCEM Time] :
    ∀ (e₁ e₂ : Ev Time),
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

end Semantics.Events.Mereology
