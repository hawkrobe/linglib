import Linglib.Core.Mereology
import Linglib.Core.MereoDim
import Linglib.Theories.Semantics.Events.Basic
import Linglib.Theories.Semantics.Lexical.Verb.Aspect

/-!
# Event Mereology

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

## References

- Champollion, L. (2017). *Parts of a Whole: Distributivity as a Bridge
  Between Aspect and Measurement*. OUP.
- Bach, E. (1986). The algebra of events.
-/

namespace Semantics.Events.Mereology

open Semantics.Events
open Core.Time
open Semantics.Lexical.Verb.Aspect
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
  extMeasure_kennedyMIP extMeasure_rouillardMIP
  cum_sum_exceeds cum_sum_exceeds_both)

-- ════════════════════════════════════════════════════
-- § 1. Event CEM (Classical Extensional Mereology)
-- ════════════════════════════════════════════════════

/-- Classical Extensional Mereology for events: enriches `EventMereology`
    with binary sum (⊔) via `SemilatticeSup (Ev Time)`.
    Champollion (2017) Ch. 2: event domain forms a join semilattice. -/
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
      Champollion (2017) §2.5.1. -/
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
    Champollion (2017) §3.2: activities and states are lexically cumulative. -/
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
    Champollion (2017) §2.5.1 eq. 34–35: Agent(e₁ ⊕ e₂) = Agent(e₁) ⊕ Agent(e₂).

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
-- § 4. τ Homomorphism
-- ════════════════════════════════════════════════════

/-- τ is a sum homomorphism: follows directly from EventCEM.τ_hom.
    τ(e₁ ⊕ e₂) = τ(e₁) ⊕ τ(e₂).
    Champollion (2017) §2.5.1: the runtime function preserves sums. -/
theorem τ_is_sum_hom (Time : Type*) [LinearOrder Time] [cem : EventCEM Time] :
    ∀ (e₁ e₂ : Ev Time),
      (@SemilatticeSup.sup _ cem.evSemilatticeSup e₁ e₂).runtime =
      @SemilatticeSup.sup _ cem.intervalSemilatticeSup e₁.runtime e₂.runtime :=
  cem.τ_hom

-- ════════════════════════════════════════════════════
-- § 5. Bridges to Existing Types
-- ════════════════════════════════════════════════════

/-- Atelic Vendler classes yield predicates that are naturally cumulative
    (Champollion 2017, §3.2). States and activities have the subinterval
    property, which entails CUM for their event predicates. -/
theorem vendlerClass_atelic_implies_cum_intent
    (c : VendlerClass) (h : c.telicity = .atelic) :
    c = .state ∨ c = .activity := by
  cases c <;> simp [VendlerClass.telicity] at h <;> try exact Or.inl rfl
  · exact Or.inr rfl

/-- Telic Vendler classes yield predicates that are naturally quantized
    (Champollion 2017, §3.3). Achievements and accomplishments lack
    the subinterval property, corresponding to QUA. -/
theorem vendlerClass_telic_implies_qua_intent
    (c : VendlerClass) (h : c.telicity = .telic) :
    c = .achievement ∨ c = .accomplishment := by
  cases c <;> simp [VendlerClass.telicity] at h
  · exact Or.inl rfl
  · exact Or.inr rfl

end Semantics.Events.Mereology
