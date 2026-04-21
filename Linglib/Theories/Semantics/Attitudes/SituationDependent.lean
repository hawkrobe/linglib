import Linglib.Core.Situation
import Linglib.Theories.Semantics.Attitudes.Doxastic

/-!
# Situation-Dependent Attitude Semantics
@cite{heim-kratzer-1998} @cite{kratzer-1998} @cite{lewis-1979} @cite{von-stechow-2009} @cite{ogihara-1989}

Attitude operators with temporal parameters: `believe`'s complement type shifts
from `st` (propositions = W → Bool) to `s(it)` (situation-dependent propositions =
Situation W Time → Bool). The doxastic alternatives `Dox_y(w,t)` become world–time
pairs, not just worlds.

## Motivation

Standard attitude semantics evaluates embedded clauses relative to worlds only:
  ⟦x believes p⟧(w) = ∀w' ∈ Dox_x(w). p(w')

This blocks sequence-of-tense (SOT) analysis, where embedded tense receives
a shifted interpretation relative to the matrix event time. @cite{von-stechow-2009}
synthesizes @cite{lewis-1979}, @cite{heim-kratzer-1998}, and @cite{ogihara-1989}: `believe`'s
complement type shifts to s(it), and doxastic alternatives become situation pairs.

## Design

Phase 1 (this module): Additive — new operators alongside existing ones, with
lifting theorems proving generalization. Zero breaking changes.

Phase 2 (future): Migrate `Doxastic.lean` and `Preferential.lean` to use
situation-dependent types natively, with backward-compat wrappers.

-/

namespace Semantics.Attitudes.SituationDependent

open Core.Time
open Semantics.Attitudes.Doxastic
  (Veridicality DoxasticPredicate AccessRel boxAt veridicalityHolds)

/-- Local alias for the agent-indexed accessibility relation
    used by the situation-dependent operators. Aliased to
    `Semantics.Attitudes.Doxastic.AccessRel` (Prop-valued, mathlib convention). -/
abbrev BAgentAccessRel (W E : Type*) := AccessRel W E


-- ════════════════════════════════════════════════════════════════
-- § Core Types
-- ════════════════════════════════════════════════════════════════

/-- Situation-dependent proposition type (von Stechow's s(it), Prop-valued).

    Where standard propositions are `W → Prop` (sets of worlds),
    situation-dependent propositions are `Situation W Time → Prop`
    (sets of world–time pairs). This is the complement type for
    attitude verbs that support temporal interpretation. -/
abbrev SitProp (W Time : Type*) := Situation W Time → Prop

/-- Situation-dependent accessibility relation: Dox_y(w,t) = {(w',t') |...}.

    Generalizes `BAgentAccessRel W E = E → W → W → Prop` to include
    temporal coordinates in both the evaluation and accessible situations. -/
abbrev SitAccessRel (W Time E : Type*) := E → Situation W Time → Situation W Time → Prop


-- ════════════════════════════════════════════════════════════════
-- § Modal Operators
-- ════════════════════════════════════════════════════════════════

/-- Situation-dependent universal modal.

    ⟦□p⟧(s) = ∀s' ∈ situations. R(agent, s, s') → p(s')

    Generalizes `Doxastic.boxAt` from worlds to situations. -/
def sitBoxAt {W Time E : Type*} (R : SitAccessRel W Time E) (agent : E)
    (s : Situation W Time) (situations : List (Situation W Time))
    (p : SitProp W Time) : Prop :=
  ∀ s' ∈ situations, R agent s s' → p s'

/-- Situation-dependent existential modal.

    ⟦◇p⟧(s) = ∃s' ∈ situations. R(agent, s, s') ∧ p(s')

    Generalizes `Doxastic.diaAt` from worlds to situations. -/
def sitDiaAt {W Time E : Type*} (R : SitAccessRel W Time E) (agent : E)
    (s : Situation W Time) (situations : List (Situation W Time))
    (p : SitProp W Time) : Prop :=
  ∃ s' ∈ situations, R agent s s' ∧ p s'

instance sitBoxAt_decidable {W Time E : Type*} (R : SitAccessRel W Time E)
    [∀ a s s', Decidable (R a s s')] (agent : E) (s : Situation W Time)
    (situations : List (Situation W Time)) (p : SitProp W Time) [DecidablePred p] :
    Decidable (sitBoxAt R agent s situations p) :=
  inferInstanceAs (Decidable (∀ s' ∈ situations, _))

instance sitDiaAt_decidable {W Time E : Type*} (R : SitAccessRel W Time E)
    [∀ a s s', Decidable (R a s s')] (agent : E) (s : Situation W Time)
    (situations : List (Situation W Time)) (p : SitProp W Time) [DecidablePred p] :
    Decidable (sitDiaAt R agent s situations p) :=
  inferInstanceAs (Decidable (∃ s' ∈ situations, _))


-- ════════════════════════════════════════════════════════════════
-- § Backward Compatibility: Lifting
-- ════════════════════════════════════════════════════════════════

/-- Lift a world-proposition to a situation-proposition.

    The lifted proposition ignores the temporal coordinate:
    `liftProp p s = p s.world`. This is the backward-compatibility
    embedding for code that hasn't moved to situation types yet. -/
def liftProp {W Time : Type*} (p : W → Prop) : SitProp W Time :=
  λ s => p s.world

/-- Lift a world-accessibility relation to a situation-accessibility relation.

    The lifted relation ignores temporal coordinates in accessibility:
    `liftAccess R agent s₁ s₂ = R agent s₁.world s₂.world`.
    This gives classic Hintikka behavior where doxastic alternatives
    differ only in world, not time. -/
def liftAccess {W Time E : Type*} (R : BAgentAccessRel W E) : SitAccessRel W Time E :=
  λ agent s₁ s₂ => R agent s₁.world s₂.world


-- ════════════════════════════════════════════════════════════════
-- § Lifting Theorems
-- ════════════════════════════════════════════════════════════════

/-- KEY THEOREM: Lifted operators recover classic Hintikka semantics.

    `sitBoxAt (liftAccess R) agent s sits (liftProp p)`
    is equivalent to
    `boxAt R agent s.world (sits.map (·.world)) p`.

    This means code using the old world-only operators produces
    identical results when embedded in the situation framework. -/
theorem sitBoxAt_lift_eq_boxAt {W Time E : Type*}
    (R : BAgentAccessRel W E) (agent : E) (s : Situation W Time)
    (sits : List (Situation W Time)) (p : W → Prop) :
    sitBoxAt (liftAccess R) agent s sits (liftProp p) ↔
    boxAt R agent s.world (sits.map (·.world)) p := by
  simp only [sitBoxAt, boxAt, liftAccess, liftProp, List.mem_map]
  constructor
  · intro h w' ⟨s', hs', heq⟩ hR
    exact heq ▸ h s' hs' (heq ▸ hR)
  · intro h s' hs' hR
    exact h s'.world ⟨s', hs', rfl⟩ hR


-- ════════════════════════════════════════════════════════════════
-- § Veridicality for Situations
-- ════════════════════════════════════════════════════════════════

/-- Veridicality check for situation-dependent propositions.

    For veridical predicates (know), requires p(s) at the
    evaluation situation. Mirrors `Doxastic.veridicalityHolds`. -/
def sitVeridicalityHolds {W Time : Type*} (v : Veridicality)
    (p : SitProp W Time) (s : Situation W Time) : Prop :=
  match v with
  | .veridical => p s
  | .nonVeridical => True

instance sitVeridicalityHolds_decidable {W Time : Type*} (v : Veridicality)
    (p : SitProp W Time) [DecidablePred p] (s : Situation W Time) :
    Decidable (sitVeridicalityHolds v p s) := by
  cases v <;> simp [sitVeridicalityHolds] <;> infer_instance

/-- Lifted veridicality matches world-level veridicality. -/
theorem sitVeridicalityHolds_lift {W Time : Type*} (v : Veridicality)
    (p : W → Prop) (s : Situation W Time) :
    sitVeridicalityHolds v (liftProp p) s ↔ veridicalityHolds v p s.world := by
  cases v <;> simp [sitVeridicalityHolds, veridicalityHolds, liftProp]


-- ════════════════════════════════════════════════════════════════
-- § Situation-Dependent Doxastic Predicate
-- ════════════════════════════════════════════════════════════════

/-- A situation-dependent doxastic attitude predicate.

    Generalizes `DoxasticPredicate` to use situation-dependent accessibility:
    `Dox_y(w,t) = {(w',t') |...}` instead of `Dox_y(w) = {w' |...}`.

    This is @cite{von-stechow-2009}'s enriched attitude semantics:
    ⟦x believes p⟧(w,t) = ∀(w',t') ∈ Dox_x(w,t). p(w')(t') -/
structure SitDoxasticPredicate (W Time E : Type*) where
  /-- Name of the predicate -/
  name : String
  /-- Situation-dependent accessibility relation -/
  access : SitAccessRel W Time E
  /-- Veridicality (veridical or not) -/
  veridicality : Veridicality

/-- Semantics for a situation-dependent doxastic predicate.

    ⟦x V that p⟧(s) = veridicalityHolds(V, p, s) ∧ ∀s'. R(x,s,s') → p(s')

    Generalizes `DoxasticPredicate.holdsAt` to situations. -/
def SitDoxasticPredicate.holdsAt {W Time E : Type*}
    (V : SitDoxasticPredicate W Time E) (agent : E) (p : SitProp W Time)
    (s : Situation W Time) (situations : List (Situation W Time)) : Prop :=
  sitVeridicalityHolds V.veridicality p s ∧ sitBoxAt V.access agent s situations p


-- ════════════════════════════════════════════════════════════════
-- § Converting Old to New
-- ════════════════════════════════════════════════════════════════

/-- Lift a world-level `DoxasticPredicate` to a situation-dependent one.

    The accessibility relation ignores temporal coordinates (classic
    Hintikka behavior), and veridicality is preserved.
    Use this to embed existing attitude predicates into the
    situation-dependent framework without changing their behavior. -/
def liftDoxastic {W E : Type*} (V : DoxasticPredicate W E)
    (Time : Type*) : SitDoxasticPredicate W Time E where
  name := V.name
  access := liftAccess V.access
  veridicality := V.veridicality

/-- The lifted predicate matches the original semantics.

    `(liftDoxastic V Time).holdsAt agent (liftProp p) s sits`
    iff `V.holdsAt agent p s.world (sits.map.world)`.

    This is the key backward-compatibility theorem: any existing
    analysis using `DoxasticPredicate` can be replayed exactly
    in the situation-dependent framework by lifting. -/
theorem liftDoxastic_holdsAt_eq {W Time E : Type*}
    (V : DoxasticPredicate W E) (agent : E)
    (p : W → Prop) (s : Situation W Time)
    (sits : List (Situation W Time)) :
    (liftDoxastic V Time).holdsAt agent (liftProp p) s sits ↔
    V.holdsAt agent p s.world (sits.map (·.world)) := by
  simp only [SitDoxasticPredicate.holdsAt, DoxasticPredicate.holdsAt,
    liftDoxastic, sitVeridicalityHolds_lift, sitBoxAt_lift_eq_boxAt]


-- ════════════════════════════════════════════════════════════════
-- § Properties
-- ════════════════════════════════════════════════════════════════

/-- Veridical situation-dependent predicates entail their complement.

    If x knows p at situation s, then p is true at s. -/
theorem sit_veridical_entails_complement {W Time E : Type*}
    (V : SitDoxasticPredicate W Time E) (hV : V.veridicality = .veridical)
    (agent : E) (p : SitProp W Time) (s : Situation W Time)
    (sits : List (Situation W Time))
    (holds : V.holdsAt agent p s sits) : p s := by
  unfold SitDoxasticPredicate.holdsAt at holds
  rw [hV] at holds
  exact holds.1

/-- Situation-dependent K axiom: closed under known implication.

    If x believes p and x believes (p → q) at situation s,
    then x believes q at s. -/
theorem sit_k_axiom {W Time E : Type*}
    (R : SitAccessRel W Time E) (agent : E)
    (p q : SitProp W Time) (s : Situation W Time)
    (sits : List (Situation W Time))
    (hp : sitBoxAt R agent s sits p)
    (hpq : sitBoxAt R agent s sits (λ s' => p s' → q s')) :
    sitBoxAt R agent s sits q := by
  intro s' hs' hR
  exact hpq s' hs' hR (hp s' hs' hR)


-- ════════════════════════════════════════════════════════════════
-- § Genuinely Temporal Accessibility
-- ════════════════════════════════════════════════════════════════

/-!
### Beyond Lifting: Temporal Accessibility Constraints

The lifting operators (`liftAccess`, `liftProp`) recover classic Hintikka
semantics exactly. But the real power of situation-dependent attitudes comes
from accessibility relations that genuinely constrain the temporal coordinate.

For example, an attitude verb might impose:
- **Temporal binding**: the doxastic alternative's time must match the
  matrix event time: `R agent s s' → s'.time = s.time`
- **Temporal ordering**: doxastic alternatives can only concern times
  at or after the attitude event: `R agent s s' → s'.time ≥ s.time`

These constraints are what make sequence-of-tense work: they tie the
embedded clause's temporal interpretation to the matrix event time.

See `Semantics.Tense.SequenceOfTense` for the formal
connection between these temporal constraints and SOT readings.
-/

/-- Temporal binding constraint: accessible situations share the
    evaluation situation's time. This gives the "simultaneous"
    reading in sequence of tense. -/
def temporallyBound {W Time E : Type*}
    (R : BAgentAccessRel W E) : SitAccessRel W Time E :=
  λ agent s₁ s₂ => R agent s₁.world s₂.world ∧ s₂.time = s₁.time

instance temporallyBound_decidable {W Time E : Type*} [DecidableEq Time]
    (R : BAgentAccessRel W E) [∀ a w w', Decidable (R a w w')] :
    ∀ a s₁ s₂, Decidable (temporallyBound (Time := Time) R a s₁ s₂) := by
  intro a s₁ s₂; unfold temporallyBound; infer_instance

/-- Future-oriented constraint: accessible situations have times
    at or after the evaluation time. This models forward-looking
    attitudes like "expect" or "intend". -/
def futureOriented {W Time E : Type*} [LE Time]
    (R : BAgentAccessRel W E) : SitAccessRel W Time E :=
  λ agent s₁ s₂ => R agent s₁.world s₂.world ∧ s₁.time ≤ s₂.time

instance futureOriented_decidable {W Time E : Type*} [LE Time]
    [DecidableRel (α := Time) (· ≤ ·)]
    (R : BAgentAccessRel W E) [∀ a w w', Decidable (R a w w')] :
    ∀ a s₁ s₂, Decidable (futureOriented (Time := Time) R a s₁ s₂) := by
  intro a s₁ s₂; unfold futureOriented; infer_instance


end Semantics.Attitudes.SituationDependent
