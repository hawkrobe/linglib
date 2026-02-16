import Linglib.Core.Time
import Linglib.Theories.IntensionalSemantics.Attitude.Doxastic

/-!
# Situation-Dependent Attitude Semantics

Attitude operators with temporal parameters: `believe`'s complement type shifts
from `st` (propositions = W → Bool) to `s(it)` (situation-dependent propositions =
Situation W Time → Bool). The doxastic alternatives `Dox_y(w,t)` become world–time
pairs, not just worlds.

## Motivation

Standard attitude semantics evaluates embedded clauses relative to worlds only:
  ⟦x believes p⟧(w) = ∀w' ∈ Dox_x(w). p(w')

This blocks sequence-of-tense (SOT) analysis, where embedded tense receives
a shifted interpretation relative to the matrix event time. Von Stechow (2009)
synthesizes Lewis (1979), Kratzer (1998), and Ogihara (1989): `believe`'s
complement type shifts to s(it), and doxastic alternatives become situation pairs.

## Design

Phase 1 (this module): Additive — new operators alongside existing ones, with
lifting theorems proving generalization. Zero breaking changes.

Phase 2 (future): Migrate `Doxastic.lean` and `Preferential.lean` to use
situation-dependent types natively, with backward-compat wrappers.

## References

- Lewis, D. (1979). Attitudes De Dicto and De Se. *The Philosophical Review* 88.
- Kratzer, A. (1998). More Structural Analogies Between Pronouns and Tenses. *SALT VIII*.
- Ogihara, T. (1989/1996). *Tense, Attitudes, and Scope*. Kluwer.
- Von Stechow, A. (2009). Tenses in compositional semantics. In Klein & Li (eds.),
  *The Expression of Time*, 129–166.
-/

namespace IntensionalSemantics.Attitude.SituationDependent

open Core.Time
open Core.ModalLogic (AgentAccessRel)
open IntensionalSemantics.Attitude.Doxastic
  (Veridicality DoxasticPredicate boxAt veridicalityHolds)


-- ════════════════════════════════════════════════════════════════
-- § Core Types
-- ════════════════════════════════════════════════════════════════

/-- Situation-dependent proposition type (von Stechow's s(it), Bool-valued
    for computational RSA evaluation).

    Where standard propositions are `W → Bool` (sets of worlds),
    situation-dependent propositions are `Situation W Time → Bool`
    (sets of world–time pairs). This is the complement type for
    attitude verbs that support temporal interpretation.

    Note: a Prop-valued counterpart exists at
    `TruthConditional.Sentence.Tense.SitProp` for proof-level
    temporal reasoning. The split follows the `Prop'`/`BProp`
    pattern in `Core/Proposition.lean`. -/
abbrev SitProp (W Time : Type*) := Situation W Time → Bool

/-- Situation-dependent accessibility relation: Dox_y(w,t) = {(w',t') | ...}.

    Generalizes `AgentAccessRel W E = E → W → W → Bool` to include
    temporal coordinates in both the evaluation and accessible situations. -/
abbrev SitAccessRel (W Time E : Type*) := E → Situation W Time → Situation W Time → Bool


-- ════════════════════════════════════════════════════════════════
-- § Modal Operators
-- ════════════════════════════════════════════════════════════════

/-- Situation-dependent universal modal.

    ⟦□p⟧(s) = ∀s' ∈ situations. R(agent, s, s') → p(s')

    Generalizes `Doxastic.boxAt` from worlds to situations. -/
def sitBoxAt {W Time E : Type*} (R : SitAccessRel W Time E) (agent : E)
    (s : Situation W Time) (situations : List (Situation W Time))
    (p : SitProp W Time) : Bool :=
  situations.all λ s' => !R agent s s' || p s'

/-- Situation-dependent existential modal.

    ⟦◇p⟧(s) = ∃s' ∈ situations. R(agent, s, s') ∧ p(s')

    Generalizes `Doxastic.diaAt` from worlds to situations. -/
def sitDiaAt {W Time E : Type*} (R : SitAccessRel W Time E) (agent : E)
    (s : Situation W Time) (situations : List (Situation W Time))
    (p : SitProp W Time) : Bool :=
  situations.any λ s' => R agent s s' && p s'


-- ════════════════════════════════════════════════════════════════
-- § Backward Compatibility: Lifting
-- ════════════════════════════════════════════════════════════════

/-- Lift a world-proposition to a situation-proposition.

    The lifted proposition ignores the temporal coordinate:
    `liftProp p s = p s.world`. This is the backward-compatibility
    embedding for code that hasn't moved to situation types yet. -/
def liftProp {W Time : Type*} (p : W → Bool) : SitProp W Time :=
  λ s => p s.world

/-- Lift a world-accessibility relation to a situation-accessibility relation.

    The lifted relation ignores temporal coordinates in accessibility:
    `liftAccess R agent s₁ s₂ = R agent s₁.world s₂.world`.
    This gives classic Hintikka behavior where doxastic alternatives
    differ only in world, not time. -/
def liftAccess {W Time E : Type*} (R : AgentAccessRel W E) : SitAccessRel W Time E :=
  λ agent s₁ s₂ => R agent s₁.world s₂.world


-- ════════════════════════════════════════════════════════════════
-- § Lifting Theorems
-- ════════════════════════════════════════════════════════════════

/-- KEY THEOREM: Lifted operators recover classic Hintikka semantics.

    `sitBoxAt (liftAccess R) agent s sits (liftProp p)`
    is equivalent to
    `boxAt R agent s.world (sits.map Situation.world) p`.

    This means code using the old world-only operators produces
    identical results when embedded in the situation framework. -/
theorem sitBoxAt_lift_eq_boxAt {W Time E : Type*}
    (R : AgentAccessRel W E) (agent : E) (s : Situation W Time)
    (sits : List (Situation W Time)) (p : W → Bool) :
    sitBoxAt (liftAccess R) agent s sits (liftProp p) =
    boxAt R agent s.world (sits.map Situation.world) p := by
  simp only [sitBoxAt, boxAt, liftAccess, liftProp]
  induction sits with
  | nil => rfl
  | cons s' rest ih => simp only [List.map, List.all_cons, ih]


-- ════════════════════════════════════════════════════════════════
-- § Veridicality for Situations
-- ════════════════════════════════════════════════════════════════

/-- Veridicality check for situation-dependent propositions.

    For veridical predicates (know), requires p(s) = true at the
    evaluation situation. Mirrors `Doxastic.veridicalityHolds`. -/
def sitVeridicalityHolds {W Time : Type*} (v : Veridicality)
    (p : SitProp W Time) (s : Situation W Time) : Bool :=
  match v with
  | .veridical => p s
  | .nonVeridical => true

/-- Lifted veridicality matches world-level veridicality. -/
theorem sitVeridicalityHolds_lift {W Time : Type*} (v : Veridicality)
    (p : W → Bool) (s : Situation W Time) :
    sitVeridicalityHolds v (liftProp p) s = veridicalityHolds v p s.world := by
  cases v <;> rfl


-- ════════════════════════════════════════════════════════════════
-- § Situation-Dependent Doxastic Predicate
-- ════════════════════════════════════════════════════════════════

/-- A situation-dependent doxastic attitude predicate.

    Generalizes `DoxasticPredicate` to use situation-dependent accessibility:
    `Dox_y(w,t) = {(w',t') | ...}` instead of `Dox_y(w) = {w' | ...}`.

    This is von Stechow's (2009) enriched attitude semantics:
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
    (s : Situation W Time) (situations : List (Situation W Time)) : Bool :=
  sitVeridicalityHolds V.veridicality p s && sitBoxAt V.access agent s situations p


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
    equals `V.holdsAt agent p s.world (sits.map .world)`.

    This is the key backward-compatibility theorem: any existing
    analysis using `DoxasticPredicate` can be replayed exactly
    in the situation-dependent framework by lifting. -/
theorem liftDoxastic_holdsAt_eq {W Time E : Type*}
    (V : DoxasticPredicate W E) (agent : E)
    (p : W → Bool) (s : Situation W Time)
    (sits : List (Situation W Time)) :
    (liftDoxastic V Time).holdsAt agent (liftProp p) s sits =
    V.holdsAt agent p s.world (sits.map Situation.world) := by
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
    (holds : V.holdsAt agent p s sits = true) : p s = true := by
  unfold SitDoxasticPredicate.holdsAt at holds
  simp only [hV, sitVeridicalityHolds, Bool.and_eq_true] at holds
  exact holds.1

/-- Situation-dependent K axiom: closed under known implication.

    If x believes p and x believes (p → q) at situation s,
    then x believes q at s. -/
theorem sit_k_axiom {W Time E : Type*}
    (R : SitAccessRel W Time E) (agent : E)
    (p q : SitProp W Time) (s : Situation W Time)
    (sits : List (Situation W Time))
    (hp : sitBoxAt R agent s sits p = true)
    (hpq : sitBoxAt R agent s sits (λ s' => !p s' || q s') = true) :
    sitBoxAt R agent s sits q = true := by
  simp only [sitBoxAt, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at *
  intro s' hs'
  cases hR : R agent s s'
  · left; rfl
  · right
    have h1 := hp s' hs'; simp [hR] at h1
    have h2 := hpq s' hs'; simp [hR, h1] at h2
    exact h2


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

See `TruthConditional.Sentence.Tense.SequenceOfTense` for the formal
connection between these temporal constraints and SOT readings.
-/

/-- Temporal binding constraint: accessible situations share the
    evaluation situation's time. This gives the "simultaneous"
    reading in sequence of tense. -/
def temporallyBound {W Time E : Type*} [DecidableEq Time]
    (R : AgentAccessRel W E) : SitAccessRel W Time E :=
  λ agent s₁ s₂ => R agent s₁.world s₂.world && (s₂.time == s₁.time)

/-- Future-oriented constraint: accessible situations have times
    at or after the evaluation time. This models forward-looking
    attitudes like "expect" or "intend". -/
def futureOriented {W Time E : Type*} [LE Time] [DecidableRel (α := Time) (· ≤ ·)]
    (R : AgentAccessRel W E) : SitAccessRel W Time E :=
  λ agent s₁ s₂ => R agent s₁.world s₂.world && decide (s₁.time ≤ s₂.time)


end IntensionalSemantics.Attitude.SituationDependent
