import Linglib.Theories.Semantics.Events.Mereology

/-!
# Thematic-Role Properties on θ
@cite{krifka-1998} @cite{dowty-1991} @cite{tenny-1994} @cite{carlson-1984}

The mereological properties a thematic relation θ : Object → Event → Prop
can have. These properties — uniqueness of participants/events,
cumulativity, mapping to objects/events/strict-sub-objects/strict-sub-events
— are the foundation of mereological event semantics. Each property
formalizes a structural correspondence between the part-mereology of
objects and the part-mereology of events under a thematic role.

Topic-named (not paper-named): defines the deep substrate that
@cite{krifka-1998} §3.2 (eq. 43-50) develops, but also the substrate
that @cite{dowty-1991} proto-roles, @cite{tenny-1994} aspectual roles,
@cite{carlson-1984} thematic-role-as-relation theory, and any modern
incremental-theme account uses. Specific paper replications import
this file and instantiate the predicates on paper-specific data.

## Sections

1. UP (uniqueness of participants, eq. 43)
2. CumTheta (cumulativity for θ, eq. 44)
3. ME / MSE (mapping to events / strict subevents, eq. 45/46)
4. UE (uniqueness of events, eq. 47)
5. MO / MSO (mapping to objects / strict subobjects, eq. 48/49)
6. UO (uniqueness of objects, eq. 50)
7. GUE (general uniqueness of events, eq. 52)

-/

namespace Semantics.Events.ThematicRoleProperties

open Mereology

variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

/-- Uniqueness of Participant (UP): each event has at most one θ-filler.
    @cite{krifka-1998} eq. 43: θ(x,e) ∧ θ(y,e) → x = y. -/
def UP (θ : α → β → Prop) : Prop :=
  ∀ (x y : α) (e : β), θ x e → θ y e → x = y

/-- Cumulative theta (CumTheta): θ preserves sums.
    @cite{krifka-1998} eq. 44: θ(x,e) ∧ θ(y,e') → θ(x⊕y, e⊕e').
    This is the relational analog of `IsSumHom`. -/
def CumTheta (θ : α → β → Prop) : Prop :=
  ∀ (x y : α) (e e' : β), θ x e → θ y e' → θ (x ⊔ y) (e ⊔ e')

/-- Mapping to Events (ME): object parts map to event parts.
    @cite{krifka-1998} eq. 45: θ(x,e) ∧ y ≤ x → ∃e'. e' ≤ e ∧ θ(y,e'). -/
def ME (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (y : α), θ x e → y ≤ x → ∃ e', e' ≤ e ∧ θ y e'

/-- Mapping to Strict subEvents (MSE): proper object parts map to proper subevents.
    @cite{krifka-1998} eq. 46: θ(x,e) ∧ y < x → ∃e'. e' < e ∧ θ(y,e'). -/
def MSE (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (y : α), θ x e → y < x → ∃ e', e' < e ∧ θ y e'

/-- Uniqueness of Events (UE): each object part maps to a unique event part.
    @cite{krifka-1998} eq. 47: θ(x,e) ∧ y ≤ x → ∃!e'. e' ≤ e ∧ θ(y,e'). -/
def UE (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (y : α), θ x e → y ≤ x →
    ∃ e', e' ≤ e ∧ θ y e' ∧ ∀ e'', e'' ≤ e → θ y e'' → e'' = e'

/-- Mapping to Objects (MO): event parts map to object parts.
    @cite{krifka-1998} eq. 48: θ(x,e) ∧ e' ≤ e → ∃y. y ≤ x ∧ θ(y,e'). -/
def MO (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (e' : β), θ x e → e' ≤ e → ∃ y, y ≤ x ∧ θ y e'

/-- Mapping to Strict subObjects (MSO): proper subevents map to proper object parts.
    @cite{krifka-1998} eq. 49: θ(x,e) ∧ e' < e → ∃y. y < x ∧ θ(y,e'). -/
def MSO (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (e' : β), θ x e → e' < e → ∃ y, y < x ∧ θ y e'

/-- Uniqueness of Objects (UO): each event part maps to a unique object part.
    @cite{krifka-1998} eq. 50: θ(x,e) ∧ e' ≤ e → ∃!y. y ≤ x ∧ θ(y,e'). -/
def UO (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e : β) (e' : β), θ x e → e' ≤ e →
    ∃ y, y ≤ x ∧ θ y e' ∧ ∀ z, z ≤ x → θ z e' → z = y

/-- Generalized Uniqueness of Events (GUE): each object participates in
    at most one event.
    @cite{krifka-1998} eq. 52: θ(x,e) ∧ θ(x,e') → e = e'. -/
def GUE (θ : α → β → Prop) : Prop :=
  ∀ (x : α) (e e' : β), θ x e → θ x e' → e = e'

/-- Bridge: a sum-homomorphism `f : β → α` (functional θ from
    `Mereology.lean`) induces a `CumTheta` relation `λ x e, f e = x`.
    This connects the functional view (θ as projection function) to
    the relational view (θ as binary predicate) at the cumulativity
    level. -/
theorem roleHom_implies_cumTheta
    {f : β → α} (hf : IsSumHom f) :
    CumTheta (fun (x : α) (e : β) => f e = x) := by
  intro x y e e' hx hy
  rw [← hx, ← hy]
  exact hf.map_sup e e'

-- ════════════════════════════════════════════════════
-- § 8. IsCumThetaVerb — typeclass for cumulative-θ verbs
-- ════════════════════════════════════════════════════

/-- A thematic relation θ has *cumulative theta* (mathlib-discipline
    typeclass form of `CumTheta` for synthesis).

    The weakest verb-class typeclass: every K98 verb class
    (strictly incremental, incremental, cumulative-only) satisfies
    `CumTheta` and hence `IsCumThetaVerb`. The stronger classes
    (`IsSincVerb` in `StrictIncrementality.lean`, `IsIncVerb` in
    `GeneralIncrementality.lean`) register upward instances providing
    `IsCumThetaVerb` automatically.

    Note: this typeclass is content-driven — its only field is
    `CumTheta`, satisfied by ALL K98 verb classes. The "cumOnly"
    empirical class (cumulative *and* non-incremental) is a
    separate sub-classification not captured here; per @cite{krifka-1998}
    §3.2 (page 12-13), *push (the cart)*, *pull*, *carry* — transitive
    activities with theme arguments where mereological structure does
    NOT transfer to events. K98 does not classify stative experiencer
    verbs (*love*, *know*) under CumTheta; statives are treated
    separately (page 13: *see the picture*, *touch a cup* are
    "peculiar" cases violating UP). -/
class IsCumThetaVerb (θ : α → β → Prop) : Prop where
  /-- Cumulative theta: θ preserves sums (K98 eq. 44). -/
  cumTheta : CumTheta θ

end Semantics.Events.ThematicRoleProperties
