import Linglib.Semantics.Tense.Domain

/-!
# Tense and Aspect Systems
[declerck-1991] [reichenbach-1947]

Type classes that abstract over specific tense and aspect frameworks.
`TenseSystem α Time Role` says "the type `α` is a way of describing
tense over a `Time` line, using `Role` as its TO vocabulary"; it
commits to (i) how to lift `α` into a `Tense.Domain` and (ii)
which two roles its tense operators target (the *anchor* and
*situation* TOs). `AspectSystem α Time Role` is the analogous
abstraction for the event/reference relation.

These typeclasses do not derive generic `isPast`/`isPerfect`/etc.
predicates — those live concretely on each schema (e.g.
`ReichenbachFrame.isPast`), where the relevant per-paper bridge
theorems (`isPast_iff_relatedByName`) connect them to the Allen
algebra via `Domain.relatedByName`. The typeclass exists to give
schema-generic `toDomain` dispatch and to commit each framework to a
consistent role vocabulary; predicate-level abstraction is left to
the concrete schemas.

The class is parameterized in the mathlib style — the carrier type
is the main parameter; `Time` and `Role` are `outParam`s, so writing
`f : ReichenbachFrame ℤ` lets the elaborator find `Time = ℤ` and
`Role = Orientation` automatically. Instances are unique per
(carrier, Time, Role) triple: there is only one canonical
TenseSystem interpretation per schema type.
-/

open Tense (Domain)

universe u v w

/-! ### Tense System -/

/-- A **tense system**: a framework for locating situations in time
    relative to a discourse anchor.

    Each instance commits to:
    - `toDomain`: how to lift the schema into a `Tense.Domain`
    - `anchor`: the role of the *anchor* TO (the TO that tense locates
      the situation against). For [reichenbach-1947] (extended with
      Kiparsky's P) this is `.perspective`; for [declerck-1991] the
      binding-TO TO₁ also plays this role and is again `.perspective`.
    - `situation`: the role of the *situation* TO. For Reichenbach this
      is `.topic` (= R); for Declerck the situation time TS coincides
      with `.situation` under the universal `TS = TO_sit` principle.

    `Time` and `Role` are `outParam`s: the carrier type `α` (e.g.,
    `ReichenbachFrame ℤ`) determines the time line and the role
    vocabulary, so callers don't pass them explicitly. -/
class TenseSystem (α : Type u)
    (Time : outParam (Type v)) (Role : outParam (Type w))
    [LinearOrder Time] [DecidableEq Role] where
  /-- Lift the schema into a temporal domain. -/
  toDomain : α → Domain Time Role
  /-- The role of the anchor TO. -/
  anchor : Role
  /-- The role of the **located** TO — the TO that tense locates
      relative to the anchor. For Reichenbach this is `.topic` (R);
      for Declerck it is `.situation` (TO_sit). Named `located` rather
      than `situation` because it does *not* generally denote the
      situation time E (`Orientation.situation`): for Reichenbach it
      is R, not E. -/
  located : Role
  /-- Law: the anchor role is present in every lifted domain. (No
      analogous law for `located`: Declercian schemas with an empty
      TO-chain lift to domains whose labels are just
      `[utterance, perspective]`, so the located role can be absent —
      a real asymmetry between the two instances, visible here.) -/
  anchor_mem : ∀ a : α, anchor ∈ (toDomain a).labels

/-! ### Aspect System -/

/-- An **aspect system**: a framework for relating event time to
    reference (situation) time.

    Each instance commits to:
    - `toDomain`: how to lift the schema into a `Tense.Domain`
    - `event`: the role of the event TO (Reichenbach: `.situation` (E);
      Declerck: `.situation` (TS))
    - `reference`: the role of the reference TO (Reichenbach: `.topic`
      (R); Declerck: `.situation` (TS) — Declerck collapses E and R
      both to the situation TO under the universal `TS = TO_sit`
      principle, so `isPerfective` always holds for Declercian schemas
      — the perfect lives in the chain structure, not the E/R relation.) -/
class AspectSystem (α : Type u)
    (Time : outParam (Type v)) (Role : outParam (Type w))
    [LinearOrder Time] [DecidableEq Role] where
  /-- Lift the schema into a temporal domain. -/
  toDomain : α → Domain Time Role
  /-- The role of the event TO. -/
  event : Role
  /-- The role of the reference TO. -/
  reference : Role

/-! ### Generic tense and aspect predicates

Defined once over the classes via `Domain.relatedByName` with Allen
atom-sets, so any tense framework that instantiates `TenseSystem` /
`AspectSystem` gets them for free — and rival frameworks can agree or
disagree about a single predicate instead of each defining its own.
Because `Domain` is interval-native, these are interval-correct;
point-based schemas (Reichenbach) satisfy them in the degenerate
point-collapse of the Allen algebra (see the `ReichenbachFrame`
specialization lemmas), and `isImperfective` is *unsatisfiable* there
(`ReichenbachFrame.not_aspectSystem_isImperfective`). -/

namespace TenseSystem

variable {α : Type u} {Time : Type v} {Role : Type w}
  [LinearOrder Time] [DecidableEq Role] [TenseSystem α Time Role]

/-- Generic PAST: the located TO precedes the anchor TO. -/
def isPast (a : α) : Prop :=
  (toDomain a).relatedByName AllenRelation.precedesSet
    (located (α := α)) (anchor (α := α))

/-- Generic PRESENT: the located TO equals the anchor TO. (Point
    approximation of present-as-overlap; an interval instance wanting
    overlap semantics should use `AllenRelation.overlapSet` directly.) -/
def isPresent (a : α) : Prop :=
  (toDomain a).relatedByName AllenRelation.equalSet
    (located (α := α)) (anchor (α := α))

/-- Generic FUTURE: the anchor TO precedes the located TO. -/
def isFuture (a : α) : Prop :=
  (toDomain a).relatedByName AllenRelation.precedesSet
    (anchor (α := α)) (located (α := α))

end TenseSystem

namespace AspectSystem

variable {α : Type u} {Time : Type v} {Role : Type w}
  [LinearOrder Time] [DecidableEq Role] [AspectSystem α Time Role]

/-- Generic PERFECT: the event TO precedes the reference TO. -/
def isPerfect (a : α) : Prop :=
  (toDomain a).relatedByName AllenRelation.precedesSet
    (event (α := α)) (reference (α := α))

/-- Generic PERFECTIVE: the event TO equals the reference TO
    (point approximation of E ⊆ R). -/
def isPerfective (a : α) : Prop :=
  (toDomain a).relatedByName AllenRelation.equalSet
    (event (α := α)) (reference (α := α))

/-- Generic PROSPECTIVE: the reference TO precedes the event TO. -/
def isProspective (a : α) : Prop :=
  (toDomain a).relatedByName AllenRelation.precedesSet
    (reference (α := α)) (event (α := α))

/-- Generic IMPERFECTIVE ([klein-1994]): the reference TO (topic time)
    is properly contained in the event TO (situation time) — TT ⊂ TSit.
    Genuinely interval-level: unsatisfiable when both TOs are points
    (`TO.not_pure_properContainment`), which is the formal statement of
    why point-based frames cannot represent the imperfective. -/
def isImperfective (a : α) : Prop :=
  (toDomain a).relatedByName AllenRelation.properContainmentSet
    (reference (α := α)) (event (α := α))

end AspectSystem
