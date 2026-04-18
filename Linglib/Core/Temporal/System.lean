import Linglib.Core.Temporal.Domain

/-!
# Tense and Aspect Systems
@cite{declerck-1991} @cite{reichenbach-1947}

Type classes that abstract over specific tense and aspect frameworks.
`TenseSystem α Time Role` says "the type `α` is a way of describing
tense over a `Time` line, using `Role` as its TO vocabulary"; it
commits to (i) how to lift `α` into a `Core.Time.Domain` and (ii)
which two roles its tense operators target (the *anchor* and
*situation* TOs). `AspectSystem α Time Role` is the analogous
abstraction for the event/reference relation.

The generic predicates `TenseSystem.isPast`, `AspectSystem.isPerfect`,
etc. are then *derived* — phrased as `Domain.relatedByName` queries
against named atom-sets from the Allen algebra. The same predicates
work uniformly across systems; what's specific to each system is the
choice of roles.

The class is parameterized in the mathlib style — the carrier type
is the main parameter; `Time` and `Role` are `outParam`s, so writing
`f : ReichenbachFrame ℤ` lets the elaborator find `Time = ℤ` and
`Role = OrientationTime` automatically. Instances are unique per
(carrier, Time, Role) triple: there is only one canonical
TenseSystem interpretation per schema type.
-/

namespace Core.Time

universe u v

-- ════════════════════════════════════════════════════
-- § Tense System
-- ════════════════════════════════════════════════════

/-- A **tense system**: a framework for locating situations in time
    relative to a discourse anchor.

    Each instance commits to:
    - `toDomain`: how to lift the schema into a `Core.Time.Domain`
    - `anchor`: the role of the *anchor* TO (the TO that tense locates
      the situation against). For @cite{reichenbach-1947} (extended with
      Kiparsky's P) this is `.perspective`; for @cite{declerck-1991} the
      binding-TO TO₁ also plays this role and is again `.perspective`.
    - `situation`: the role of the *situation* TO. For Reichenbach this
      is `.topic` (= R); for Declerck the situation time TS coincides
      with `.situation` under the universal `TS = TO_sit` principle.

    `Time` and `Role` are `outParam`s: the carrier type `α` (e.g.,
    `ReichenbachFrame ℤ`) determines the time line and the role
    vocabulary, so callers don't pass them explicitly. -/
class TenseSystem (α : Type u)
    (Time : outParam (Type u)) (Role : outParam (Type v))
    [LinearOrder Time] [DecidableEq Role] where
  /-- Lift the schema into a temporal domain. -/
  toDomain : α → Domain Time Role
  /-- The role of the anchor TO. -/
  anchor : Role
  /-- The role of the situation TO. -/
  situation : Role

namespace TenseSystem

variable {α : Type u} {Time : Type u} {Role : Type v}
  [LinearOrder Time] [DecidableEq Role] [TenseSystem α Time Role]

/-- Generic PAST: situation-TO precedes anchor-TO in the Allen algebra.
    Reduces to `f.referenceTime < f.perspectiveTime` for Reichenbach
    via the predicate-bridge theorems. -/
def isPast (s : α) : Prop :=
  (toDomain s).relatedByName AllenRelation.precedesSet
    (situation α) (anchor α)

/-- Generic PRESENT: situation-TO equals anchor-TO. -/
def isPresent (s : α) : Prop :=
  (toDomain s).relatedByName AllenRelation.equalSet
    (situation α) (anchor α)

/-- Generic FUTURE: anchor-TO precedes situation-TO. -/
def isFuture (s : α) : Prop :=
  (toDomain s).relatedByName AllenRelation.precedesSet
    (anchor α) (situation α)

end TenseSystem

-- ════════════════════════════════════════════════════
-- § Aspect System
-- ════════════════════════════════════════════════════

/-- An **aspect system**: a framework for relating event time to
    reference (situation) time.

    Each instance commits to:
    - `toDomain`: how to lift the schema into a `Core.Time.Domain`
    - `event`: the role of the event TO (Reichenbach: `.situation` (E);
      Declerck: `.situation` (TS))
    - `reference`: the role of the reference TO (Reichenbach: `.topic`
      (R); Declerck: `.situation` (TS) — Declerck collapses E and R
      both to the situation TO under the universal `TS = TO_sit`
      principle, so `isPerfective` always holds for Declercian schemas
      — the perfect lives in the chain structure, not the E/R relation.) -/
class AspectSystem (α : Type u)
    (Time : outParam (Type u)) (Role : outParam (Type v))
    [LinearOrder Time] [DecidableEq Role] where
  /-- Lift the schema into a temporal domain. -/
  toDomain : α → Domain Time Role
  /-- The role of the event TO. -/
  event : Role
  /-- The role of the reference TO. -/
  reference : Role

namespace AspectSystem

variable {α : Type u} {Time : Type u} {Role : Type v}
  [LinearOrder Time] [DecidableEq Role] [AspectSystem α Time Role]

/-- Generic PERFECTIVE: event-TO equals reference-TO. -/
def isPerfective (s : α) : Prop :=
  (toDomain s).relatedByName AllenRelation.equalSet
    (event α) (reference α)

/-- Generic PERFECT: event-TO precedes reference-TO. -/
def isPerfect (s : α) : Prop :=
  (toDomain s).relatedByName AllenRelation.precedesSet
    (event α) (reference α)

/-- Generic PROSPECTIVE: reference-TO precedes event-TO. -/
def isProspective (s : α) : Prop :=
  (toDomain s).relatedByName AllenRelation.precedesSet
    (reference α) (event α)

end AspectSystem

end Core.Time
