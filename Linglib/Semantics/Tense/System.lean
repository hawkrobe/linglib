import Linglib.Semantics.Tense.Domain

/-!
# Tense and Aspect Systems
[declerck-1991] [reichenbach-1947]

Type classes that abstract over specific tense and aspect frameworks.
`TenseSystem α Time Role` says "the type `α` is a way of describing
tense over a `Time` line, using `Role` as its TO vocabulary"; it
commits to (i) how to lift `α` into a `Semantics.Tense.Domain` and (ii)
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

namespace Semantics.Tense

universe u v w

/-! ### Tense System -/

/-- A **tense system**: a framework for locating situations in time
    relative to a discourse anchor.

    Each instance commits to:
    - `toDomain`: how to lift the schema into a `Semantics.Tense.Domain`
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
  /-- The role of the situation TO. -/
  situation : Role

/-! ### Aspect System -/

/-- An **aspect system**: a framework for relating event time to
    reference (situation) time.

    Each instance commits to:
    - `toDomain`: how to lift the schema into a `Semantics.Tense.Domain`
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

end Semantics.Tense
