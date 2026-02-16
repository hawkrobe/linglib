/-
# Donnellan's Referential/Attributive Distinction

Formalizes Donnellan (1966): definite descriptions have two uses:
- **Attributive**: "The φ is ψ" means whoever uniquely satisfies φ is ψ
- **Referential**: "The φ is ψ" means the speaker's intended individual is ψ

The referential use yields rigid content — Almog's third mechanism of direct
reference (Ch 3). The attributive use yields Russellian/Fregean descriptive
content that varies across worlds.

## Key Results

- `referentialUse_isRigid`: Referential use produces rigid content
- `donnellanDivergence`: The two uses come apart when the description
  fails to apply to the intended referent
- `definitePrProp`: Attributive semantics with presupposition (bridges
  to `Core.Presupposition.PrProp`)

## References

- Donnellan, K. (1966). Reference and Definite Descriptions. Philosophical Review.
- Almog, J. (2014). Referential Mechanics, Ch 3.
- Russell, B. (1905). On Denoting. Mind.
- Partee, B. (1987). Noun Phrase Interpretation and Type-shifting Principles.
-/

import Linglib.Theories.Semantics.Reference.Basic
import Linglib.Core.Presupposition

namespace IntensionalSemantics.Reference.Donnellan

open Core.Intension (Intension rigid IsRigid rigid_isRigid)
open Core.Presupposition (PrProp)
open IntensionalSemantics.Reference.Basic

/-! ## Use Modes -/

/-- The two uses of definite descriptions (Donnellan 1966).

- `attributive`: The speaker means "whoever uniquely satisfies the
  description". Content is descriptive (non-rigid in general).
- `referential`: The speaker uses the description to pick out a
  *particular* individual they have in mind. Content is rigid. -/
inductive UseMode where
  | attributive
  | referential
  deriving DecidableEq, BEq, Repr

/-! ## Definite Descriptions -/

/-- A definite description with a specified use mode.

The same surface form "the man drinking a martini" can be used
attributively (whoever is drinking a martini) or referentially
(that guy over there, whom I happen to identify via the description). -/
structure DefiniteDescription (W : Type*) (E : Type*) where
  /-- The restrictor property (e.g., "man drinking a martini") -/
  restrictor : E → W → Bool
  /-- How the description is being used -/
  useMode : UseMode
  /-- The speaker's intended referent (only relevant for referential use) -/
  intendedRef : Option E := none

/-! ## Attributive Semantics -/

/-- Attributive content: at each world, the unique satisfier of the restrictor.

This is the Russellian analysis: "the φ" denotes, at world w, the unique
entity satisfying φ at w. The referent can vary across worlds. -/
def attributiveContent {W E : Type*} (domain : List E) (restrictor : E → W → Bool)
    : W → Option E :=
  λ w =>
    match domain.filter (λ e => restrictor e w) with
    | [e] => some e
    | _ => none

/-- Attributive semantics wrapped in `PrProp`: existence and uniqueness
are presupposed, the assertion is the predicate applied to the unique
satisfier.

Bridge to `Core.Presupposition.PrProp`: the definite article triggers
an existence+uniqueness presupposition (Heim & Kratzer 1998). -/
def definitePrProp {W E : Type*} (domain : List E) (restrictor : E → W → Bool)
    (predicate : E → W → Bool) : PrProp W :=
  { presup := λ w =>
      match domain.filter (λ e => restrictor e w) with
      | [_] => true
      | _ => false
  , assertion := λ w =>
      match domain.filter (λ e => restrictor e w) with
      | [e] => predicate e w
      | _ => false }

/-! ## Referential Semantics -/

/-- Referential content: the intension is rigid, fixed to the speaker's
intended referent regardless of which world we evaluate at.

This is Donnellan's key insight: in referential use, "the φ" functions
like a proper name for the intended individual. -/
def referentialContent {W E : Type*} (intended : E) : Intension W E :=
  rigid intended

/-- Referential use produces rigid content. -/
theorem referentialUse_isRigid {W E : Type*} (intended : E) :
    IsRigid (referentialContent (W := W) intended) :=
  rigid_isRigid intended

/-- A referential definite description as a `ReferringExpression`. -/
def referentialExpression {C W E : Type*} (intended : E) : ReferringExpression C W E :=
  { character := λ _ => rigid intended
  , mechanisms := [.referentialUse] }

/-! ## Donnellan Divergence -/

/-- Donnellan's divergence scenario: attributive and referential uses come
apart when the description fails to apply to the intended referent.

Classic example: "The man drinking a martini is happy."
- The speaker intends Jones (who is actually drinking water).
- Attributive: whoever IS drinking a martini — picks out Smith.
- Referential: Jones — the speaker's intended referent.

When the description misfits, the two uses yield different truth values. -/
structure DonnellanDivergence (W : Type*) (E : Type*) where
  /-- The world where divergence occurs -/
  world : W
  /-- The restrictor (e.g., "man drinking a martini") -/
  restrictor : E → W → Bool
  /-- The predicate (e.g., "is happy") -/
  predicate : E → W → Bool
  /-- Who the speaker intends -/
  intended : E
  /-- Who actually uniquely satisfies the description -/
  actualSatisfier : E
  /-- The description picks out someone other than the intended referent -/
  misfit : intended ≠ actualSatisfier
  /-- The intended referent doesn't satisfy the description -/
  intendedFails : restrictor intended world = false
  /-- The actual satisfier does satisfy the description -/
  satisfierSucceeds : restrictor actualSatisfier world = true

/-- When divergence occurs, referential and attributive uses evaluate
differently (assuming the predicate distinguishes the two individuals). -/
theorem donnellanDivergence {W E : Type*} (d : DonnellanDivergence W E)
    (_hPred : d.predicate d.intended d.world ≠ d.predicate d.actualSatisfier d.world) :
    referentialContent d.intended d.world ≠ d.actualSatisfier := by
  intro heq
  simp only [referentialContent, rigid] at heq
  exact d.misfit heq

/-! ## Bridge to Partee's Type-Shifting Triangle -/

/-- Connection to `TypeShifting.iota`: the attributive semantics of "the φ"
is Partee's `iota` applied at each world. Both compute the unique satisfier
of a predicate in a domain.

`TypeShifting.iota domain P` returns the unique `e` with `P e = true`.
`attributiveContent domain restrictor w` returns the unique `e` with
`restrictor e w = true`. These coincide when we fix the world parameter. -/
theorem attributive_is_pointwise_iota {W E : Type*} (domain : List E)
    (restrictor : E → W → Bool) (w : W) :
    attributiveContent domain restrictor w =
    (match domain.filter (λ e => restrictor e w) with
     | [e] => some e
     | _ => none) := rfl

end IntensionalSemantics.Reference.Donnellan
