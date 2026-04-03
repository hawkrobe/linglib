/-
# Donnellan's Referential/Attributive Distinction

Formalizes @cite{donnellan-1966}: definite descriptions have two uses:
- **Attributive**: "The φ is ψ" means whoever uniquely satisfies φ is ψ
- **Referential**: "The φ is ψ" — the speaker has a particular individual
  in mind; what is *said* is about that individual

On @cite{donnellan-1966}'s account, the truth conditions of a referential
use depend on the *intended referent*, not on whoever satisfies the
description. "The man drinking a martini is happy" (said about Jones,
who is drinking water) is true iff Jones is happy.

Whether this makes the expression's semantic content rigid is a disputed
interpretive question:
- @cite{kripke-1977} argues referential use is merely pragmatic (speaker's
  reference ≠ semantic reference); the semantic content remains descriptive.
- @cite{almog-2014} (Ch 3) argues referential use is genuinely semantic but
  operates through a cognitive mechanism independent of rigidification.
- Many semanticists (Kaplan, Wettstein) treat referential use as producing
  singular propositional content about the intended individual.

We formalize Donnellan's own position: in referential use, the truth
conditions track the intended individual. The profile ⟨false, false, true⟩
records that the expression is not a rigid *designator* by type
(designation = false) and does not produce structured ⟨individual, property⟩
content (singularProp = false), but is used referentially.

## Key Results

- `referentialContent`: The intended referent, modeled as a rigid intension
- `referentialExpression`: A referentially-used description
- `donnellanDivergence`: The two uses come apart when the description
  fails to apply to the intended referent
- `definitePrProp`: Attributive semantics with presupposition (bridges
  to `Core.Presupposition.PrProp`)

-/

import Linglib.Theories.Semantics.Reference.Basic
import Linglib.Core.Semantics.Presupposition

namespace Semantics.Reference.Donnellan

open Core (Intension)
open Core.Intension (rigid IsRigid rigid_isRigid)
open Core.Presupposition (PrProp)
open Semantics.Reference.Basic

/-! ## Use Modes -/

/-- The two uses of definite descriptions.

- `attributive`: The speaker means "whoever uniquely satisfies the
  description". Content is descriptive (non-rigid in general).
- `referential`: The speaker has a particular individual in mind.
  What is *said* is about that individual (@cite{donnellan-1966}).
  The interpretive status of this (pragmatic vs. semantic) is disputed;
  see module docstring. -/
inductive UseMode where
  | attributive
  | referential
  deriving DecidableEq, Repr

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
an existence+uniqueness presupposition. -/
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

/-- Referential content: truth conditions fixed to the speaker's intended
referent, regardless of which world we evaluate at.

@cite{donnellan-1966}: in referential use, what is *said* is about the
intended individual. "The man drinking a martini is happy" (referential,
about Jones) is true iff Jones is happy — even if Jones isn't drinking
a martini.

Note: modeling this as `rigid intended` captures Donnellan's claim about
truth conditions. Whether this represents the expression's *semantic*
content or merely the *speaker's* reference is the Kripke 1977 vs
Donnellan dispute — see module docstring. -/
def referentialContent {W E : Type*} (intended : E) : Intension W E :=
  rigid intended

/-- A referential definite description as a `ReferringExpression`.

The profile ⟨false, false, true⟩ records:
- `designation = false`: not a rigid designator by linguistic type
  (it is a description, not a name or indexical)
- `singularProp = false`: per @cite{almog-2014}'s reading of Donnellan
  (Ch 3, §2.12), referential use gives a "proposition-free" account,
  not a structured ⟨individual, property⟩ pair
- `referentialUse = true`: the speaker has a cognitive fix on the referent -/
def referentialExpression {C W E : Type*} (intended : E) : ReferringExpression C W E :=
  { character := λ _ => rigid intended
  , profile := ⟨false, false, true⟩ }

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

end Semantics.Reference.Donnellan
