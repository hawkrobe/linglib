/-
# Donnellan's Referential/Attributive Distinction

Formalizes [donnellan-1966]: definite descriptions have two uses:
- **Attributive**: "The φ is ψ" means whoever uniquely satisfies φ is ψ
- **Referential**: "The φ is ψ" — the speaker has a particular individual
  in mind; what is *said* is about that individual

On [donnellan-1966]'s account, the truth conditions of a referential
use depend on the *intended referent*, not on whoever satisfies the
description. "The man drinking a martini is happy" (said about Jones,
who is drinking water) is true iff Jones is happy.

Whether this makes the expression's semantic content rigid is a disputed
interpretive question:
- [kripke-1977] argues referential use is merely pragmatic (speaker's
  reference ≠ semantic reference); the semantic content remains descriptive.
- [almog-2014] (Ch 3) argues referential use is genuinely semantic but
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
- `definiteNominal`: Attributive semantics as a `NominalDenot` (selector =
  the Russellian iota; `resolve` it for a `PrProp`)

-/

import Linglib.Semantics.Reference.Basic
import Linglib.Semantics.Reference.Nominal
import Linglib.Semantics.Presupposition.Basic
import Linglib.Core.Nominal.Maximality

namespace Semantics.Reference.Donnellan

open Core (Intension)
open Core.Intension (rigid IsRigid rigid_isRigid)
open Semantics.Presupposition (PrProp)
open Semantics.Presupposition.PrProp (presupOfReferent)
open Semantics.Reference.Basic
open Core.Nominal (russellIotaList)

/-! ## Use Modes -/

/-- The two uses of definite descriptions.

- `attributive`: The speaker means "whoever uniquely satisfies the
  description". Content is descriptive (non-rigid in general).
- `referential`: The speaker has a particular individual in mind.
  What is *said* is about that individual ([donnellan-1966]).
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
entity satisfying φ at w — the canonical iota `russellIotaList` applied
pointwise. The referent can vary across worlds. -/
def attributiveContent {W E : Type*} (domain : List E) (restrictor : E → W → Bool)
    : W → Option E :=
  fun w => russellIotaList domain (fun e => restrictor e w)

/-- The definite description as a `NominalDenot`: the selector is the
Russellian iota (`attributiveContent`); there is no intrinsic presupposition
beyond definedness of that selector.

This is the single source of truth for definite descriptions in the library;
familiarity-based, anaphoric, and discourse-restricted variants are
`NominalDenot`s with different selectors, and pronouns add a φ-feature presup
(see `PersonalPronoun.denote`). -/
def definiteNominal {W E : Type*} (domain : List E) (restrictor : E → W → Bool) :
    NominalDenot Unit W E :=
  NominalDenot.ofReferent (attributiveContent domain restrictor)

/-! ## Referential Semantics -/

/-- Referential content: truth conditions fixed to the speaker's intended
referent, regardless of which world we evaluate at.

[donnellan-1966]: in referential use, what is *said* is about the
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
- `singularProp = false`: per [almog-2014]'s reading of Donnellan
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

/-- `attributiveContent` is the canonical Russellian iota `russellIotaList`
applied pointwise: "the φ" picks, at each world `w`, the unique `e` in the
domain with `restrictor e w = true`. -/
theorem attributive_is_pointwise_iota {W E : Type*} (domain : List E)
    (restrictor : E → W → Bool) (w : W) :
    attributiveContent domain restrictor w =
    russellIotaList domain (fun e => restrictor e w) := rfl

end Semantics.Reference.Donnellan
