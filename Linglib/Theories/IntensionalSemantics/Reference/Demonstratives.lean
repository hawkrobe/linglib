/-
# True Demonstratives and Demonstrations

Kaplan (1989) "Demonstratives" §IX, XV, XVI: the theory of true
demonstratives ("that", "this") as opposed to pure indexicals ("I", "now").

True demonstratives require a *demonstration* — an act of pointing, directing
attention, etc. — to complete their character. Without a demonstration, a
demonstrative has no content.

## Key Results

- `Demonstration`: manner of presentation (demonstrating act → demonstratum)
- `TrueDemonstrative`: bundles demonstration + optional sortal restriction
- `demo_directlyReferential`: Principle 2 — complete demonstratives are
  directly referential
- `demo_character_varies`: different demonstrations → different contents
- `DemoFregePuzzle`: "that [Hes] = that [Phos]" informative because
  demonstrations differ

## References

- Kaplan, D. (1989). Demonstratives, §IX, XV, XVI.
-/

import Linglib.Core.Context
import Linglib.Theories.IntensionalSemantics.Reference.Basic
import Linglib.Theories.IntensionalSemantics.Reference.KaplanLD

namespace IntensionalSemantics.Reference.Demonstratives

open Core.Intension (Intension rigid IsRigid rigid_isRigid)
open Core.Context (KContext)
open IntensionalSemantics.Reference.Basic (ReferringExpression isDirectlyReferential
  RefMechanism)

/-! ## Demonstrations -/

/-- A demonstration: an act that presents an individual in a context.

Kaplan (1989) §IX: "A demonstration is, roughly, a visual presentation of
a local object discriminated by a pointing." The demonstration provides the
*manner of presentation* — different demonstrations of the same object
constitute different modes of presentation. -/
structure Demonstration (C : Type*) (E : Type*) where
  /-- Given a context, yield the demonstrated object (if any). -/
  demonstratum : C → Option E
  /-- Description of the manner of presentation (for documentation). -/
  description : String

/-- A demonstration succeeds in context c if it yields a demonstratum. -/
def Demonstration.succeeds {C E : Type*} (d : Demonstration C E) (c : C) : Prop :=
  d.demonstratum c ≠ none

/-- A vacuous demonstration: always fails (hallucination, empty pointing). -/
def vacuousDemonstration {C E : Type*} : Demonstration C E :=
  ⟨λ _ => none, "vacuous"⟩

/-- A constant demonstration: always yields the same individual. -/
def constantDemonstration {C E : Type*} (e : E) (desc : String) : Demonstration C E :=
  ⟨λ _ => some e, desc⟩

/-! ## True Demonstratives -/

/-- A true demonstrative: a demonstrative expression completed by a demonstration.

Kaplan (1989) §XV: "that [pointing at Venus in the evening] is bright."
The demonstration completes the character; without it, "that" is incomplete. -/
structure TrueDemonstrative (C : Type*) (W : Type*) (E : Type*) where
  /-- The associated demonstration -/
  demonstration : Demonstration C E
  /-- Optional sortal restriction (e.g., "that *planet*") -/
  sortal : Option (E → W → Bool) := none

/-- The character of a true demonstrative: in each context, rigidly designate
the demonstratum (if the demonstration succeeds).

If the demonstration fails, the content is a trivially rigid intension
returning a default entity. -/
def TrueDemonstrative.character {C W E : Type*} [Inhabited E]
    (td : TrueDemonstrative C W E) : C → Intension W E :=
  λ c => match td.demonstration.demonstratum c with
    | some e => rigid e
    | none   => rigid default

/-- Principle 2 (Kaplan 1989 §XVI): Complete demonstratives are directly
referential — at every context, their content is rigid. -/
theorem demo_directlyReferential {C W E : Type*} [Inhabited E]
    (td : TrueDemonstrative C W E) :
    isDirectlyReferential td.character := by
  intro c
  simp only [TrueDemonstrative.character]
  cases td.demonstration.demonstratum c with
  | none   => exact rigid_isRigid default
  | some e => exact rigid_isRigid e

/-- Different demonstrations in different contexts yield different contents.

If the demonstratum differs between two contexts, the contents differ. -/
theorem demo_character_varies {C W E : Type*} [Inhabited E] [Inhabited W]
    (td : TrueDemonstrative C W E)
    (c₁ c₂ : C) (e₁ e₂ : E)
    (h₁ : td.demonstration.demonstratum c₁ = some e₁)
    (h₂ : td.demonstration.demonstratum c₂ = some e₂)
    (hne : e₁ ≠ e₂) :
    td.character c₁ ≠ td.character c₂ := by
  intro heq
  simp only [TrueDemonstrative.character, h₁, h₂] at heq
  have : rigid (W := W) e₁ default = rigid (W := W) e₂ default :=
    congrFun heq default
  simp only [rigid] at this
  exact hne this

/-! ## Demonstrative Frege Puzzle (§IX.ii-iv) -/

/-- The Demonstrative Frege Puzzle: "that [Hes] = that [Phos]" is informative
even though both demonstrations pick out the same object (Venus).

The two demonstrations constitute different manners of presentation.
The identity is informative because the *characters* differ (different
demonstrations), even though the *contents* coincide. -/
structure DemoFregePuzzle (C : Type*) (W : Type*) (E : Type*) where
  /-- First demonstrative (e.g., "that" + pointing at evening star) -/
  demo₁ : TrueDemonstrative C W E
  /-- Second demonstrative (e.g., "that" + pointing at morning star) -/
  demo₂ : TrueDemonstrative C W E
  /-- The shared demonstratum (Venus) -/
  sharedObject : E
  /-- Context in which both demonstrations succeed with the same object -/
  context : C
  /-- First demonstration yields the shared object -/
  demo₁_yields : demo₁.demonstration.demonstratum context = some sharedObject
  /-- Second demonstration yields the shared object -/
  demo₂_yields : demo₂.demonstration.demonstratum context = some sharedObject
  /-- The demonstrations themselves differ (different descriptions) -/
  demonstrations_differ : demo₁.demonstration.description ≠ demo₂.demonstration.description

/-- In a Frege puzzle configuration, the contents coincide: both demos
yield the same rigid intension at the shared context. -/
theorem fregePuzzle_same_content {C W E : Type*} [Inhabited E]
    (fp : DemoFregePuzzle C W E) :
    fp.demo₁.character fp.context = fp.demo₂.character fp.context := by
  simp only [TrueDemonstrative.character, fp.demo₁_yields, fp.demo₂_yields]

/-! ## Bridges -/

/-- Wrap a TrueDemonstrative as a ReferringExpression for integration with
the `Reference/Basic.lean` types. -/
def TrueDemonstrative.toReferringExpression {C W E : Type*} [Inhabited E]
    (td : TrueDemonstrative C W E) : ReferringExpression C W E :=
  { character := td.character
  , mechanisms := [.designation, .singularProp, .referentialUse] }

/-!
### Bridge to RSA Reference Games

Demonstrations connect to RSA reference games:
- A demonstration is analogous to a pointing gesture in a reference game
- L0 (literal listener) ≈ attributive interpretation (resolves via description)
- S1 (pragmatic speaker) ≈ referential interpretation (chooses expression
  to single out the intended referent)

The full formalization of this bridge lives in `RSA/Domains/ReferenceGames.lean`.
-/

end IntensionalSemantics.Reference.Demonstratives
