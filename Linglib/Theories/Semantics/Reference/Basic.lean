/-
# Direct Reference: Core Infrastructure

@cite{almog-2014}'s three-mechanism taxonomy of direct reference:
1. **Designation**: A term rigidly picks out an object
2. **Singular proposition**: Content is a structured ⟨individual, property⟩
3. **Referential use**: Speaker intends a particular individual

These mechanisms are independent: a term can exhibit any subset.

## Key Definitions

- `Context`: Kaplanian context of utterance (agent, world)
- `Character`: Two-stage semantics — context → content
- `ReferringExpression`: Bundles character + referential profile
- `isDirectlyReferential`: Content is rigid at every context
- `properName`: Constant character, rigid content

-/

import Linglib.Core.Semantics.Intension
import Linglib.Core.Semantics.Proposition
import Linglib.Core.Context.Basic

namespace Semantics.Reference.Basic

open Core (Intension)
open Core.Intension (rigid IsRigid rigid_isRigid evalAt CoRefer CoExtensional
  rigid_identity_necessary)

/-! ## Context and Character -/

/-- A Kaplanian context of utterance.

Contexts supply the parameters that indexicals depend on: who is speaking,
what world is actual, etc. Following @cite{kaplan-1989}, characters are functions
from contexts to contents. -/
structure Context (W : Type*) (E : Type*) where
  /-- The agent of the context (the speaker) -/
  agent : E
  /-- The world of the context (the actual world) -/
  world : W

/-- A Kaplanian character: a function from contexts to contents (intensions).

Characters represent the *linguistic meaning* of an expression — what any
competent speaker knows. Content (= intension) represents what is said
on a particular occasion of use. -/
abbrev Character (C : Type*) (W : Type*) (E : Type*) := C → Intension W E

/-- Content is just an intension — a function from worlds to extensions. -/
abbrev Content (W : Type*) (E : Type*) := Intension W E

/-! ## Referential Profile (@cite{almog-2014}) -/

/-- @cite{almog-2014}'s three independent mechanisms of direct reference,
represented as a three-dimensional Boolean profile.

Each dimension is a distinct *way* that an expression can refer:
- `designation`: The expression rigidly designates its referent (Kripke)
- `singularProp`: The content is a structured singular proposition (Kaplan)
- `referentialUse`: The speaker uses the expression to pick out a particular
  individual, regardless of the expression's descriptive content (Donnellan)

The three dimensions are logically independent: any of the 2³ = 8 combinations
is coherent, and @cite{almog-2014} argues each is linguistically attested. -/
structure ReferentialProfile where
  /-- Kripke: the expression rigidly designates its referent -/
  designation : Bool
  /-- Kaplan: the content is a structured ⟨individual, property⟩ pair -/
  singularProp : Bool
  /-- Donnellan: the speaker has a cognitive fix on a particular individual -/
  referentialUse : Bool
  deriving DecidableEq, BEq, Repr

/-- A referring expression bundles a character with its referential profile. -/
structure ReferringExpression (C : Type*) (W : Type*) (E : Type*) where
  /-- The expression's character (linguistic meaning) -/
  character : Character C W E
  /-- Which direct-reference mechanisms the expression exhibits -/
  profile : ReferentialProfile

/-! ## Direct Reference Properties -/

/-- An expression is directly referential iff its content is rigid at every context.

@cite{kaplan-1989}: "For directly referential terms, the referent determines
the content; once we fix the referent, the content is just the referent
itself." -/
def isDirectlyReferential {C W E : Type*} (char : Character C W E) : Prop :=
  ∀ c : C, IsRigid (char c)

/-- A character is constant iff it assigns the same content at every context.

Proper names have constant character: "Aristotle" picks out the same
intension regardless of who utters it or when. -/
def constantCharacter {C W E : Type*} (char : Character C W E) : Prop :=
  ∀ c₁ c₂ : C, char c₁ = char c₂

/-! ## Proper Names -/

/-- A proper name for entity `e`: constant character, rigid content.

"Aristotle" ↦ at every context, the intension λw. e (the constant
function returning e). This is the paradigm case of direct reference
via the designation mechanism. -/
def properName {C W E : Type*} (e : E) : ReferringExpression C W E :=
  { character := λ _ => rigid e
  , profile := ⟨true, true, false⟩ }

/-- Proper names have constant character. -/
theorem properName_constantCharacter {C W E : Type*} (e : E) :
    constantCharacter (properName (C := C) (W := W) e).character :=
  λ _ _ => rfl

/-- Proper names are directly referential. -/
theorem properName_isDirectlyReferential {C W E : Type*} (e : E) :
    isDirectlyReferential (properName (C := C) (W := W) e).character :=
  λ _ => rigid_isRigid e

/-- The content of a proper name equals `rigid e`, connecting to Core.Intension. -/
theorem properName_content_eq_rigid {C W E : Type*} (e : E) (c : C) :
    (properName (W := W) e).character c = rigid e := rfl

/-! ## De Jure vs De Facto Rigidity -/

/-- De jure rigidity: the expression is rigid *by mechanism* — its linguistic
meaning guarantees rigidity. Proper names and indexicals are de jure rigid.

Cf. @cite{kripke-1980}: "one meter" is de facto rigid (happens to pick out the
same length at every world) but not de jure rigid (its character involves
a description). -/
def IsDeJureRigid {C W E : Type*} (expr : ReferringExpression C W E) : Prop :=
  expr.profile.designation = true ∧ isDirectlyReferential expr.character

/-- De facto rigidity: the expression happens to have rigid content at
the actual context, but not by mechanism. "The smallest prime" is de facto
rigid (it's 2 at every world) but its character is descriptive. -/
def IsDeFactoRigid {C W E : Type*} (expr : ReferringExpression C W E) (c : C) : Prop :=
  IsRigid (expr.character c) ∧ expr.profile.designation = false

/-- Proper names are de jure rigid. -/
theorem properName_deJureRigid {C W E : Type*} (e : E) :
    IsDeJureRigid (properName (C := C) (W := W) e) :=
  ⟨rfl, properName_isDirectlyReferential e⟩

/-- Two proper names that co-refer are co-extensional (Kripke's argument).

Bridge to `Core.Intension.rigid_identity_necessary`: if "Hesperus" and
"Phosphorus" are both proper names and co-refer at the actual world,
they have the same content. -/
theorem properNames_corefer_coextensional {C W E : Type*}
    (e₁ e₂ : E) (c : C) (w : W)
    (h : CoRefer ((properName (C := C) (W := W) e₁).character c)
                 ((properName (W := W) e₂).character c) w) :
    CoExtensional ((properName (C := C) (W := W) e₁).character c)
                  ((properName (W := W) e₂).character c) :=
  rigid_identity_necessary _ _ (rigid_isRigid e₁) (rigid_isRigid e₂) w h

/-! ## Bridge to KContext -/

/-- Lift a simple `Context W E` to a full `KContext W E P T` by supplying
trivial time and position.

This allows existing code using the two-component context to interoperate
with the full Kaplanian context. -/
def Context.toKContext {W E P T : Type*} (c : Context W E) (addr : E) (p : P) (t : T) :
    Core.Context.KContext W E P T :=
  ⟨c.agent, addr, c.world, t, p⟩

end Semantics.Reference.Basic
