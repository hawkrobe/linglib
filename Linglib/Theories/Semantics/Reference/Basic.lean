/-
# Direct Reference: Core Infrastructure

Almog's (2014) three-mechanism taxonomy of direct reference:
1. **Designation**: A term rigidly picks out an object (Kripke 1980)
2. **Singular proposition**: Content is a structured ⟨individual, property⟩ (Kaplan 1989)
3. **Referential use**: Speaker intends a particular individual (Donnellan 1966)

These mechanisms are independent: a term can exhibit any subset.

## Key Definitions

- `Context`: Kaplanian context of utterance (agent, world)
- `Character`: Two-stage semantics — context → content
- `ReferringExpression`: Bundles character + mechanism
- `isDirectlyReferential`: Content is rigid at every context
- `properName`: Constant character, rigid content

## References

- Almog, J. (2014). Referential Mechanics. Oxford University Press.
- Kaplan, D. (1989). Demonstratives. In Almog, Perry & Wettstein (eds.), Themes from Kaplan.
- Kripke, S. (1980). Naming and Necessity. Harvard University Press.
- Donnellan, K. (1966). Reference and Definite Descriptions. Philosophical Review.
-/

import Linglib.Core.Intension
import Linglib.Core.Proposition
import Linglib.Core.Context

namespace Semantics.Reference.Basic

open Core.Intension (Intension rigid IsRigid rigid_isRigid evalAt CoRefer CoExtensional
  rigid_identity_necessary)

/-! ## Context and Character -/

/-- A Kaplanian context of utterance.

Contexts supply the parameters that indexicals depend on: who is speaking,
what world is actual, etc. Following Kaplan (1989), characters are functions
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

/-! ## Reference Mechanisms -/

/-- Almog's three independent mechanisms of direct reference.

Each mechanism is a distinct *way* that an expression can refer directly:
- `designation`: The expression rigidly designates its referent (Kripke)
- `singularProp`: The content is a structured singular proposition (Kaplan)
- `referentialUse`: The speaker uses the expression to pick out a particular
  individual, regardless of the expression's descriptive content (Donnellan) -/
inductive RefMechanism where
  | designation
  | singularProp
  | referentialUse
  deriving DecidableEq, BEq, Repr

/-- A referring expression bundles a character with the mechanism(s) it exhibits. -/
structure ReferringExpression (C : Type*) (W : Type*) (E : Type*) where
  /-- The expression's character (linguistic meaning) -/
  character : Character C W E
  /-- Which direct-reference mechanism(s) the expression exhibits -/
  mechanisms : List RefMechanism

/-! ## Direct Reference Properties -/

/-- An expression is directly referential iff its content is rigid at every context.

Kaplan (1989): "For directly referential terms, the referent determines
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
  , mechanisms := [.designation, .singularProp] }

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

Cf. Kripke (1980): "one meter" is de facto rigid (happens to pick out the
same length at every world) but not de jure rigid (its character involves
a description). -/
def IsDeJureRigid {C W E : Type*} (expr : ReferringExpression C W E) : Prop :=
  .designation ∈ expr.mechanisms ∧ isDirectlyReferential expr.character

/-- De facto rigidity: the expression happens to have rigid content at
the actual context, but not by mechanism. "The smallest prime" is de facto
rigid (it's 2 at every world) but its character is descriptive. -/
def IsDeFactoRigid {C W E : Type*} (expr : ReferringExpression C W E) (c : C) : Prop :=
  IsRigid (expr.character c) ∧ .designation ∉ expr.mechanisms

/-- Proper names are de jure rigid. -/
theorem properName_deJureRigid {C W E : Type*} (e : E) :
    IsDeJureRigid (properName (C := C) (W := W) e) :=
  ⟨List.Mem.head _, properName_isDirectlyReferential e⟩

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
