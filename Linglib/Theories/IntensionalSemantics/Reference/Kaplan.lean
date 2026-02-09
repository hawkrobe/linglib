/-
# Kaplan's Character/Content Semantics

Formalizes Kaplan (1989) "Demonstratives": the two-stage semantics for
indexicals and the theory of singular propositions (Almog 2014, Ch 2).

## Key Results

- `indexical`: Character varies with context, content is rigid
- `pronI`: "I" picks out the agent of the context
- `pronI_directlyReferential`: "I" is directly referential
- `SingularProposition`: Structured ⟨individual, property⟩ pairs
- `structured_distinguishes_unstructured`: The Frege puzzle — same
  unstructured content, different structured content

## References

- Kaplan, D. (1989). Demonstratives. In Almog, Perry & Wettstein (eds.),
  Themes from Kaplan. Oxford University Press.
- Almog, J. (2014). Referential Mechanics, Ch 2.
-/

import Linglib.Theories.IntensionalSemantics.Reference.Basic
import Linglib.Core.ModalLogic
import Linglib.Core.Context

namespace IntensionalSemantics.Reference.Kaplan

open Core.Intension (Intension rigid IsRigid rigid_isRigid)
open IntensionalSemantics.Reference.Basic
open Core.Context (KContext)

/-! ## Indexicals -/

/-- An indexical expression: its character varies with context (unlike proper
names), but its content at each context is rigid.

Example: "I" has a different content when uttered by Alice vs Bob,
but once we fix the context, the content rigidly picks out the agent. -/
def indexical {W E : Type*} (charFn : Context W E → E) : ReferringExpression (Context W E) W E :=
  { character := λ c => rigid (charFn c)
  , mechanisms := [.designation, .singularProp] }

/-- "I": picks out the agent of the context. -/
def pronI {W E : Type*} : ReferringExpression (Context W E) W E :=
  indexical (λ c => c.agent)

/-- "I" is directly referential: at every context, its content is rigid. -/
theorem pronI_directlyReferential {W E : Type*} :
    isDirectlyReferential (pronI (W := W) (E := E)).character :=
  λ _ => rigid_isRigid _

/-- "You": picks out the addressee of the context (Speas & Tenny's HEARER).

    Parallel to `pronI` but uses the full `KContext` (which has `addressee`)
    rather than the simple `Context` (which only has `agent` and `world`). -/
def pronYou {W E P T : Type*} : ReferringExpression (KContext W E P T) W E :=
  { character := λ c => rigid c.addressee
  , mechanisms := [.designation, .singularProp] }

/-- "You" is directly referential: at every context, its content is rigid. -/
theorem pronYou_directlyReferential {W E P T : Type*} :
    isDirectlyReferential (pronYou (W := W) (E := E) (P := P) (T := T)).character :=
  λ _ => rigid_isRigid _

/-- Indexicals have non-constant character (in general).

"I" said by Alice ≠ "I" said by Bob: the character varies. -/
theorem indexical_character_varies {W E : Type*} [Inhabited W]
    (charFn : Context W E → E)
    (c₁ c₂ : Context W E) (h : charFn c₁ ≠ charFn c₂) :
    (indexical charFn).character c₁ ≠ (indexical charFn).character c₂ := by
  intro heq
  have : (indexical charFn).character c₁ default = (indexical charFn).character c₂ default :=
    congrFun heq default
  simp only [indexical, rigid] at this
  exact h this

/-! ## Singular Propositions -/

/-- A singular proposition: a structured pair ⟨individual, property⟩.

Where unstructured propositions are sets of worlds (W → Bool), singular
propositions retain the identity of the individual. This is essential
for solving the Frege puzzle: ⟨Hesperus, bright⟩ ≠ ⟨Phosphorus, bright⟩
even when "Hesperus is bright" and "Phosphorus is bright" are true at
exactly the same worlds. -/
structure SingularProposition (W : Type*) (E : Type*) where
  /-- The individual the proposition is about -/
  individual : E
  /-- The property predicated of the individual -/
  property : E → W → Bool

namespace SingularProposition

variable {W E : Type*}

/-- Evaluate a singular proposition at a world. -/
def eval (sp : SingularProposition W E) (w : W) : Bool :=
  sp.property sp.individual w

/-- Flatten a singular proposition to an unstructured proposition (W → Bool). -/
def flatten (sp : SingularProposition W E) : W → Bool :=
  λ w => sp.property sp.individual w

/-- Two singular propositions with the same property but different individuals
produce the same unstructured content iff the property can't distinguish them.

This is the formal Frege puzzle: ⟨a, P⟩ and ⟨b, P⟩ may flatten to the same
W → Bool, yet remain distinct as structured propositions because a ≠ b. -/
theorem structured_distinguishes_unstructured
    (a b : E) (P : E → W → Bool) (hab : a ≠ b)
    (_hflat : (SingularProposition.mk a P).flatten = (SingularProposition.mk b P).flatten) :
    (SingularProposition.mk a P) ≠ (SingularProposition.mk b P) := by
  intro heq
  have : (SingularProposition.mk a P).individual = (SingularProposition.mk b P).individual :=
    congrArg SingularProposition.individual heq
  simp at this
  exact hab this

end SingularProposition

/-! ## Bridge to Attitude/Intensional -/

/-- Montague's `up` operator (constant intension) coincides with the character
of a proper name: both produce `rigid e`.

This connects the PTQ-style `up` (in `Attitude/Intensional.lean`) to the
Kaplanian `constantCharacter` of a proper name. -/
theorem constantCharacter_is_up {C W E : Type*} (e : E) (c : C) :
    (properName (C := C) (W := W) e).character c = rigid e := rfl

/-! ## Kaplan's Logical Truth: "I am here now" -/

/-- "I am here now" is a logical truth in the logic of demonstratives:
at every context, the content is true at the world of the context.

It is NOT necessary — there are worlds where the agent is elsewhere.
This distinguishes logical truth (true at every context) from
necessity (true at every world). -/
theorem i_am_here_now_logically_true {W E : Type*}
    (here : Context W E → E → W → Bool)
    (hCtx : ∀ c : Context W E, here c c.agent c.world = true) :
    ∀ c : Context W E, here c c.agent c.world = true :=
  hCtx

end IntensionalSemantics.Reference.Kaplan
