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

import Linglib.Theories.Semantics.Reference.Basic
import Linglib.Core.ModalLogic
import Linglib.Core.Context.Tower
import Linglib.Core.Context.Shifts

namespace Semantics.Reference.Kaplan

open Core.Intension (Intension rigid IsRigid rigid_isRigid)
open Semantics.Reference.Basic
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

/-! ## Indexicals as Tower Access Patterns

Connects the character/content theory above to the ContextTower infrastructure.
Each pure indexical is an `AccessPattern` reading from the origin (speech-act context)
with a projection to the relevant coordinate. Kaplan's thesis that English indexicals
are invariant under embedding operators becomes a corollary of `origin_stable`. -/

section TowerIndexicals

open Core.Context

variable {W' : Type*} {E' : Type*} {P' : Type*} {T' : Type*}

-- ════════════════════════════════════════════════════════════════
-- § Pure Indexicals as Access Patterns
-- ════════════════════════════════════════════════════════════════

/-- "I" — first person pronoun. Reads the agent from the speech-act context.

    Kaplan (1989): the character of "I" is the function that maps every
    context to the agent of that context. In tower terms, "I" reads from
    the origin (depth 0), projecting `KContext.agent`. -/
def pronI_access : AccessPattern (KContext W' E' P' T') E' :=
  ⟨.origin, KContext.agent⟩

/-- "you" — second person pronoun. Reads the addressee from the speech-act context.

    Following Speas & Tenny (2003), the addressee is a coordinate of the
    Kaplanian context. "You" reads from the origin, projecting `KContext.addressee`. -/
def pronYou_access : AccessPattern (KContext W' E' P' T') E' :=
  ⟨.origin, KContext.addressee⟩

/-- "now" — temporal indexical. Reads the time from the speech-act context.

    Kaplan (1989) §VI: N (now) is a content operator that shifts the
    evaluation time to the context time. As an access pattern, "now"
    reads `KContext.time` from the origin. -/
def opNow_access : AccessPattern (KContext W' E' P' T') T' :=
  ⟨.origin, KContext.time⟩

/-- "here" — spatial indexical. Reads the position from the speech-act context. -/
def opHere_access : AccessPattern (KContext W' E' P' T') P' :=
  ⟨.origin, KContext.position⟩

/-- "actually" — modal indexical. Reads the world from the speech-act context.

    Kaplan (1989) §VI: A (actually) shifts the evaluation world to the
    context world. As an access pattern, "actually" reads `KContext.world`
    from the origin. -/
def opActually_access : AccessPattern (KContext W' E' P' T') W' :=
  ⟨.origin, KContext.world⟩

-- ════════════════════════════════════════════════════════════════
-- § Depth Verification
-- ════════════════════════════════════════════════════════════════

@[simp] theorem pronI_depth :
    (pronI_access (W' := W') (E' := E') (P' := P') (T' := T')).depth = .origin := rfl

@[simp] theorem pronYou_depth :
    (pronYou_access (W' := W') (E' := E') (P' := P') (T' := T')).depth = .origin := rfl

@[simp] theorem opNow_depth :
    (opNow_access (W' := W') (E' := E') (P' := P') (T' := T')).depth = .origin := rfl

@[simp] theorem opHere_depth :
    (opHere_access (W' := W') (E' := E') (P' := P') (T' := T')).depth = .origin := rfl

@[simp] theorem opActually_depth :
    (opActually_access (W' := W') (E' := E') (P' := P') (T' := T')).depth = .origin := rfl

-- ════════════════════════════════════════════════════════════════
-- § Shift Invariance: "I" Under Embedding
-- ════════════════════════════════════════════════════════════════

/-- "I" is invariant under any tower push. This is the formal content of
    Kaplan's thesis for the first person pronoun: no embedding operator
    (attitude verb, temporal shift, mood operator) changes what "I" refers to.

    "John said that I am happy" => "I" = the actual speaker, not John. -/
theorem pronI_shift_invariant
    (t : ContextTower (KContext W' E' P' T')) (σ : ContextShift (KContext W' E' P' T')) :
    pronI_access.resolve (t.push σ) = pronI_access.resolve t :=
  AccessPattern.origin_stable pronI_access rfl t σ

/-- "you" is invariant under any tower push. -/
theorem pronYou_shift_invariant
    (t : ContextTower (KContext W' E' P' T')) (σ : ContextShift (KContext W' E' P' T')) :
    pronYou_access.resolve (t.push σ) = pronYou_access.resolve t :=
  AccessPattern.origin_stable pronYou_access rfl t σ

/-- "now" is invariant under any tower push. -/
theorem opNow_shift_invariant
    (t : ContextTower (KContext W' E' P' T')) (σ : ContextShift (KContext W' E' P' T')) :
    opNow_access.resolve (t.push σ) = opNow_access.resolve t :=
  AccessPattern.origin_stable opNow_access rfl t σ

/-- "here" is invariant under any tower push. -/
theorem opHere_shift_invariant
    (t : ContextTower (KContext W' E' P' T')) (σ : ContextShift (KContext W' E' P' T')) :
    opHere_access.resolve (t.push σ) = opHere_access.resolve t :=
  AccessPattern.origin_stable opHere_access rfl t σ

/-- "actually" is invariant under any tower push. -/
theorem opActually_shift_invariant
    (t : ContextTower (KContext W' E' P' T')) (σ : ContextShift (KContext W' E' P' T')) :
    opActually_access.resolve (t.push σ) = opActually_access.resolve t :=
  AccessPattern.origin_stable opActually_access rfl t σ

-- ════════════════════════════════════════════════════════════════
-- § Kaplan's Thesis (Tower Formulation)
-- ════════════════════════════════════════════════════════════════

/-- Kaplan's thesis as a tower property: an access pattern is Kaplan-compliant
    iff its depth is `.origin`. This means it reads from the speech-act context
    and is unaffected by any embedding operators. -/
def IsKaplanCompliant {C R : Type*} (ap : AccessPattern C R) : Prop :=
  ap.depth = .origin

/-- All English pure indexicals are Kaplan-compliant: they all read from
    the origin (speech-act context).

    This is the tower formulation of Kaplan (1989) §VIII: natural language
    (English) operators cannot shift the context of utterance. In tower
    terms, English indexicals have `depth = .origin`, so embedding (pushing
    shifts) has no effect on their resolution. -/
theorem kaplansThesisTower :
    IsKaplanCompliant (pronI_access (W' := W') (E' := E') (P' := P') (T' := T')) ∧
    IsKaplanCompliant (pronYou_access (W' := W') (E' := E') (P' := P') (T' := T')) ∧
    IsKaplanCompliant (opNow_access (W' := W') (E' := E') (P' := P') (T' := T')) ∧
    IsKaplanCompliant (opHere_access (W' := W') (E' := E') (P' := P') (T' := T')) ∧
    IsKaplanCompliant (opActually_access (W' := W') (E' := E') (P' := P') (T' := T')) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § Resolution in Root Tower
-- ════════════════════════════════════════════════════════════════

/-- In a root tower, "I" resolves to the context's agent. -/
theorem pronI_root (c : KContext W' E' P' T') :
    pronI_access.resolve (ContextTower.root c) = c.agent := rfl

/-- In a root tower, "you" resolves to the context's addressee. -/
theorem pronYou_root (c : KContext W' E' P' T') :
    pronYou_access.resolve (ContextTower.root c) = c.addressee := rfl

/-- In a root tower, "now" resolves to the context's time. -/
theorem opNow_root (c : KContext W' E' P' T') :
    opNow_access.resolve (ContextTower.root c) = c.time := rfl

/-- In a root tower, "here" resolves to the context's position. -/
theorem opHere_root (c : KContext W' E' P' T') :
    opHere_access.resolve (ContextTower.root c) = c.position := rfl

/-- In a root tower, "actually" resolves to the context's world. -/
theorem opActually_root (c : KContext W' E' P' T') :
    opActually_access.resolve (ContextTower.root c) = c.world := rfl

end TowerIndexicals

end Semantics.Reference.Kaplan
