/-
# Doxastic Attitude Semantics

Modal/accessibility-based semantics for doxastic attitude verbs like
`believe`, `know`, `think`.

## Semantic Mechanism

Doxastic attitudes use Hintikka-style accessibility relations:
- R(x, w, w') means w' is compatible with what x believes/knows in w
- ⟦x believes p⟧(w) = ∀w'. R(x,w,w') → p(w')

## Veridicality

- **Veridical** (know, realize): x V p ⊢ p
- **Non-veridical** (believe, think): x V p ⊬ p

## Question Embedding

Doxastic attitudes can embed questions via exhaustive interpretation:
- ⟦x knows Q⟧ = ∀p ∈ Q. (p true → x knows p) ∧ (p false → x knows ¬p)

## References

- Hintikka (1969). Knowledge and Belief.
- Heim (1992). Presupposition projection and the semantics of attitude verbs.
- Karttunen (1977). Syntax and semantics of questions.
-/

import Linglib.Core.Proposition
import Linglib.Theories.Montague.Question.Hamblin

namespace Montague.Verb.Attitude.Doxastic

open Core.Proposition

-- Accessibility Relations

/--
Doxastic accessibility relation type.

R(agent, evalWorld, accessibleWorld) = true iff accessibleWorld is compatible
with what agent believes/knows in evalWorld.
-/
abbrev AccessRel (W E : Type*) := E → W → W → Bool

/--
Universal modal: true at w iff p true at all accessible worlds.

⟦□p⟧(w) = ∀w'. R(w,w') → p(w')
-/
def boxAt {W E : Type*} (R : AccessRel W E) (agent : E) (w : W)
    (worlds : List W) (p : W → Bool) : Bool :=
  worlds.all fun w' => !R agent w w' || p w'

/--
Existential modal: true at w iff p true at some accessible world.

⟦◇p⟧(w) = ∃w'. R(w,w') ∧ p(w')
-/
def diaAt {W E : Type*} (R : AccessRel W E) (agent : E) (w : W)
    (worlds : List W) (p : W → Bool) : Bool :=
  worlds.any fun w' => R agent w w' && p w'

-- Veridicality

/--
A doxastic predicate is veridical if believing/knowing p entails p is true.

Veridical: know, realize, discover
Non-veridical: believe, think, suspect
-/
inductive Veridicality where
  | veridical      -- x V p ⊢ p (knowledge, factives)
  | nonVeridical   -- x V p ⊬ p (belief, opinion)
  deriving DecidableEq, Repr, BEq

/--
Veridicality constraint: if veridical, accessible worlds ⊆ actual world's p-value.

For "know", we require: p(w) = true for the evaluation world w.
-/
def veridicalityHolds {W : Type*} (v : Veridicality) (p : W → Bool) (w : W) : Bool :=
  match v with
  | .veridical => p w  -- Must be true at evaluation world
  | .nonVeridical => true  -- No constraint

-- Doxastic Predicate Structure

/--
A doxastic attitude predicate.

Bundles the accessibility relation with veridicality and other properties.
-/
structure DoxasticPredicate (W E : Type*) where
  /-- Name of the predicate -/
  name : String
  /-- Accessibility relation -/
  access : AccessRel W E
  /-- Veridicality (veridical or not) -/
  veridicality : Veridicality
  /-- Does it create an opaque context? (substitution failures) -/
  createsOpaqueContext : Bool := true

/--
Semantics for a doxastic predicate taking a proposition.

⟦x V that p⟧(w) = (veridicalityHolds V p w) ∧ ∀w'. R(x,w,w') → p(w')

For veridical predicates, we also require p(w) = true.
-/
def DoxasticPredicate.holdsAt {W E : Type*}
    (V : DoxasticPredicate W E) (agent : E) (p : W → Bool)
    (w : W) (worlds : List W) : Bool :=
  veridicalityHolds V.veridicality p w && boxAt V.access agent w worlds p

/--
Semantics for doxastic predicate taking a Hamblin question.

Following Karttunen (1977), "know Q" means knowing the true answer:
⟦x knows Q⟧(w) = ∃p ∈ Q. p(w) ∧ x knows p

For non-veridical predicates, we drop the p(w) requirement:
⟦x believes Q⟧(w) = ∃p ∈ Q. x believes p
-/
def DoxasticPredicate.holdsAtQuestion {W E : Type*}
    (V : DoxasticPredicate W E) (agent : E) (Q : (W → Bool) → Bool)
    (w : W) (worlds : List W) (answers : List (W → Bool)) : Bool :=
  answers.any fun p =>
    Q p &&  -- p is an answer to Q
    (match V.veridicality with
     | .veridical => p w  -- For know: p must be true
     | .nonVeridical => true) &&  -- For believe: no truth requirement
    boxAt V.access agent w worlds p

-- Standard Doxastic Predicates (Abstract)

/--
Abstract "believe" predicate template.

Users instantiate with their specific accessibility relation.
-/
def believeTemplate {W E : Type*} (R : AccessRel W E) : DoxasticPredicate W E :=
  { name := "believe"
  , access := R
  , veridicality := .nonVeridical
  , createsOpaqueContext := true
  }

/--
Abstract "know" predicate template.

Veridical: knowing p requires p to be true.
-/
def knowTemplate {W E : Type*} (R : AccessRel W E) : DoxasticPredicate W E :=
  { name := "know"
  , access := R
  , veridicality := .veridical
  , createsOpaqueContext := true
  }

/--
Abstract "think" predicate template.

Non-veridical, typically less commitment than "believe".
-/
def thinkTemplate {W E : Type*} (R : AccessRel W E) : DoxasticPredicate W E :=
  { name := "think"
  , access := R
  , veridicality := .nonVeridical
  , createsOpaqueContext := true
  }

-- Properties and Theorems

/--
Veridical predicates entail their complement.

If x knows p at w, then p is true at w.
-/
theorem veridical_entails_complement {W E : Type*}
    (V : DoxasticPredicate W E) (hV : V.veridicality = .veridical)
    (agent : E) (p : W → Bool) (w : W) (worlds : List W)
    (holds : V.holdsAt agent p w worlds = true) : p w = true := by
  unfold DoxasticPredicate.holdsAt at holds
  simp only [hV, veridicalityHolds, Bool.and_eq_true] at holds
  exact holds.1

/--
Non-veridical predicates don't entail their complement.

There exist cases where x believes p but p is false.
-/
theorem nonVeridical_not_entails {W E : Type*}
    (V : DoxasticPredicate W E) (hV : V.veridicality = .nonVeridical) :
    ∃ (agent : E) (p : W → Bool) (w : W) (worlds : List W),
      V.holdsAt agent p w worlds = true ∧ p w = false :=
  sorry  -- Requires concrete model to exhibit

/--
Doxastic predicates are closed under known implication.

If x knows p and x knows (p → q), then x knows q.
(This is the K axiom of modal logic)
-/
theorem doxastic_k_axiom {W E : Type*}
    (V : DoxasticPredicate W E) (agent : E) (p q : W → Bool)
    (w : W) (worlds : List W)
    (_hp : boxAt V.access agent w worlds p = true)
    (_hpq : boxAt V.access agent w worlds (fun w' => !p w' || q w') = true) :
    boxAt V.access agent w worlds q = true :=
  sorry  -- K axiom proof: requires detailed case analysis

-- Substitution and Opacity

/-!
## Substitution and Opacity

Opaque contexts block substitution of co-referential terms.

Even if a = b (extensionally), "x believes Fa" may differ from "x believes Fb"
because the agent may not know a = b.

This is formalized by the `createsOpaqueContext` field: when true, the predicate
operates on intensions (functions from worlds), not extensions.
-/

/--
For opaque predicates, substitution failure is possible.

This is a statement that the predicate distinguishes intensions that
happen to have the same extension at the evaluation world.
-/
def substitutionMayFail {W E : Type*} (V : DoxasticPredicate W E) : Prop :=
  V.createsOpaqueContext = true →
  ∃ (agent : E) (p q : W → Bool) (w : W) (worlds : List W),
    p w = q w ∧  -- Same extension at w
    p ≠ q ∧      -- Different intensions
    V.holdsAt agent p w worlds ≠ V.holdsAt agent q w worlds

-- De Dicto vs De Re

/--
De dicto reading: quantifier under the attitude.

"John believes someone is a spy" (de dicto) =
John believes ∃x. spy(x)
-/
def deDicto {W E : Type*} (V : DoxasticPredicate W E)
    (agent : E) (p : W → Bool) (w : W) (worlds : List W) : Bool :=
  V.holdsAt agent p w worlds

/--
De re reading: quantifier over the attitude.

"John believes someone is a spy" (de re) =
∃x. John believes spy(x)

Here we need a domain of individuals to quantify over.
-/
def deRe {W E D : Type*} (V : DoxasticPredicate W E)
    (agent : E) (predicate : D → W → Bool) (domain : List D)
    (w : W) (worlds : List W) : Bool :=
  domain.any fun x => V.holdsAt agent (predicate x) w worlds

-- Connection to Scalar Implicature

/-!
## Attitude Embedding and Scalar Implicature

When scalar expressions are embedded under attitudes, the implicature
can be computed locally (inside the attitude) or globally (about speaker):

**Global**: Speaker implicates ¬(speaker believes all)
**Local**: x believes (some ∧ ¬all) [apparent local reading]

Goodman & Stuhlmüller (2013) show the "local" reading arises from
pragmatic inference about speaker knowledge, not true local computation.

See `RSA/Implementations/GoodmanStuhlmuller2013.lean` for the RSA treatment.
-/

end Montague.Verb.Attitude.Doxastic
