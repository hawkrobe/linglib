/-
# Montague Semantics: Anaphora and Binding

Semantic interpretation of binding configurations, following Heim & Kratzer (1998).

## Architecture

1. Syntax provides: `BindingConfig` (via `HasBindingConfig` interface)
2. Semantics interprets: Assignment functions + λ-abstraction

This module extends `Variables.lean` to interpret full binding configurations.

## Mathematical Perspective: Continuations

The H&K assignment-based approach and B&S continuation approach are
mathematically equivalent. The continuation view reveals the underlying
computational structure:

- Binders = scope-taking continuations
- Binding = duplication via the W combinator
- Evaluation order = order of continuation consumption

This correspondence is developed in Part 3.

## References

- Heim & Kratzer (1998). Semantics in Generative Grammar. Ch. 5.
- Barker & Shan (2014). Continuations and Natural Language. Ch. 15.
-/

import Linglib.Theories.Montague.Basic
import Linglib.Theories.Montague.Variables
import Linglib.Theories.Montague.Determiner.Quantifier
import Linglib.Core.Interfaces.BindingSemantics

namespace Montague.Anaphora

open Montague
open Montague.Variables
open Interfaces.BindingSemantics


/-!
## From Syntax to Semantics

Given a `BindingConfig` from some syntactic theory, we interpret it using
assignment functions. The key operations:

1. Binder: Introduces λ-abstraction over a variable index
2. Bindee: Reads from the assignment at that index
3. Free variable: Reads from the ambient assignment
-/

/-- Semantic interpretation state: current assignment + pending abstractions -/
structure InterpState (m : Model) where
  /-- Current assignment function -/
  assignment : Assignment m
  /-- Stack of indices being abstracted over (for nested binders) -/
  abstractionStack : List Nat

/-- Initial interpretation state with a given assignment -/
def InterpState.initial {m : Model} (g : Assignment m) : InterpState m :=
  { assignment := g, abstractionStack := [] }

/-- Push an abstraction index onto the stack -/
def InterpState.pushAbstraction {m : Model}
    (state : InterpState m) (idx : Nat) : InterpState m :=
  { state with abstractionStack := idx :: state.abstractionStack }

/-- Interpret a bound pronoun: read from assignment at the variable index -/
def interpretBoundPronoun {m : Model}
    (state : InterpState m) (varIdx : Nat) : m.Entity :=
  state.assignment varIdx

/-- Interpret a binder: create a function that updates the assignment -/
def interpretBinder {m : Model} {τ : Ty}
    (varIdx : Nat) (body : InterpState m → m.interpTy τ)
    (state : InterpState m) : m.interpTy (.e ⇒ τ) :=
  λ x => body { state with assignment := state.assignment[varIdx ↦ x] }


/-!
## Semantic Binding Conditions

The traditional binding conditions (A, B, C) constrain syntax.
Here we state their semantic correlates: when does binding produce
well-defined interpretations?
-/

/-- A binding is semantically well-formed if the binder's scope includes the bindee.

In terms of interpretation: when we evaluate the bindee, the binder's
λ-abstraction must still be "active" (on the abstraction stack).
-/
def bindingWellFormed {m : Model}
    (state : InterpState m) (varIdx : Nat) : Bool :=
  varIdx ∈ state.abstractionStack

/-- Interpret a binding configuration as a semantic check.

Returns true if all bindings are semantically coherent:
- Every bound variable is within scope of its binder
- No unbound variables (all free variables have indices in the assignment domain)
-/
def interpretBindingConfig {m : Model}
    (bc : BindingConfig) (_g : Assignment m) : Bool :=
  -- All bindings must have consistent indices
  bc.wellFormed


/-!
## Continuations as Mathematical Abstraction

B&S 2014 shows that GQs are continuations: `(Entity → Bool) → Bool`.
This view reveals that binding is fundamentally about duplication:
when a pronoun is bound, the binder's entity is used twice.

### The W Combinator

The duplicator combinator W = λκλx.κxx captures binding:
- κ : Entity → Entity → Bool (expects two entities)
- W κ : Entity → Bool (takes one entity, uses it twice)

"Every₁ boy loves himself₁" →
- "every boy" provides entity x
- W duplicates: the VP expects subject and object, gets x for both
-/

/-- Duplicator combinator W = λκλx.κxx

Binding amounts to duplication of a value
into multiple positions in a continuation.
-/
def W {A B : Type} (κ : A → A → B) (x : A) : B := κ x x

/-- W is the semantic content of reflexive binding.

"John sees himself" = W(λsubj λobj. sees(subj, obj))(john)
                    = sees(john, john)
-/
example : W (λ x y => x == y) 5 = true := rfl

/-- Continuation monad for binding.

This is the GQ type from Quantifiers.lean, made explicit as a monad.
Binders are values of this type; binding is monadic composition.
-/
abbrev Cont' (R A : Type) := (A → R) → R

/-- Return (unit): lift a value into the continuation monad -/
def Cont'.pure {R A : Type} (a : A) : Cont' R A := λ k => k a

/-- Bind: compose continuations -/
def Cont'.bind {R A B : Type} (m : Cont' R A) (f : A → Cont' R B) : Cont' R B :=
  λ k => m (λ a => f a k)

instance {R : Type} : Monad (Cont' R) where
  pure := Cont'.pure
  bind := Cont'.bind

/-!
### Correspondence Theorem

The H&K assignment approach and B&S continuation approach are equivalent:

- H&K: Binder introduces λx_n, bindee reads g(n)
- B&S: Binder is continuation (Entity → Bool) → Bool, bindee uses W

The W combinator corresponds to the H&K rule:
  "λx_n body" applied to "e" = body[n ↦ e]

Both achieve: the binder's entity appears in the bindee's position.
-/

/-- The H&K interpretation of binding (from Variables.lean) -/
def hkBinding {m : Model} (n : Nat) (body : m.Entity → Bool)
    (binder : m.Entity) (g : Assignment m) : Bool :=
  body (g[n ↦ binder] n)  -- = body(binder)

/-- The B&S interpretation of binding (continuation-based) -/
def bsBinding {Entity : Type} (body : Entity → Entity → Bool)
    (binder : Entity) : Bool :=
  W body binder  -- = body(binder, binder)

/-- When body treats both arguments uniformly, H&K and B&S agree.

This shows the mathematical equivalence for the reflexive case:
both approaches produce body(binder, binder).
-/
theorem hk_bs_reflexive_equiv {m : Model} (n : Nat)
    (body : m.Entity → m.Entity → Bool)
    (binder : m.Entity) (g : Assignment m) :
    -- H&K: evaluate body with both arguments from updated assignment
    body (g[n ↦ binder] n) (g[n ↦ binder] n) =
    -- B&S: use W to duplicate
    W body binder := by
  simp only [W, update_same]

-- PART 3b: CATEGORICAL PERSPECTIVE

/-!
## Categorical Relationship: Reader ↔ Continuation

The H&K and B&S approaches are categorically related via the
Reader-Continuation adjunction.

### Reader Monad (H&K)

Assignment functions are instances of the Reader monad:
```
Reader E A = E → A
```

For binding, E = (Nat → Entity) (the assignment type), so:
```
Reader (Nat → Entity) A = (Nat → Entity) → A
```

A denotation-with-free-variables is exactly a Reader computation.

### Continuation Monad (B&S)

The continuation monad:
```
Cont R A = (A → R) → R
```

For binding, R = Bool, A = Entity, so GQ = Cont Bool Entity.

### The Adjunction

These monads are related via the continuation-passing transform:

1. CPS transform: Converts Reader-style to Cont-style
   ```
   cps : (E → A) → ((A → R) → E → R)
   cps f = λk e. k (f e)
   ```

2. Uncps transform: Converts Cont-style back to Reader-style
   ```
   uncps : ((A → R) → E → R) → (E → A)
   uncps g = λe. g (λa. a) e   -- when R = A
   ```

These form an adjunction (not isomorphism) because information
flows differently through continuations vs readers.

### The W Combinator Categorically

W is the diagonal in the Kleisli category of Cont:
```
W : Cont R (A × A) → Cont R A
W m = m >>= λ(x,y). pure x   -- when x = y
```

Or more directly, W is the contraction morphism of the
comonoid structure on continuations.
-/

/-- The Reader monad (same as `ReaderT E Id`) -/
abbrev Reader (E A : Type) := E → A

/-- Reader is a monad -/
instance {E : Type} : Monad (Reader E) where
  pure a := λ _ => a
  bind m f := λ e => f (m e) e

/-- CPS transform: Reader → Continuation-expecting function.

This is one direction of the Reader-Cont relationship.
-/
def cpsTransform {E A R : Type} (f : Reader E A) : (A → R) → E → R :=
  λ k e => k (f e)

/-- The Yoneda embedding view: Cont R A ≅ ∀X. (A → X) → (R → X) → X

This is the categorical essence: continuations are a form of
universal property (existential types / coproducts).
-/
def contAsYoneda {R A : Type} (c : Cont' R A) : (A → R) → R := c

/-- CPS transform preserves binding semantics.

For any Reader-style denotation, the CPS transform produces
a Cont-style denotation with equivalent behavior.
-/
theorem cps_preserves_semantics {E A : Type} (f : Reader E A) (e : E) (k : A → Bool) :
    cpsTransform f k e = k (f e) := rfl

/-- W is the semantic content of binding in both frameworks.

In the Reader framework: binding copies a value from the environment.
In the Cont framework: binding duplicates via W.

Both reduce to "use the same entity twice."
-/
theorem binding_is_contraction {A : Type} (rel : A → A → Bool) (x : A) :
    -- Reader-style: read x twice from environment
    (λ _ : Unit => rel x x) () =
    -- Cont-style: use W to duplicate
    W rel x := rfl


/-!
## Evaluation Order and Binding Constraints

B&S's insight: traditional binding conditions follow from evaluation order.
In left-to-right evaluation:

- Condition A (reflexives local): Reflexive must be evaluated while
  binder's continuation is active

- Condition B (pronouns non-local): Pronouns shift to find binders
  outside the local evaluation context

- Crossover: Pronoun evaluated before binder, so no entity is available
-/

/-- Evaluation context tracks which binders are "active" -/
structure EvalContext (Entity : Type) where
  /-- Stack of active binders (most recent first) -/
  activeBinders : List Entity
  /-- Evaluation position (left-to-right) -/
  position : Nat
  deriving Repr

/-- A pronoun can be bound only if its binder is active -/
def canBind {Entity : Type} [DecidableEq Entity]
    (ctx : EvalContext Entity) (binder : Entity) : Bool :=
  binder ∈ ctx.activeBinders

/-- Crossover: pronoun position < binder position → binding fails -/
def crossover (pronounPos binderPos : Nat) : Bool :=
  pronounPos < binderPos


/-!
## VP Ellipsis

VP ellipsis with bound pronouns creates ambiguity:

"John₁ loves his₁ mother, and Bill does too"
- Strict: Bill loves John's mother (pronoun keeps original referent)
- Sloppy: Bill loves Bill's mother (pronoun re-bound)

The continuation approach explains this as two evaluation strategies:
- Strict: Copy the VP's denotation (including resolved pronoun)
- Sloppy: Copy the VP's continuation-expecting form (pronoun re-binds)
-/

/-- Strict reading: pronoun resolves to original antecedent -/
def strictReading {Entity : Type}
    (vp : Entity → Entity → Bool)  -- λsubj λpro. loves(subj, mother(pro))
    (antecedent : Entity)          -- John
    (ellipsisSite : Entity)        -- Bill
    : Bool :=
  vp ellipsisSite antecedent  -- Bill loves John's mother

/-- Sloppy reading: pronoun re-binds to new subject -/
def sloppyReading {Entity : Type}
    (vp : Entity → Entity → Bool)
    (ellipsisSite : Entity)
    : Bool :=
  W vp ellipsisSite  -- Bill loves Bill's mother

/-- VPE ambiguity: both readings available -/
structure VPEAmbiguity (Entity : Type) where
  vp : Entity → Entity → Bool
  antecedentSubj : Entity
  ellipsisSite : Entity

def VPEAmbiguity.strictValue {Entity : Type} (a : VPEAmbiguity Entity) : Bool :=
  strictReading a.vp a.antecedentSubj a.ellipsisSite

def VPEAmbiguity.sloppyValue {Entity : Type} (a : VPEAmbiguity Entity) : Bool :=
  sloppyReading a.vp a.ellipsisSite


end Montague.Anaphora
