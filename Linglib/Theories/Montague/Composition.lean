/-
# Type-Driven Interpretation (Heim & Kratzer Chapter 3)

Formalizes the core composition principles from H&K §3.1:

1. **Terminal Nodes (TN)**: Lexical items get meaning from lexicon
2. **Non-Branching Nodes (NN)**: Unary projection preserves meaning
3. **Functional Application (FA)**: ⟦α⟧ = ⟦β⟧(⟦γ⟧) when types match
4. **Predicate Modification (PM)**: Combine two ⟨e,t⟩ predicates (Ch. 4)

## Key H&K Insight (§3.2)

"The semantic interpretation component can ignore certain features that
syntactic phrase structure trees are usually assumed to have. All it has
to see are the lexical items and the hierarchical structure in which they
are arranged. **Syntactic category labels and linear order are irrelevant.**"

This insight motivates our syntax-agnostic design: interpretation works
with ANY structure that provides terminals and branching, regardless of
the underlying syntactic theory.

## Architecture

1. **Generic interpretation**: Works with ANY syntax via `SemanticStructure` interface
2. **Concrete example**: `SynTree` as one syntax that implements the interface

Any syntactic theory (Minimalism, CCG, HPSG) can plug in by implementing
the typeclasses in `Core/Interfaces/SemanticStructure.lean`.

## References

- Heim & Kratzer (1998) "Semantics in Generative Grammar", Ch. 3-4
- Klein & Sag (1985) "Type-Driven Translation"
-/

import Linglib.Theories.Montague.Basic
import Linglib.Theories.Montague.Modification
import Linglib.Core.Interfaces.SemanticStructure

namespace Montague.Composition

open Montague Montague.Modification Core.Interfaces

-- Typed Denotations

/--
A typed denotation pairs a semantic type with a value of that type.
This is how lexical entries work in H&K: each word has a type and a meaning.
-/
structure TypedDenot (m : Model) where
  ty : Ty
  val : m.interpTy ty

/--
Check if one type can take another as argument via Functional Application.

FA applies when ⟦β⟧ is a function whose domain contains ⟦γ⟧.
That is, β : σ → τ and γ : σ.
-/
def canApply (funTy argTy : Ty) : Option Ty :=
  match funTy with
  | .fn σ τ => if σ = argTy then some τ else none
  | _ => none

-- The Composition Principles (Syntax-Agnostic)

/--
Terminal Nodes (TN): If α is a terminal node, ⟦α⟧ is specified in the lexicon.

H&K §3.1: "The lexicon specifies the denotation of terminal nodes."
-/
def interpTerminal (m : Model) (lex : Lexicon m) (word : String)
    : Option (TypedDenot m) :=
  (lex word).map fun entry => ⟨entry.ty, entry.denot⟩

/--
Non-Branching Nodes (NN): If α is non-branching with daughter β, then ⟦α⟧ = ⟦β⟧.

H&K §3.1: This handles unary projections like N → NP when NP is non-branching.
-/
def interpNonBranching {m : Model} (daughter : TypedDenot m) : TypedDenot m :=
  daughter

/--
Functional Application (FA): If ⟦β⟧ : σ → τ and ⟦γ⟧ : σ, then ⟦α⟧ = ⟦β⟧(⟦γ⟧).

H&K §3.1: "If α is a branching node, {β, γ} is the set of α's daughters,
and ⟦β⟧ is a function whose domain contains ⟦γ⟧, then ⟦α⟧ = ⟦β⟧(⟦γ⟧)."

Note: FA doesn't specify linear order. Types determine which is function, which is argument.
-/
def interpFA {m : Model} {σ τ : Ty}
    (f : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ) : m.interpTy τ :=
  f x

/--
Attempt Functional Application in either direction.

H&K §3.1: "It's the semantic types of the daughter nodes that determine
the procedure for calculating the meaning of the mother node."

We try both orders: f(x) and x(f).
-/
def tryFA {m : Model} (d1 d2 : TypedDenot m) : Option (TypedDenot m) :=
  -- Try d1 as function, d2 as argument
  match hf : d1.ty with
  | .fn σ τ =>
    if ha : σ = d2.ty then
      let f : m.interpTy (σ ⇒ τ) := hf ▸ d1.val
      let a : m.interpTy σ := ha ▸ d2.val
      some ⟨τ, f a⟩
    else
      -- Try d2 as function, d1 as argument
      match hf' : d2.ty with
      | .fn σ' τ' =>
        if ha' : σ' = d1.ty then
          let f : m.interpTy (σ' ⇒ τ') := hf' ▸ d2.val
          let a : m.interpTy σ' := ha' ▸ d1.val
          some ⟨τ', f a⟩
        else none
      | _ => none
  | _ =>
    -- d1 is not a function, try d2 as function
    match hf : d2.ty with
    | .fn σ τ =>
      if ha : σ = d1.ty then
        let f : m.interpTy (σ ⇒ τ) := hf ▸ d2.val
        let a : m.interpTy σ := ha ▸ d1.val
        some ⟨τ, f a⟩
      else none
    | _ => none

/--
Attempt Predicate Modification: combine two ⟨e,t⟩ predicates.

H&K §4.3: "If α is a branching node, {β, γ} is the set of α's daughters,
and ⟦β⟧ and ⟦γ⟧ are both in D⟨e,t⟩, then ⟦α⟧ = λx. ⟦β⟧(x) = ⟦γ⟧(x) = 1."
-/
def tryPM {m : Model} (d1 d2 : TypedDenot m) : Option (TypedDenot m) :=
  match h1 : d1.ty, h2 : d2.ty with
  | .fn .e .t, .fn .e .t =>
    -- Both are ⟨e,t⟩ predicates
    let p1 : m.interpTy (.e ⇒ .t) := h1 ▸ d1.val
    let p2 : m.interpTy (.e ⇒ .t) := h2 ▸ d2.val
    some ⟨.fn .e .t, predicateModification p1 p2⟩
  | _, _ => none

/--
Interpret a binary branching node: try FA first, then PM.

H&K's principle: FA is the primary composition mechanism.
PM is added for modifier constructions (Ch. 4).
-/
def interpBinary {m : Model} (d1 d2 : TypedDenot m) : Option (TypedDenot m) :=
  tryFA d1 d2 <|> tryPM d1 d2

-- Generic Interpretation (Syntax-Agnostic)

/--
Generic recursive interpretation for any syntax satisfying the interface.

This is the core H&K insight: interpretation only needs to know about
terminals, unary nodes, and binary nodes. The syntax theory provides
these via the `SemanticStructure` interface.

H&K §3.2: "All [semantics] has to see are the lexical items and the
hierarchical structure in which they are arranged."
-/
def interpret {S : Type} [HasTerminals S] [HasBinaryComposition S] [HasUnaryProjection S]
    (m : Model) (lex : Lexicon m) (interp : S → Option (TypedDenot m)) (s : S)
    : Option (TypedDenot m) :=
  -- TN: Terminal node → lexical lookup
  match HasTerminals.getTerminal s with
  | some word => interpTerminal m lex word
  | none =>
    -- NN: Unary node → pass through
    match HasUnaryProjection.getUnaryChild s with
    | some child => (interp child).map interpNonBranching
    | none =>
      -- Binary node → FA or PM
      match HasBinaryComposition.getBinaryChildren s with
      | some (left, right) => do
        let d1 ← interp left
        let d2 ← interp right
        interpBinary d1 d2
      | none => none

-- Syntax Trees (Concrete Example)

/--
A simple phrase structure tree for semantic interpretation.

Following H&K §3.2: "phrase structure trees consist of labeled nodes
ordered by dominance and linear precedence."

For semantic interpretation, we only need:
- Terminal nodes (lexical items)
- Unary branching (projection)
- Binary branching (composition)

Linear order and syntactic labels are irrelevant to interpretation.
-/
inductive SynTree where
  | terminal : String → SynTree
  | unary : SynTree → SynTree
  | binary : SynTree → SynTree → SynTree
  deriving Repr

-- SemanticStructure Instances for SynTree

/--
SynTree provides terminal access: extract the word from terminal nodes.
-/
instance : HasTerminals SynTree where
  getTerminal
    | .terminal w => some w
    | _ => none

/--
SynTree provides binary composition: extract children from binary nodes.
-/
instance : HasBinaryComposition SynTree where
  getBinaryChildren
    | .binary t1 t2 => some (t1, t2)
    | _ => none

/--
SynTree provides unary projection: extract child from unary nodes.
-/
instance : HasUnaryProjection SynTree where
  getUnaryChild
    | .unary t => some t
    | _ => none

/--
SynTree doesn't inherently have binding (that requires richer structure).
For now, return none. Richer syntaxes (Minimalism with traces) can provide this.
-/
instance : HasBinding SynTree where
  getBinder _ := none

/--
SynTree doesn't store semantic types on nodes.
Type information comes from the lexicon during interpretation.
-/
instance : HasSemanticType SynTree where
  getType _ := none

/--
SynTree satisfies the full SemanticStructure interface (via the above instances).
-/
instance : SemanticStructure SynTree where

-- SynTree-Specific Interpretation (Uses Generic Machinery)

/--
Recursive tree interpretation for SynTree.

This is a concrete instantiation of the generic `interpret` function.
Implements the three principles:
- TN: Look up terminals in lexicon
- NN: Pass through unary nodes
- Binary: Try FA, then PM
-/
def interpTree (m : Model) (lex : Lexicon m) : SynTree → Option (TypedDenot m)
  | .terminal w => interpTerminal m lex w
  | .unary t =>
    (interpTree m lex t).map interpNonBranching
  | .binary t1 t2 => do
    let d1 ← interpTree m lex t1
    let d2 ← interpTree m lex t2
    interpBinary d1 d2

-- Interpretability (H&K §3.3) - Generic

/--
Generic interpretability check for any syntax.

H&K §3.3: "Structures which fail to receive denotations will be called
uninterpretable. We take it that uninterpretability is one among other
sources of ungrammaticality."
-/
def isInterpretableWith {S : Type} {m : Model} (interp : S → Option (TypedDenot m)) (s : S) : Bool :=
  (interp s).isSome

/--
Generic Principle of Interpretability.

H&K §3.3: "All nodes in a phrase structure tree must be in the domain
of the interpretation function ⟦⟧."
-/
def satisfiesInterpretabilityWith {S : Type} {m : Model} (interp : S → Option (TypedDenot m)) (s : S) : Prop :=
  isInterpretableWith interp s = true

-- Interpretability (H&K §3.3) - SynTree Specific

/--
A tree is interpretable if it receives a denotation.
-/
def isInterpretable (m : Model) (lex : Lexicon m) (t : SynTree) : Bool :=
  (interpTree m lex t).isSome

/--
Principle of Interpretability for SynTree.
-/
def satisfiesInterpretability (m : Model) (lex : Lexicon m) (t : SynTree) : Prop :=
  isInterpretable m lex t = true

-- Type Mismatch Examples (H&K §3.3)

/--
"Ann laughed Jan" is uninterpretable due to type mismatch.

H&K §3.3: The VP "laughed Jan" has type t (truth value), so combining
with subject "Ann" (type e) fails FA—neither is a function of the other.
-/
example : canApply .t .e = none := rfl
example : canApply .e .t = none := rfl

/--
Type mismatch: ⟨e,t⟩ function applied to t argument.

H&K's example "It is not the case that greeted Ann":
- "greeted Ann" : ⟨e,t⟩
- "it is not the case that" : ⟨t,t⟩
Neither can apply to the other.
-/
example : canApply (.fn .t .t) (.fn .e .t) = none := rfl
example : canApply (.fn .e .t) (.fn .t .t) = none := rfl

-- Theorems about Type-Driven Interpretation

/-- NN is the identity on denotations -/
theorem interpNonBranching_id {m : Model} (d : TypedDenot m) :
    interpNonBranching d = d := rfl

/-- FA is well-typed: result type is the codomain of the function -/
theorem interpFA_type {m : Model} {σ τ : Ty}
    (f : m.interpTy (σ ⇒ τ)) (x : m.interpTy σ)
    : (interpFA f x : m.interpTy τ) = f x := rfl

/-- PM preserves type ⟨e,t⟩ -/
theorem tryPM_preserves_type {m : Model} (d1 d2 : TypedDenot m)
    (h1 : d1.ty = .fn .e .t) (h2 : d2.ty = .fn .e .t)
    : ∃ d, tryPM d1 d2 = some d ∧ d.ty = .fn .e .t := by
  cases d1 with | mk ty1 val1 =>
  cases d2 with | mk ty2 val2 =>
  simp only at h1 h2
  subst h1 h2
  exact ⟨_, rfl, rfl⟩

/-- FA and PM are the only composition mechanisms for binary nodes -/
theorem interpBinary_eq {m : Model} (d1 d2 : TypedDenot m) :
    interpBinary d1 d2 = (tryFA d1 d2).orElse (fun _ => tryPM d1 d2) := rfl

-- Summary

/-
## What This Module Provides

### Core Principles (H&K §3.1, §4.3)
- `interpTerminal`: TN - lexical lookup
- `interpNonBranching`: NN - unary projection
- `interpFA`: FA - functional application
- `tryPM`: PM - predicate modification

### Syntax-Agnostic Interpretation
- `interpret`: Generic interpretation for ANY syntax satisfying `SemanticStructure`
- `TypedDenot`: Type-value pairs (syntax-independent)
- `interpBinary`: Binary node composition (FA then PM)

### Concrete Example: SynTree
- `SynTree`: Simple phrase structure trees
- `interpTree`: SynTree-specific interpretation
- Instances: `HasTerminals`, `HasBinaryComposition`, `HasUnaryProjection`, etc.

### Interpretability (H&K §3.3)
- `isInterpretableWith`: Generic interpretability check
- `satisfiesInterpretabilityWith`: Generic Principle of Interpretability
- `isInterpretable`: SynTree-specific check
- `satisfiesInterpretability`: SynTree-specific principle

### Key H&K Insight (§3.2)

"Syntactic category labels and linear order are irrelevant."

Type-driven interpretation means:
1. We don't need construction-specific rules
2. Semantic types determine composition order
3. Type mismatch causes uninterpretability
4. ANY syntax that provides terminals + branching can be interpreted

### For Other Syntactic Theories

To interpret your syntax, implement:
```lean
instance : HasTerminals   YourSyntax where ...
instance : HasBinaryComposition YourSyntax where ...
instance : HasUnaryProjection   YourSyntax where ...
```

Then use `interpret` or write a recursive function using the composition primitives.
-/

end Montague.Composition
