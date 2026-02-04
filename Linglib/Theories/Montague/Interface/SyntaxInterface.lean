/-
# Syntax-Semantics Interface: What Montague Requires

This module documents what Montague semantics requires from and provides to
syntactic theories, and what it's agnostic to.

## The Homomorphism Principle (Compositionality)

Montague's key insight: semantics is a HOMOMORPHISM from syntax to meanings.

For every syntactic rule R: A × B → C
there exists a semantic rule R': ⟦A⟧ × ⟦B⟧ → ⟦C⟧

such that ⟦R(a, b)⟧ = R'(⟦a⟧, ⟦b⟧)

This is the ONLY requirement Montague places on syntax.
-/

import Linglib.Theories.Montague.Basic

namespace Montague.Interface.SyntaxInterface

open Montague

-- WHAT MONTAGUE REQUIRES FROM SYNTAX

/-
## Required: Type Assignment

Every syntactic category must be assigned a semantic type.

Examples:
- NP → e (entities)
- S → t (truth values)
- IV (intransitive verb) → e → t (properties)
- TV (transitive verb) → e → e → t (relations)
- Det → (e → t) → (e → t) → t (quantifiers)

This assignment must be:
1. TOTAL: Every category gets a type
2. SYSTEMATIC: Derived categories have predictable types
-/

/-- A type assignment maps syntactic categories to semantic types -/
structure TypeAssignment (SynCat : Type) where
  /-- The semantic type for a syntactic category -/
  typeOf : SynCat → Ty

/-
## Required: Compositional Rules

For each syntactic combination rule, there must be a corresponding
semantic composition rule that operates on the appropriate types.

In practice, most rules reduce to FUNCTION APPLICATION:
- If f : σ → τ and a : σ, then f(a) : τ
-/

/-- A compositional semantics maps derivations to meanings -/
class CompositionalSemantics (SynCat : Type) (Deriv : Type) where
  /-- Type assignment -/
  types : TypeAssignment SynCat
  /-- Model for interpretation -/
  model : Model
  /-- Semantic interpretation of a derivation -/
  interp : Deriv → (cat : SynCat) → model.interpTy (types.typeOf cat)

-- WHAT MONTAGUE IS AGNOSTIC TO

/-
## Agnostic: Choice of Syntactic Formalism

Montague works with ANY syntax that provides compositional structure:

### Categorial Grammars (CCG, CG, TLG)
- Natural fit: categories encode types directly
- X/Y means "give me Y, I'll give you X"
- Type correspondence is built into the formalism

### Phrase Structure Grammars (HPSG, LFG)
- Assign types to phrasal categories (NP, VP, S)
- Composition via phrase structure rules
- May need type-shifting for flexibility

### Minimalism
- Assign types to features/functional heads
- Merge corresponds to function application
- LF provides the compositional structure

### Dependency Grammar
- Assign types to dependency relations
- Composition via head-dependent combination
- May need different type assignments

The SYNTAX doesn't matter - only that it provides:
1. Structured representations (trees, proofs, etc.)
2. A systematic way to combine meanings
-/

/-
## Agnostic: Linear Order

Montague semantics doesn't care about word order.
"John sees Mary" and "Mary sees John" have different meanings
NOT because of order, but because of structural roles (subject vs object).

Different languages with different word orders (SVO, SOV, VSO)
all get the same semantic treatment.
-/

/-
## Agnostic: Morphological Realization

Whether a language marks case, agreement, tense, etc. morphologically
doesn't affect the semantic composition. These features may be:
- Reflected in the syntax (triggering different rules)
- Ignored semantically (pure agreement)
- Semantically interpreted (tense → temporal operators)

But the COMPOSITIONAL STRUCTURE is what matters.
-/

-- WHAT MONTAGUE IS INCOMPATIBLE WITH

/-
## Incompatible: Non-Compositional Theories

Any theory where meaning ISN'T determined by structure is incompatible:

### Pure Construction Grammar
If constructions have meanings not derivable from parts,
Montague can't model them directly.
(Though constructional meanings CAN be encoded as lexical rules)

### Holistic Approaches
If sentence meaning is primitive (not built from parts),
there's nothing for Montague to compute.

### Strict Behaviorism
If meaning is just stimulus-response patterns with no
compositional structure, Montague doesn't apply.
-/

/-
## Incompatible: Non-Functional Type Systems

Montague uses the simply-typed lambda calculus.
Alternative type systems may be incompatible:

### Dependent Types for Semantics
If types depend on values (not just other types),
the simply-typed approach needs extension.
(Linear type theories, separation logic, etc.)

### Substructural Logics
If meaning combination isn't freely duplicable/discardable,
the standard functional approach needs modification.
(Relevant for resource-sensitive semantics)

Note: These aren't necessarily WRONG, just require
extending beyond basic Montague.
-/

-- THE INTERFACE IN CODE

/-
## Abstract Interface

Any syntax that wants to use Montague semantics must provide:
-/

/-- Requirements for a syntax to interface with Montague semantics -/
class MontagueSyntax (SynCat : Type) (Deriv : Type) where
  /-- Get the syntactic category of a derivation -/
  catOf : Deriv → SynCat
  /-- Type assignment -/
  typeOf : SynCat → Ty
  /-- Check if a derivation is well-formed -/
  wellFormed : Deriv → Prop
  /-- Compositional interpretation -/
  interp : (d : Deriv) → (m : Model) → m.interpTy (typeOf (catOf d))

/-
## What the Syntax Gets Back

In return, Montague semantics provides:

1. **Truth conditions**: For any sentence, whether it's true in a model
2. **Entailment**: Logical relationships between sentences
3. **Compositionality**: Systematic meaning computation
4. **Model-theoretic grounding**: Clear semantics for linguistic expressions
-/

/-- Results that Montague provides to any compatible syntax -/
structure MontagueBenefits (SynCat : Type) (Deriv : Type) [MontagueSyntax SynCat Deriv] where
  /-- Truth in a model -/
  trueIn : Deriv → Model → Bool
  /-- Entailment between derivations -/
  entails : Deriv → Deriv → Model → Bool

-- SUMMARY

/-
## Montague Requires
- Type assignment to syntactic categories
- Compositional combination rules
- Structured representations

## Montague Is Agnostic To
- Choice of syntactic formalism (CCG, HPSG, Minimalism, DG)
- Word order
- Morphological realization
- Specific rule inventory

## Montague Is Incompatible With
- Non-compositional meaning theories
- Holistic/behaviorist approaches
- (Some) non-standard type systems

## The Interface
Any syntax providing `MontagueSyntax` gets compositional semantics.
This is demonstrated concretely in CCG/Semantics.lean.
-/

end Montague.Interface.SyntaxInterface

-- Backward compatibility alias
namespace Montague.SyntaxInterface
  export Montague.Interface.SyntaxInterface (TypeAssignment CompositionalSemantics MontagueSyntax MontagueBenefits)
end Montague.SyntaxInterface
