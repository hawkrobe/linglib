/-
# Semantic Structure Interfaces

Typeclasses defining what compositional semantics needs from syntax.

## Philosophy

Different syntactic theories (Minimalism, CCG, HPSG, etc.) have different
representations. Rather than forcing them through a common tree format,
we define *interfaces* that semantics can query.

A semantic analysis declares what it needs:
```
def interpQuantifier [HasBinding S] [HasTerminals S] (s : S) : ...
```

Any syntax that provides those instances can plug in.

## Typeclasses

- `HasTerminals`: Access lexical items at leaves
- `HasBinaryComposition`: Decompose into two children (for FA, PM)
- `HasUnaryProjection`: Single child (for NN rule)
- `HasBinding`: Binding sites with indices (for quantifiers, λ)

## Usage

Semantic modules import these and declare requirements:
```
variable [HasBinaryComposition S] [HasTerminals S]
```

Syntax theories provide instances:
```
instance : HasBinaryComposition SynTree where ...
instance : HasBinaryComposition SynObj where ...
```

## References

- Inspired by Glue Semantics (Dalrymple et al.) modularity
- Follows Mathlib typeclass patterns
-/

import Linglib.Theories.Montague.Basic

namespace Core.Interfaces

open Montague

-- ============================================================================
-- Terminal Access
-- ============================================================================

/--
Access to lexical/terminal content.

Semantics needs to look up meanings of words. This abstracts over
how different syntaxes represent terminals.
-/
class HasTerminals (S : Type) where
  /-- Get terminal content if this is a leaf node -/
  getTerminal : S → Option String

-- ============================================================================
-- Binary Composition
-- ============================================================================

/--
Binary decomposition for Functional Application and Predicate Modification.

H&K's FA and PM rules apply to binary-branching nodes. This abstracts
over how different syntaxes represent branching.
-/
class HasBinaryComposition (S : Type) where
  /-- Decompose into two children if this is a binary node -/
  getBinaryChildren : S → Option (S × S)

-- ============================================================================
-- Unary Projection
-- ============================================================================

/--
Unary decomposition for the Non-Branching Nodes rule.

H&K's NN rule: if α has single daughter β, then ⟦α⟧ = ⟦β⟧.
-/
class HasUnaryProjection (S : Type) where
  /-- Get single child if this is a unary node -/
  getUnaryChild : S → Option S

-- ============================================================================
-- Binding Sites
-- ============================================================================

/--
Binding sites for λ-abstraction.

Needed for: quantifier scope, relative clauses, wh-questions, etc.
The index identifies which variable is bound.

Different syntaxes create binding differently:
- Minimalism: movement leaves traces, λ at landing site
- CCG: type-raising and hypothetical reasoning
- HPSG: index features on NPs
-/
class HasBinding (S : Type) where
  /-- Get binding index and body if this is a binder -/
  getBinder : S → Option (ℕ × S)

-- ============================================================================
-- Semantic Types
-- ============================================================================

/--
Access to semantic types.

For type-driven interpretation, we need to know the semantic type
of constituents. Different syntaxes may compute this differently.
-/
class HasSemanticType (S : Type) where
  /-- Get the semantic type of this node -/
  getType : S → Option Ty

-- ============================================================================
-- Combined Interface
-- ============================================================================

/--
Full semantic structure: everything needed for H&K-style interpretation.

This combines all the interfaces. Use this when you need the full
compositional machinery. Use individual classes when you need less.
-/
class SemanticStructure (S : Type) extends
    HasTerminals S,
    HasBinaryComposition S,
    HasUnaryProjection S,
    HasBinding S,
    HasSemanticType S

-- ============================================================================
-- Generic Interpretation
-- ============================================================================

/--
Check if a node is a terminal.
-/
def isTerminal {S : Type} [HasTerminals S] (s : S) : Bool :=
  (HasTerminals.getTerminal s).isSome

/--
Check if a node is binary-branching.
-/
def isBinary {S : Type} [HasBinaryComposition S] (s : S) : Bool :=
  (HasBinaryComposition.getBinaryChildren s).isSome

/--
Check if a node is a binder.
-/
def isBinder {S : Type} [HasBinding S] (s : S) : Bool :=
  (HasBinding.getBinder s).isSome


-- ============================================================================
-- Summary
-- ============================================================================

/-
## What This Module Provides

### Typeclasses (what semantics can ask for)
- `HasTerminals`: lexical lookup
- `HasBinaryComposition`: FA, PM composition
- `HasUnaryProjection`: NN rule
- `HasBinding`: λ-abstraction, quantifier scope
- `HasSemanticType`: type-driven interpretation
- `SemanticStructure`: all of the above

### For Syntax Theories
Implement these typeclasses for your structures:
- Minimalism: `instance : HasBinding SynObj where ...`
- CCG: `instance : HasBinaryComposition Derivation where ...`
- etc.

### For Semantic Analyses
Declare what you need:
- `[HasBinaryComposition S]` for basic predication
- `[HasBinding S]` for quantifier scope
- `[SemanticStructure S]` for full H&K interpretation

The typeclass constraints document exactly what syntactic assumptions
your semantic analysis makes.
-/

end Core.Interfaces
