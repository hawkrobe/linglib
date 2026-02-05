import Linglib.Theories.TruthConditional.Basic

/-!
# Semantic Structure Interfaces

Typeclasses defining what compositional semantics needs from syntax.
-/

namespace Core.Interfaces

open TruthConditional

/-- Access to lexical/terminal content. -/
class HasTerminals (S : Type) where
  /-- Get terminal content if this is a leaf node -/
  getTerminal : S → Option String

/-- Binary decomposition for Functional Application and Predicate Modification. -/
class HasBinaryComposition (S : Type) where
  /-- Decompose into two children if this is a binary node -/
  getBinaryChildren : S → Option (S × S)

/-- Unary decomposition for H&K's Non-Branching Nodes rule. -/
class HasUnaryProjection (S : Type) where
  /-- Get single child if this is a unary node -/
  getUnaryChild : S → Option S

/-- Binding sites for λ-abstraction. -/
class HasBinding (S : Type) where
  /-- Get binding index and body if this is a binder -/
  getBinder : S → Option (ℕ × S)

/-- Access to semantic types. -/
class HasSemanticType (S : Type) where
  /-- Get the semantic type of this node -/
  getType : S → Option Ty

/-- Full semantic structure for H&K-style interpretation. -/
class SemanticStructure (S : Type) extends
    HasTerminals S,
    HasBinaryComposition S,
    HasUnaryProjection S,
    HasBinding S,
    HasSemanticType S

/-- Check if a node is a terminal. -/
def isTerminal {S : Type} [HasTerminals S] (s : S) : Bool :=
  (HasTerminals.getTerminal s).isSome

/-- Check if a node is binary-branching. -/
def isBinary {S : Type} [HasBinaryComposition S] (s : S) : Bool :=
  (HasBinaryComposition.getBinaryChildren s).isSome

/-- Check if a node is a binder. -/
def isBinder {S : Type} [HasBinding S] (s : S) : Bool :=
  (HasBinding.getBinder s).isSome

end Core.Interfaces
