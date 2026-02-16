/-!
# Semantic Structure Interfaces

Typeclasses defining what compositional semantics needs from syntax.
Parameterized over an arbitrary type system `T` — Semantics.Montague instantiates
with `Ty`, but other theories can supply their own.
-/

namespace Core.Interfaces

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
  getBinder : S → Option (Nat × S)

/-- Access to semantic types, parameterized over the type system `T`. -/
class HasSemanticType (S : Type) (T : Type) where
  /-- Get the semantic type of this node -/
  getType : S → Option T

/-- Full semantic structure for H&K-style interpretation. -/
class SemanticStructure (S : Type) (T : Type) extends
    HasTerminals S,
    HasBinaryComposition S,
    HasUnaryProjection S,
    HasBinding S,
    HasSemanticType S T

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
