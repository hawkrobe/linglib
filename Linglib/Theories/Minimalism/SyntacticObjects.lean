/-
# Syntactic Objects

Formalization of syntactic objects following Chomsky's Minimalist Program.

## Key Definitions

- **Lexical Item (LI)**: Bundle of features including category and selectional requirements
- **Complex LI**: List of feature bundles - enables head movement (Chomsky 1995)
- **Syntactic Object (SO)**: Either an LI token or a set of two SOs
- **Merge**: The fundamental structure-building operation

## References

- Chomsky, N. (1995). "The Minimalist Program"
- Chomsky, N. (2013). "Problems of Projection"
- Adger, D. (2003). "Core Syntax", Chapters 2-3
-/

import Mathlib.Data.Set.Basic

namespace Minimalism

-- ============================================================================
-- Part 1: Categorial Features
-- ============================================================================

/-- Categorial features (Definition 10)

    These are Minimalism-specific categories following Harizanov's notation.
    Note: `v` is light verb, `A` is adjective (Minimalist notation). -/
inductive Cat where
  | V     -- verb
  | N     -- noun
  | A     -- adjective
  | P     -- preposition
  | D     -- determiner
  | T     -- tense
  | C     -- complementizer
  | v     -- light verb
  deriving Repr, DecidableEq, Inhabited

/-- A selectional stack specifies what categories an LI selects
    The stack is consumed as selection proceeds -/
abbrev SelStack := List Cat

-- ============================================================================
-- Part 2: Lexical Items
-- ============================================================================

/-- A simple LI is a ⟨CAT, SEL⟩ pair (Definition 10)
    - `cat`: The categorial feature (what this LI IS)
    - `sel`: What this LI selects (stack, consumed left-to-right) -/
structure SimpleLI where
  cat : Cat
  sel : SelStack
  deriving Repr, DecidableEq

/-- A lexical item can be simple or complex (Definition 88)

    Complex LIs arise from head-to-head movement: when X moves to Y
    via head-to-head, Y becomes a complex LI containing both X and Y's
    feature bundles. This is crucial for reprojection.

    The list is ordered: the "outer" (projecting) features come first. -/
structure LexicalItem where
  features : List SimpleLI
  nonempty : features ≠ []
  deriving Repr

/-- Decidable equality for LexicalItem based on features -/
instance : DecidableEq LexicalItem := λ a b =>
  if h : a.features = b.features then
    isTrue (by cases a; cases b; simp at h; simp [h])
  else
    isFalse (by intro heq; cases heq; exact h rfl)

/-- Create a simple (non-complex) LI -/
def LexicalItem.simple (cat : Cat) (sel : SelStack) : LexicalItem :=
  ⟨[⟨cat, sel⟩], by simp⟩

/-- Get the outer (projecting) category of an LI -/
def LexicalItem.outerCat (li : LexicalItem) : Cat :=
  match li.features with
  | [] => .V  -- unreachable by nonempty constraint
  | s :: _ => s.cat

/-- Get the outer selectional requirements -/
def LexicalItem.outerSel (li : LexicalItem) : SelStack :=
  match li.features with
  | [] => []  -- unreachable
  | s :: _ => s.sel

/-- Is this LI complex (result of head-to-head movement)? -/
def LexicalItem.isComplex (li : LexicalItem) : Bool :=
  li.features.length > 1

/-- Combine two LIs into a complex LI (for head-to-head movement)
    The target Y's features come first (Y reprojects) -/
def LexicalItem.combine (target mover : LexicalItem) : LexicalItem :=
  ⟨target.features ++ mover.features, by
    cases htf : target.features with
    | nil => exact absurd htf target.nonempty
    | cons hd tl => simp⟩

-- ============================================================================
-- Part 3: LI Tokens
-- ============================================================================

/-- An LI token is a specific instance of an LI in a derivation
    Different tokens of the same LI are distinct objects -/
structure LIToken where
  item : LexicalItem
  id : Nat
  deriving Repr

/-- Decidable equality for LIToken based on id and item -/
instance : DecidableEq LIToken := λ a b =>
  if hid : a.id = b.id then
    if hitem : a.item = b.item then
      isTrue (by cases a; cases b; simp at hid hitem; simp [hid, hitem])
    else
      isFalse (by intro heq; cases heq; exact hitem rfl)
  else
    isFalse (by intro heq; cases heq; exact hid rfl)

-- ============================================================================
-- Part 4: Syntactic Objects
-- ============================================================================

/-- A syntactic object is either:
    1. An LI token (leaf/terminal)
    2. A set of exactly two SOs (derived by Merge)

    Definition 11: "A syntactic object (SO) is either:
    (a) a Lexical Item (LI) token, or
    (b) a set of SOs" -/
inductive SyntacticObject where
  | leaf : LIToken → SyntacticObject
  | node : SyntacticObject → SyntacticObject → SyntacticObject
  deriving Repr, DecidableEq

namespace SyntacticObject

/-- Is this SO a leaf (LI token)? -/
def isLeaf : SyntacticObject → Bool
  | .leaf _ => true
  | .node _ _ => false

/-- Is this SO derived (result of Merge)? -/
def isNode : SyntacticObject → Bool
  | .leaf _ => false
  | .node _ _ => true

/-- Get the LI token if this is a leaf -/
def getLIToken : SyntacticObject → Option LIToken
  | .leaf tok => some tok
  | .node _ _ => none

/-- Get the two immediate constituents if this is a node -/
def getConstituents : SyntacticObject → Option (SyntacticObject × SyntacticObject)
  | .leaf _ => none
  | .node a b => some (a, b)

end SyntacticObject

-- ============================================================================
-- Part 5: Merge
-- ============================================================================

/-- Merge: the structure-building operation (Definition 12)

    "Merge is the operation that takes two distinct SOs X and Y
    as input and yields the SO {X, Y} as output."

    Note: We model sets as ordered pairs (node), which is standard
    in computational treatments. The unorderedness is captured in
    the symmetric treatment in labeling. -/
def merge (x y : SyntacticObject) : SyntacticObject :=
  .node x y

/-- Valid merge requires distinct inputs
    "X and Y must be distinct, i.e., not identical" -/
def validMerge (x y : SyntacticObject) : Prop :=
  x ≠ y

/-- External Merge: combining two separate SOs -/
def externalMerge (x y : SyntacticObject) (_h : x ≠ y) : SyntacticObject :=
  merge x y

/-- Internal Merge: re-merging an SO already in the structure
    This is the basis of movement -/
def internalMerge (target mover : SyntacticObject) (_h : target ≠ mover) : SyntacticObject :=
  merge mover target

-- ============================================================================
-- Part 6: Example Constructions
-- ============================================================================

/-- Create a simple leaf SO from category and selection -/
def mkLeaf (cat : Cat) (sel : SelStack) (id : Nat) : SyntacticObject :=
  .leaf ⟨.simple cat sel, id⟩

/-- Example: A transitive verb "eat" - V that selects D (object) -/
def exampleVerb : SyntacticObject := mkLeaf .V [.D] 1

/-- Example: A noun "pizza" - N with no selection -/
def exampleNoun : SyntacticObject := mkLeaf .N [] 2

/-- Example: A determiner "the" - D that selects N -/
def exampleDet : SyntacticObject := mkLeaf .D [.N] 3

-- ============================================================================
-- Part 7: Basic Properties
-- ============================================================================

/-- Count the number of nodes (Merge operations) in an SO -/
def SyntacticObject.nodeCount : SyntacticObject → Nat
  | .leaf _ => 0
  | .node a b => 1 + a.nodeCount + b.nodeCount

/-- Count the number of leaves (LI tokens) in an SO -/
def SyntacticObject.leafCount : SyntacticObject → Nat
  | .leaf _ => 1
  | .node a b => a.leafCount + b.leafCount

/-- Leaves + 1 = Nodes (binary tree property) -/
theorem leaf_node_relation (so : SyntacticObject) :
    so.leafCount = so.nodeCount + 1 := by
  induction so with
  | leaf _ => simp [SyntacticObject.leafCount, SyntacticObject.nodeCount]
  | node a b iha ihb =>
    simp [SyntacticObject.leafCount, SyntacticObject.nodeCount]
    omega

end Minimalism
