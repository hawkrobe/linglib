/-
# Syntactic Objects and Containment

Foundation module for the Minimalist Program formalization.

## Syntactic Objects

- `SimpleLI`, `LexicalItem`, `LIToken`, `SyntacticObject`
- `merge`, `externalMerge`, `internalMerge`

## Containment Relations

- **Immediate Containment**: X immediately contains Y iff Y is a member of X
- **Containment (Dominance)**: Transitive closure of immediate containment
- **C-command**: Standard asymmetric relation for binding and locality

## References

- Chomsky, N. (1995). "The Minimalist Program"
- Chomsky, N. (2013). "Problems of Projection"
- Adger, D. (2003). "Core Syntax", Chapters 2-3
-/

import Mathlib.Data.Set.Basic
import Linglib.Core.UD

namespace Minimalism

/-- Categorial features (Definition 10) -/
inductive Cat where
  | V     -- verb
  | N     -- noun
  | A     -- adjective
  | P     -- preposition
  | D     -- determiner
  | T     -- tense
  | C     -- complementizer
  | v     -- light verb
  | Voice -- Voice head (Kratzer 1996; Schäfer 2008)
  | Appl  -- Applicative head (Pylkkänen 2008; Cuervo 2003)
  | Fin   -- finiteness (Rizzi 1997 split-CP; allocutive probe in Magahi/Galician)
  | SA    -- speech act head (Speas & Tenny 2003; hosts speaker/addressee)
  deriving Repr, DecidableEq, Inhabited

/-- Selectional stack consumed left-to-right -/
abbrev SelStack := List Cat

/-- A simple LI is a ⟨CAT, SEL⟩ pair (Definition 10), optionally with
    a phonological form for linearization. -/
structure SimpleLI where
  cat : Cat
  sel : SelStack
  phonForm : String := ""
  deriving Repr, DecidableEq

/-- Lexical item (simple or complex from head movement, Definition 88) -/
structure LexicalItem where
  features : List SimpleLI
  nonempty : features ≠ []
  deriving Repr

instance : DecidableEq LexicalItem := λ a b =>
  if h : a.features = b.features then
    isTrue (by cases a; cases b; simp at h; simp [h])
  else
    isFalse (by intro heq; cases heq; exact h rfl)

/-- Create a simple (non-complex) LI -/
def LexicalItem.simple (cat : Cat) (sel : SelStack) (phonForm : String := "") : LexicalItem :=
  ⟨[⟨cat, sel, phonForm⟩], by simp⟩

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

/-- Combine two LIs for head-to-head movement (target reprojects) -/
def LexicalItem.combine (target mover : LexicalItem) : LexicalItem :=
  ⟨target.features ++ mover.features, by
    cases htf : target.features with
    | nil => exact absurd htf target.nonempty
    | cons hd tl => simp⟩

/-- LI token: specific instance of an LI in a derivation -/
structure LIToken where
  item : LexicalItem
  id : Nat
  deriving Repr

instance : DecidableEq LIToken := λ a b =>
  if hid : a.id = b.id then
    if hitem : a.item = b.item then
      isTrue (by cases a; cases b; simp at hid hitem; simp [hid, hitem])
    else
      isFalse (by intro heq; cases heq; exact hitem rfl)
  else
    isFalse (by intro heq; cases heq; exact hid rfl)

/-- Syntactic object: LI token or set of two SOs (Definition 11) -/
inductive SyntacticObject where
  | leaf : LIToken → SyntacticObject
  | node : SyntacticObject → SyntacticObject → SyntacticObject
  deriving Repr, DecidableEq

namespace SyntacticObject

def isLeaf : SyntacticObject → Bool
  | .leaf _ => true
  | .node _ _ => false

def isNode : SyntacticObject → Bool
  | .leaf _ => false
  | .node _ _ => true

def getLIToken : SyntacticObject → Option LIToken
  | .leaf tok => some tok
  | .node _ _ => none

def getConstituents : SyntacticObject → Option (SyntacticObject × SyntacticObject)
  | .leaf _ => none
  | .node a b => some (a, b)

end SyntacticObject

/-- Merge: the fundamental structure-building operation (Definition 12) -/
def merge (x y : SyntacticObject) : SyntacticObject :=
  .node x y

def validMerge (x y : SyntacticObject) : Prop :=
  x ≠ y

def externalMerge (x y : SyntacticObject) (_h : x ≠ y) : SyntacticObject :=
  merge x y

def internalMerge (target mover : SyntacticObject) (_h : target ≠ mover) : SyntacticObject :=
  merge mover target

/-- Create a leaf SO from category and selection -/
def mkLeaf (cat : Cat) (sel : SelStack) (id : Nat) : SyntacticObject :=
  .leaf ⟨.simple cat sel, id⟩

/-- Create a leaf SO with a phonological form -/
def mkLeafPhon (cat : Cat) (sel : SelStack) (phon : String) (id : Nat) : SyntacticObject :=
  .leaf ⟨.simple cat sel (phonForm := phon), id⟩

/-- Map UD UPOS tags to Minimalist categories.

    This bridges the theory-neutral UD POS tags used in Core/Basic.lean
    and Fragments/ to the Minimalist Cat system. -/
def uposToCat : UD.UPOS → Cat
  | .VERB  => .V
  | .AUX   => .T
  | .NOUN  => .N
  | .PROPN => .N  -- proper nouns are N (but project to DP)
  | .ADJ   => .A
  | .ADP   => .P
  | .DET   => .D
  | .SCONJ => .C
  | .CCONJ => .C
  | _      => .N  -- default

/-- Get the phonological yield of an SO (collect phonForms from leaves) -/
def SyntacticObject.phonYield : SyntacticObject → List String
  | .leaf tok =>
    let phon := tok.item.features.head?.map (·.phonForm) |>.getD ""
    if phon.isEmpty then [] else [phon]
  | .node a b => a.phonYield ++ b.phonYield

/-- Create a trace SO. Traces are leaves with a distinguished sentinel:
    cat = N, sel = [], phonForm = "", and id = index + 10000.
    This encoding is detectable via `isTrace`. -/
def mkTrace (index : Nat) : SyntacticObject :=
  .leaf ⟨.simple .N [] (phonForm := ""), index + 10000⟩

/-- Detect if an SO is a trace (created via mkTrace).
    Returns the trace index if so. -/
def isTrace : SyntacticObject → Option Nat
  | .leaf tok => if tok.id ≥ 10000 then some (tok.id - 10000) else none
  | .node _ _ => none

def exampleVerb : SyntacticObject := mkLeaf .V [.D] 1

def exampleNoun : SyntacticObject := mkLeaf .N [] 2

def exampleDet : SyntacticObject := mkLeaf .D [.N] 3

/-- Count nodes (Merge operations) in an SO -/
def SyntacticObject.nodeCount : SyntacticObject → Nat
  | .leaf _ => 0
  | .node a b => 1 + a.nodeCount + b.nodeCount

def SyntacticObject.leafCount : SyntacticObject → Nat
  | .leaf _ => 1
  | .node a b => a.leafCount + b.leafCount
theorem leaf_node_relation (so : SyntacticObject) :
    so.leafCount = so.nodeCount + 1 := by
  induction so with
  | leaf _ => simp [SyntacticObject.leafCount, SyntacticObject.nodeCount]
  | node a b iha ihb =>
    simp [SyntacticObject.leafCount, SyntacticObject.nodeCount]
    omega

-- ============================================================================
-- Containment Relations
-- ============================================================================

-- Part 1: Immediate Containment (Definition 13)

/-- X immediately contains Y iff Y is a member of X

    "X immediately contains Y iff X = {Y, Z} for some SO Z"

    Since our SOs are binary sets, this means Y is one of the
    two immediate daughters of X. -/
def immediatelyContains (x y : SyntacticObject) : Prop :=
  match x with
  | .leaf _ => False
  | .node a b => y = a ∨ y = b

/-- Decidable immediate containment -/
instance decImmediatelyContains (x y : SyntacticObject) :
    Decidable (immediatelyContains x y) := by
  unfold immediatelyContains
  cases x with
  | leaf _ => exact isFalse (λ h => h)
  | node a b =>
    cases h1 : decide (y = a) with
    | true =>
      simp at h1
      exact isTrue (Or.inl h1)
    | false =>
      simp at h1
      cases h2 : decide (y = b) with
      | true =>
        simp at h2
        exact isTrue (Or.inr h2)
      | false =>
        simp at h2
        exact isFalse (λ h => h.elim h1 h2)

-- Part 2: Containment / Dominance (Definition 14)

/-- Containment is the transitive closure of immediate containment

    "X contains Y iff X immediately contains Y or
    X immediately contains some SO Z such that Z contains Y"

    This is standard syntactic dominance. -/
inductive contains : SyntacticObject → SyntacticObject → Prop where
  | imm : ∀ x y, immediatelyContains x y → contains x y
  | trans : ∀ x y z, immediatelyContains x z → contains z y → contains x y

-- Part 3: Properties of Containment

/-- Immediate containment implies containment -/
theorem imm_implies_contains {x y : SyntacticObject}
    (h : immediatelyContains x y) : contains x y :=
  contains.imm x y h

/-- Containment is transitive -/
theorem contains_trans {x y z : SyntacticObject}
    (hxy : contains x y) (hyz : contains y z) : contains x z := by
  induction hxy with
  | imm x y himm =>
    exact contains.trans x z y himm hyz
  | trans x y w himm _ ih =>
    exact contains.trans x z w himm (ih hyz)

/-- Leaves contain nothing -/
theorem leaf_contains_nothing (tok : LIToken) (y : SyntacticObject) :
    ¬(contains (SyntacticObject.leaf tok) y) := by
  intro h
  cases h with
  | imm _ _ himm =>
    simp [immediatelyContains] at himm
  | trans _ _ z himm _ =>
    simp [immediatelyContains] at himm

-- Part 3b: Well-Foundedness via nodeCount

/-- Immediate containment strictly decreases nodeCount -/
theorem immediatelyContains_lt_nodeCount {x y : SyntacticObject}
    (h : immediatelyContains x y) : y.nodeCount < x.nodeCount := by
  cases x with
  | leaf _ => simp [immediatelyContains] at h
  | node a b =>
    simp only [immediatelyContains] at h
    simp only [SyntacticObject.nodeCount]
    rcases h with rfl | rfl
    · omega
    · omega

/-- Containment strictly decreases nodeCount -/
theorem contains_lt_nodeCount {x y : SyntacticObject}
    (h : contains x y) : y.nodeCount < x.nodeCount := by
  induction h with
  | imm x y himm =>
    exact immediatelyContains_lt_nodeCount himm
  | trans x y z himm _ ih =>
    have h1 := immediatelyContains_lt_nodeCount himm
    omega

/-- No element contains itself (containment is irreflexive) -/
theorem contains_irrefl (x : SyntacticObject) : ¬contains x x := by
  intro h
  have hlt := contains_lt_nodeCount h
  exact Nat.lt_irrefl _ hlt

-- Part 4: Membership in Derivation

/-- X is a term of Y iff X = Y or Y contains X

    "X is a term of SO Y iff X = Y or Y contains X"

    This is useful for stating when an element is "somewhere in" a structure -/
def isTermOf (x y : SyntacticObject) : Prop :=
  x = y ∨ contains y x

/-- Every SO is a term of itself -/
theorem self_is_term (x : SyntacticObject) : isTermOf x x :=
  Or.inl rfl

/-- If Y contains X, then X is a term of Y -/
theorem contained_is_term {x y : SyntacticObject} (h : contains y x) : isTermOf x y :=
  Or.inr h

-- Part 5: Root and Reflexive Containment

/-- Reflexive containment (useful for stating constraints) -/
def containsOrEq (x y : SyntacticObject) : Prop :=
  x = y ∨ contains x y

/-- Every SO reflexively contains itself -/
theorem refl_containsOrEq (x : SyntacticObject) : containsOrEq x x :=
  Or.inl rfl

/-- Reflexive containment is transitive -/
theorem containsOrEq_trans {x y z : SyntacticObject}
    (hxy : containsOrEq x y) (hyz : containsOrEq y z) : containsOrEq x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  · rcases hyz with rfl | hyz
    · exact Or.inr hxy
    · exact Or.inr (contains_trans hxy hyz)

-- Part 6: Sisters

/-- X and Y are sisters iff they are immediately contained in the same SO

    "X and Y are sisters iff they are immediately contained in some SO Z" -/
def areSisters (x y : SyntacticObject) : Prop :=
  ∃ z, immediatelyContains z x ∧ immediatelyContains z y ∧ x ≠ y

/-- If a node has daughters a and b, they are sisters -/
theorem node_daughters_are_sisters (a b : SyntacticObject) (h : a ≠ b) :
    areSisters a b := by
  use .node a b
  constructor
  · simp [immediatelyContains]
  constructor
  · simp [immediatelyContains]
  · exact h

-- Part 7: C-Command (Standard Definition)

/-- X c-commands Y iff X's sister contains (or equals) Y

    Standard syntactic relation. X c-commands everything in its sister's
    projection. -/
def cCommands (x y : SyntacticObject) : Prop :=
  ∃ z, areSisters x z ∧ containsOrEq z y

/-- A node c-commands its sister -/
theorem ccommand_sister {x y : SyntacticObject} (h : areSisters x y) :
    cCommands x y :=
  ⟨y, h, Or.inl rfl⟩

-- C-command is not symmetric (in general)
-- This is expected: in {X, {Y, Z}}, X c-commands Y and Z,
-- but Y only c-commands Z (not X)

end Minimalism
