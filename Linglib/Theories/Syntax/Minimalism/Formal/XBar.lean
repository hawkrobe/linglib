/-
# X-Bar Theory

Formalization of X-Bar structure following Adger (2003) Chapter 2.

## The X-Bar Schema

X-Bar theory provides a template for phrase structure:

```
      XP (maximal projection)
     /  \
  Spec   X' (intermediate projection)
        /  \
       X    Complement
     (head)
```

- X = head (zero-level, minimal)
- X' = intermediate projection (bar-level)
- XP = maximal projection (phrase-level)

## Key Principles

1. **Endocentricity**: Every phrase has a head of the same category
2. **Binary Branching**: All structures are binary
3. **Specifier-Head-Complement**: Linear order in English

## References

- Jackendoff, R. (1977). X-Bar Syntax.
- Chomsky, N. (1986). Barriers.
- Adger, D. (2003). Core Syntax, Chapter 2.
-/

import Linglib.Theories.Syntax.Minimalism.Core.Labeling

namespace Minimalism

-- Part 1: Bar Levels

/-- Bar level in X-Bar theory
    - zero: X (head, minimal projection)
    - bar: X' (intermediate projection)
    - max: XP (maximal projection, phrase) -/
inductive BarLevel where
  | zero  -- X (head)
  | bar   -- X' (intermediate)
  | max   -- XP (maximal/phrase)
  deriving Repr, DecidableEq, Inhabited

/-- String representation for bar levels -/
def BarLevel.toString : BarLevel → String
  | .zero => "X⁰"
  | .bar => "X'"
  | .max => "XP"

instance : ToString BarLevel := ⟨BarLevel.toString⟩

-- Part 2: X-Bar Phrase Structure

/-- An X-Bar phrase with explicit Spec-Head-Complement structure

    This captures the traditional X-Bar schema:
    - `head`: The lexical head X
    - `complement`: The sister of X (selected by X)
    - `specifier`: The sister of X' (in Spec position)
    - `cat`: The category of the phrase -/
structure XBarPhrase where
  cat : Cat
  head : SyntacticObject
  complement : Option SyntacticObject := none
  specifier : Option SyntacticObject := none
  deriving Repr

/-- Create an X-Bar phrase from a head only (no complement or specifier) -/
def XBarPhrase.fromHead (h : SyntacticObject) : Option XBarPhrase :=
  match h.getLIToken with
  | some tok => some { cat := tok.item.outerCat, head := h }
  | none => none

/-- Add a complement to an X-Bar phrase (head + complement = X') -/
def XBarPhrase.addComplement (xp : XBarPhrase) (comp : SyntacticObject) : XBarPhrase :=
  { xp with complement := some comp }

/-- Add a specifier to an X-Bar phrase (X' + specifier = XP) -/
def XBarPhrase.addSpecifier (xp : XBarPhrase) (spec : SyntacticObject) : XBarPhrase :=
  { xp with specifier := some spec }

-- Part 3: Computing Bar Level

/-- Compute the bar level of a syntactic object relative to a root

    - A leaf is minimal (zero)
    - A node where the head projects further is intermediate (bar)
    - A node where the head doesn't project further is maximal (max) -/
def barLevelIn (so root : SyntacticObject) : BarLevel :=
  -- If it's a leaf (LI), it's zero-level (head)
  if so.isLeaf then
    .zero
  else
    -- If it's maximal (doesn't project), it's XP
    -- If it projects, it's X'
    -- Use the isMaximalIn check
    match so with
    | .leaf _ => .zero  -- unreachable, covered above
    | .node _ _ =>
      -- Check if there's anything that immediately contains so with same label
      let hasParentWithSameLabel := match root with
        | .leaf _ => false
        | .node a b =>
          if a == so || b == so then
            sameLabelB so root
          else
            -- Need to search deeper (simplified: just check at top level)
            false
      if hasParentWithSameLabel then .bar else .max

/-- Alternative: determine bar level from structure alone -/
def barLevelSimple (so : SyntacticObject) : BarLevel :=
  match so with
  | .leaf _ => .zero
  | .node a b =>
    -- If both children are leaves, could be X' (head + complement)
    -- If one child is a phrase (node), more likely XP (spec + X')
    match a.isLeaf, b.isLeaf with
    | true, true => .bar   -- Two heads merged = likely X' (head + complement)
    | true, false => .max  -- Leaf + phrase = likely XP (specifier configuration)
    | false, true => .max  -- Phrase + leaf = likely XP
    | false, false => .max -- Two phrases = XP level

-- Part 4: Extracting Structure

/-- Get the specifier of a node (the non-projecting daughter)

    In {Spec, X'}, the specifier is the daughter that doesn't share
    the label with the parent. -/
def getSpecifier (so : SyntacticObject) : Option SyntacticObject :=
  match so with
  | .leaf _ => none
  | .node a b =>
    -- The specifier is the one that doesn't project (different label)
    if selectsB a b then
      none  -- a selects b, so b is complement, not specifier
    else if selectsB b a then
      none  -- b selects a, so a is complement, not specifier
    else
      -- Neither selects the other - this is a spec-head configuration
      -- The phrase projects, so the leaf/phrase that doesn't project is spec
      if sameLabelB a so then some b
      else if sameLabelB b so then some a
      else none

/-- Get the complement of a node (the selected daughter)

    In {X, Complement}, the complement is the daughter selected by the head. -/
def getComplement (so : SyntacticObject) : Option SyntacticObject :=
  match so with
  | .leaf _ => none
  | .node a b =>
    -- The complement is the one that's selected
    if selectsB a b then some b
    else if selectsB b a then some a
    else none

/-- Get the head of a phrase (the projecting minimal element) -/
def getHead (so : SyntacticObject) : Option SyntacticObject :=
  match so with
  | .leaf _ => some so
  | .node a b =>
    -- The head is the element whose label matches the phrase's label
    if sameLabelB a so then getHead a
    else if sameLabelB b so then getHead b
    else none

-- Part 5: X-Bar Well-Formedness

/-- An X-Bar phrase is well-formed if:
    1. The head has the appropriate category
    2. The complement (if present) is selected by the head
    3. Structure is binary branching -/
def XBarPhrase.isWellFormed (xp : XBarPhrase) : Bool :=
  -- Check head has correct category
  let headCatOk := match xp.head.getLIToken with
    | some tok => tok.item.outerCat == xp.cat
    | none => match getCategory xp.head with
      | some c => c == xp.cat
      | none => false
  -- Check complement is selected (if present)
  let compOk := match xp.complement with
    | none => true
    | some comp => selectsB xp.head comp
  headCatOk && compOk

-- Part 6: Converting to/from SyntacticObjects

/-- Build a SyntacticObject from an XBarPhrase

    Constructs the tree bottom-up:
    1. Head alone = X
    2. Head + Complement = X' (merge head with complement)
    3. X' + Specifier = XP (merge specifier with X') -/
def XBarPhrase.toSyntacticObject (xp : XBarPhrase) : SyntacticObject :=
  let xZero := xp.head
  let xBar := match xp.complement with
    | none => xZero
    | some comp => merge xZero comp
  match xp.specifier with
  | none => xBar
  | some spec => merge spec xBar

/-- Analyze a SyntacticObject as an X-Bar phrase -/
def analyzeAsXBar (so : SyntacticObject) : Option XBarPhrase :=
  match getCategory so with
  | none => none
  | some cat =>
    let head := getHead so
    let comp := getComplement so
    let spec := getSpecifier so
    match head with
    | none => none
    | some h => some {
        cat := cat
        head := h
        complement := comp
        specifier := spec
      }

-- Part 7: Theorems

/-- Selection determines complement position -/
theorem selection_gives_complement (h c : SyntacticObject)
    (hSel : selectsB h c = true) :
    getComplement (merge h c) = some c := by
  simp [getComplement, merge, selectsB] at *
  split <;> simp_all

/-- Heads are minimal (zero bar level) -/
theorem heads_are_minimal (tok : LIToken) :
    barLevelSimple (.leaf tok) = .zero := rfl

/-- Phrases built from specifier+X' are maximal -/
theorem spec_xbar_is_maximal (spec xbar : SyntacticObject)
    (hSpec : spec.isNode) :
    barLevelSimple (merge spec xbar) = .max := by
  simp only [SyntacticObject.isNode] at hSpec
  cases spec with
  | leaf _ => simp at hSpec
  | node a b =>
    simp only [barLevelSimple, merge, SyntacticObject.isLeaf]
    cases xbar <;> rfl

-- Part 8: Examples

/-- Example: Building "the cat" as a DP

    [D the] + [N cat] = [DP [D the] [N cat]]
    D selects N, so D projects -/
def exampleDP : XBarPhrase := {
  cat := .D
  head := .leaf ⟨.simple .D [.N], 1⟩  -- "the"
  complement := some (.leaf ⟨.simple .N [], 2⟩)  -- "cat"
  specifier := none
}

#eval exampleDP.isWellFormed  -- true

/-- Example: "John saw Mary" as a simple clause sketch

    V selects D (object), so in [V saw] + [D Mary]:
    V projects, making VP -/
def exampleVP : XBarPhrase := {
  cat := .V
  head := .leaf ⟨.simple .V [.D], 3⟩  -- "saw"
  complement := some (.leaf ⟨.simple .D [], 4⟩)  -- "Mary"
  specifier := none  -- Subject would be in Spec,vP or Spec,TP
}

#eval exampleVP.isWellFormed  -- true

end Minimalism
