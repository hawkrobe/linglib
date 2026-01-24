/-
# Labeling and Projection (Harizanov)

Formalization of labeling, projection, and the head/phrase distinction.

## Key Definitions

- **Label**: The categorial identity of an SO (Definition 16-17)
- **Projection**: When an LI's label becomes the label of containing SOs (Definition 20)
- **Maximality/Minimality**: Relational properties determined by projection (Definition 21)
- **Head vs Phrase**: Defined by maximality/minimality (Definition 22)

## The Core Insight

Harizanov's key observation is that maximality and minimality are RELATIONAL,
not intrinsic. An LI can be minimal in one structure but maximal in another.
This enables head movement to change an element's status.

## References

- Harizanov, B. "Syntactic Head Movement", Definitions 16-22
-/

import Linglib.Theories.Minimalism.Containment

namespace Minimalism.Harizanov

-- ============================================================================
-- Part 1: Selection
-- ============================================================================

/-- X selects Y iff X's outer sel stack starts with Y's category

    Selection is what triggers projection: the selector projects.
    When V[D] merges with DP, V selects D, so V projects. -/
def selects (selector selected : SyntacticObject) : Prop :=
  match selector.getLIToken, selected with
  | some tok, _ =>
    match tok.item.outerSel with
    | [] => False  -- nothing to select
    | c :: _ =>
      -- The selector's first selectional requirement must match
      -- the category of the selected element
      match selected.getLIToken with
      | some selTok => selTok.item.outerCat = c
      | none => False  -- For now, require selected to be LI
  | none, _ => False

-- ============================================================================
-- Part 2: Labels (Definition 16-17)
-- ============================================================================

/-- The label of an SO

    - For an LI token: its lexical item
    - For a set {X, Y}: the label of whichever element projects

    "The label of X is the label of the projecting element"

    Note: This is partial - not all SOs have a label (e.g., if neither
    element projects, as in certain symmetric structures) -/
def label : SyntacticObject → Option LexicalItem
  | .leaf tok => some tok.item
  | .node a _b =>
    -- The projecting element determines the label
    -- For now: the first element projects if it's an LI
    -- (Full implementation requires tracking selection)
    match a with
    | .leaf tok => some tok.item
    | .node _ _ => label a

/-- Two SOs have the same label -/
def sameLabel (x y : SyntacticObject) : Prop :=
  label x = label y ∧ label x ≠ none

-- ============================================================================
-- Part 3: Projection (Definition 20)
-- ============================================================================

/-- X projects in Y iff X's label = Y's label and X is immediately contained in Y

    "X projects in Y iff X is immediately contained in Y and
    the label of X is the label of Y"

    This captures the notion that X's categorial identity becomes
    the categorial identity of the larger structure Y. -/
def projectsIn (x y : SyntacticObject) : Prop :=
  immediatelyContains y x ∧ sameLabel x y

/-- X projects iff X projects in some containing SO -/
def projects (x root : SyntacticObject) : Prop :=
  ∃ y, containsOrEq root y ∧ projectsIn x y

-- ============================================================================
-- Part 4: Maximality and Minimality (Definition 21)
-- ============================================================================

/-- X is minimal in Y iff X is a term of Y and X doesn't project in anything in Y

    "X is +minimal in Y iff X is a term of Y and there is no Z such that
    Z is a term of Y and X projects in Z"

    Intuitively: nothing in Y has X's label as a result of X projecting. -/
def isMinimalIn (x y : SyntacticObject) : Prop :=
  isTermOf x y ∧ ¬∃ z, isTermOf z y ∧ projectsIn x z

/-- X is maximal in Y iff X is a term of Y and nothing in Y projects into X

    "X is +maximal in Y iff X is a term of Y and there is no Z such that
    Z is a term of Y and Z projects in X and Z ≠ X"

    Intuitively: X's label is not "inherited" from a projecting element inside it. -/
def isMaximalIn (x y : SyntacticObject) : Prop :=
  isTermOf x y ∧ ¬∃ z, isTermOf z y ∧ projectsIn z x ∧ z ≠ x

-- ============================================================================
-- Part 5: Heads and Phrases (Definition 22)
-- ============================================================================

/-- A head in Y: +minimal, -maximal

    "X is a head in Y iff X is +minimal and -maximal in Y"

    Heads project but are not themselves projections of something larger.
    They are "at the bottom" of a projection chain. -/
def isHeadIn (x y : SyntacticObject) : Prop :=
  isMinimalIn x y ∧ ¬isMaximalIn x y

/-- A phrase in Y: +maximal

    "X is a phrase in Y iff X is +maximal in Y"

    Phrases are projections that have "topped out" - they don't project further.
    Minimality is irrelevant for phrasehood. -/
def isPhraseIn (x y : SyntacticObject) : Prop :=
  isMaximalIn x y

/-- X-bar level: +minimal, +maximal

    Not a head (would need -maximal) and not necessarily a phrase in the
    traditional sense. These are intermediate projections. -/
def isIntermediateIn (x y : SyntacticObject) : Prop :=
  isMinimalIn x y ∧ isMaximalIn x y

-- ============================================================================
-- Part 6: Key Theorem: LI Tokens are Minimal
-- ============================================================================

/-- An LI token is always minimal in any containing structure

    Reasoning: LI tokens don't contain anything, so they can't have
    anything project into them. And they don't project "in" themselves. -/
theorem li_token_minimal (tok : LIToken) (root : SyntacticObject)
    (h : isTermOf (.leaf tok) root) :
    isMinimalIn (.leaf tok) root := by
  constructor
  · exact h
  · intro ⟨z, _, hproj⟩
    -- x projects in z means z immediately contains x
    obtain ⟨himm, _⟩ := hproj
    -- But z immediately containing leaf tok means z = node _ _
    -- and then leaf tok would need to be contained, but we showed
    -- leaf_contains_nothing, which is about contains not immediatelyContains
    -- Actually immediatelyContains is fine here
    cases z with
    | leaf _ => simp [immediatelyContains] at himm
    | node a b =>
      -- This is fine - the leaf can be immediately contained
      -- The issue is whether the leaf "projects in" z
      -- For a leaf to project in z, we need sameLabel (leaf tok) z
      -- which requires label z = some tok.item
      -- This can happen if z's label comes from the leaf
      sorry  -- Need more careful tracking of projection

-- ============================================================================
-- Part 7: Projection Chains
-- ============================================================================

/-- A projection chain is a sequence of SOs where each projects in the next -/
def ProjectionChain : List SyntacticObject → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => projectsIn x y ∧ ProjectionChain (y :: rest)

/-- The head of a projection chain -/
def chainHead : List SyntacticObject → Option SyntacticObject
  | [] => none
  | x :: _ => some x

/-- The maximal projection of a chain -/
def chainMax : List SyntacticObject → Option SyntacticObject
  | [] => none
  | [x] => some x
  | _ :: rest => chainMax rest

-- ============================================================================
-- Part 8: Specifier, Complement, Adjunct
-- ============================================================================

/-- X is a specifier in Y iff X is a phrase immediately contained in Y
    and X's sister projects

    Specifiers are maximal projections that are sisters to projecting heads. -/
def isSpecifierIn (x y root : SyntacticObject) : Prop :=
  isPhraseIn x root ∧ immediatelyContains y x ∧
  ∃ z, immediatelyContains y z ∧ z ≠ x ∧ projectsIn z y

/-- X is a complement of Y iff X is selected by Y

    Complements satisfy selectional requirements. -/
def isComplementOf (comp head : SyntacticObject) : Prop :=
  selects head comp

-- ============================================================================
-- Part 9: The Critical Insight: Maximality is Relational
-- ============================================================================

/-
## Why Maximality Matters for Head Movement

Harizanov's key insight: The same LI can be:
- A HEAD in one position: +min, -max (projects further up)
- A PHRASE in another position: +max (does not project)

When a head X moves:
- **Head-to-specifier**: X becomes +max in the new position (a phrase)
- **Head-to-head**: X remains -max (reprojects, stays a head)

This relational view explains:
1. How head movement changes syntactic status
2. Why head-to-head requires complex LIs (for reprojection)
3. The interpretive differences between movement types
-/

/-- An element's maximality can differ between positions

    This is the formalization of Harizanov's key insight. -/
theorem maximality_is_relational :
    ∃ (x : SyntacticObject) (y z : SyntacticObject),
      isMaximalIn x y ∧ ¬isMaximalIn x z := by
  sorry  -- Constructive proof requires building specific structures

end Minimalism.Harizanov
