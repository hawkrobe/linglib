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
-- Part 1: Getting Categories from SOs
-- ============================================================================

/-- Helper: does sel stack contain category? -/
def selContains (sel : SelStack) (c : Cat) : Bool :=
  sel.any (· == c)

/-- Helper: check if option cat matches any in sel stack -/
def selMatchesOpt (sel : SelStack) (oc : Option Cat) : Bool :=
  match oc with
  | some c => selContains sel c
  | none => false

/-- Get the category of an SO by finding the projecting head
    This must match the logic in `label` -/
partial def getCategory (so : SyntacticObject) : Option Cat :=
  match so with
  | .leaf tok => some tok.item.outerCat
  | .node a b =>
    match a.getLIToken with
    | some tokA =>
      match b.getLIToken with
      | some tokB =>
        -- Both leaves: check selection
        if selContains tokA.item.outerSel tokB.item.outerCat then
          some tokA.item.outerCat
        else if selContains tokB.item.outerSel tokA.item.outerCat then
          some tokB.item.outerCat
        else if tokA.item.outerSel.isEmpty && !tokB.item.outerSel.isEmpty then
          some tokB.item.outerCat
        else
          some tokA.item.outerCat
      | none =>
        -- a is leaf, b is phrase
        let bCat := getCategory b
        if selMatchesOpt tokA.item.outerSel bCat then
          some tokA.item.outerCat  -- a selects b → a projects
        else
          bCat  -- specifier-head: phrase projects (a doesn't select b)
    | none =>
      match b.getLIToken with
      | some tokB =>
        -- a is phrase, b is leaf
        let aCat := getCategory a
        if selMatchesOpt tokB.item.outerSel aCat then
          some tokB.item.outerCat  -- b selects a → b projects
        else
          aCat  -- specifier-head: phrase projects (b doesn't select a)
      | none =>
        -- Both phrases - prefer second (complement position typically)
        let bCat := getCategory b
        match bCat with
        | some _ => bCat
        | none => getCategory a

/-- Get the LI of an SO (the projecting head) -/
partial def getProjectingLI (so : SyntacticObject) : Option LexicalItem :=
  match so with
  | .leaf tok => some tok.item
  | .node a b =>
    match a.getLIToken with
    | some tokA =>
      match b.getLIToken with
      | some tokB =>
        if selContains tokA.item.outerSel tokB.item.outerCat then some tokA.item
        else if selContains tokB.item.outerSel tokA.item.outerCat then some tokB.item
        else if tokA.item.outerSel.isEmpty && !tokB.item.outerSel.isEmpty then some tokB.item
        else some tokA.item
      | none =>
        let bCat := getCategory b
        if selMatchesOpt tokA.item.outerSel bCat then some tokA.item
        else getProjectingLI b  -- specifier-head: phrase projects
    | none =>
      match b.getLIToken with
      | some tokB =>
        let aCat := getCategory a
        if selMatchesOpt tokB.item.outerSel aCat then some tokB.item
        else getProjectingLI a  -- specifier-head: phrase projects
      | none =>
        match getProjectingLI b with
        | some li => some li
        | none => getProjectingLI a

-- ============================================================================
-- Part 2: Selection (Decidable)
-- ============================================================================

/-- X selects Y iff X's selectional requirements include Y's category

    Selection is what triggers projection: the selector projects.
    When V[D] merges with DP, V selects D, so V projects. -/
def selectsB (selector selected : SyntacticObject) : Bool :=
  match selector.getLIToken with
  | some tok =>
    match tok.item.outerSel, getCategory selected with
    | c :: _, some selCat => c == selCat
    | _, _ => false
  | none =>
    -- selector is a phrase - check its head's selection
    match getProjectingLI selector with
    | some li =>
      match li.outerSel, getCategory selected with
      | c :: _, some selCat => c == selCat
      | _, _ => false
    | none => false

/-- Propositional version of selection -/
def selects (selector selected : SyntacticObject) : Prop :=
  selectsB selector selected = true

instance (x y : SyntacticObject) : Decidable (selects x y) :=
  inferInstanceAs (Decidable (selectsB x y = true))

-- ============================================================================
-- Part 3: Labels (Definition 16-17) - Selection-Based
-- ============================================================================

/-- The label of an SO - determined by which element projects

    - For an LI token: its lexical item
    - For a set {X, Y}: the label of whichever element selects the other

    "The label of X is the label of the projecting element" -/
def label : SyntacticObject → Option LexicalItem
  | .leaf tok => some tok.item
  | .node a b =>
    -- The selector projects
    if selectsB a b then label a
    else if selectsB b a then label b
    else
      -- Neither selects directly. This happens in specifier-head structures.
      -- Try to find which one is the "head" (has selectional features remaining)
      match a.getLIToken, b.getLIToken with
      | some tokA, some tokB =>
        -- Both are leaves - the one with selectional features projects
        if tokA.item.outerSel.isEmpty && !tokB.item.outerSel.isEmpty then
          some tokB.item  -- b is the head
        else
          some tokA.item  -- default: a projects
      | some _tok, none =>
        -- a is leaf, b is phrase: phrase projects (specifier-head)
        -- The leaf is a specifier unless it selects the phrase
        label b
      | none, some _tok =>
        -- a is phrase, b is leaf: phrase projects (specifier-head)
        -- The leaf is a specifier unless it selects the phrase
        label a
      | none, none =>
        -- Both are phrases - recurse on both, prefer the one with sel features
        match label a, label b with
        | some liA, some liB =>
          if liA.outerSel.isEmpty && !liB.outerSel.isEmpty then some liB
          else some liA
        | some li, none => some li
        | none, some li => some li
        | none, none => none

/-- Get the category from the label -/
def labelCat (so : SyntacticObject) : Option Cat :=
  (label so).map (·.outerCat)

/-- Two SOs have the same label -/
def sameLabel (x y : SyntacticObject) : Prop :=
  label x = label y ∧ label x ≠ none

def sameLabelB (x y : SyntacticObject) : Bool :=
  match label x, label y with
  | some lx, some ly => lx.features == ly.features
  | _, _ => false

instance (x y : SyntacticObject) : Decidable (sameLabel x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ============================================================================
-- Part 4: Projection (Definition 20)
-- ============================================================================

/-- X projects in Y iff X's label = Y's label and X is immediately contained in Y -/
def projectsIn (x y : SyntacticObject) : Prop :=
  immediatelyContains y x ∧ sameLabel x y

def projectsInB (x y : SyntacticObject) : Bool :=
  match y with
  | .leaf _ => false
  | .node a b => (x == a || x == b) && sameLabelB x y

instance (x y : SyntacticObject) : Decidable (projectsIn x y) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- X projects iff X projects in some containing SO -/
def projects (x root : SyntacticObject) : Prop :=
  ∃ y, containsOrEq root y ∧ projectsIn x y

-- ============================================================================
-- Part 5: Maximality and Minimality (Definition 21)
-- ============================================================================

/-- X is minimal in Y iff X is a term of Y and X doesn't contain anything

    From Harizanov: "A head is thus a strictly minimal element, one that
    does not contain anything (and is therefore an LI)"

    +min = is a leaf/LI -/
def isMinimalIn (x y : SyntacticObject) : Prop :=
  isTermOf x y ∧
  match x with
  | .leaf _ => True
  | .node _ _ => False

/-- X is maximal in Y iff X is a term of Y and X doesn't project in anything in Y

    +max = X is at the top of its projection chain (nothing contains X with same label)

    From Harizanov: a phrase is +max, meaning it's a maximal projection -/
def isMaximalIn (x y : SyntacticObject) : Prop :=
  isTermOf x y ∧ ¬∃ z, isTermOf z y ∧ projectsIn x z

-- ============================================================================
-- Part 6: Heads and Phrases (Definition 22)
-- ============================================================================

/-- A head in Y: +minimal AND -maximal

    From Harizanov (22b): "A head is an SO that is both +min and −max"

    This means: X is an LI (doesn't contain anything) AND X projects
    (is contained by something with same label).

    Footnote: "a head is an LI which projects" -/
def isHeadIn (x y : SyntacticObject) : Prop :=
  isMinimalIn x y ∧ ¬isMaximalIn x y

/-- A phrase in Y: +maximal

    From Harizanov (22a): "A phrase is an SO that is +max (and ±min)"

    A phrase is a maximal projection - at the top of its projection chain. -/
def isPhraseIn (x y : SyntacticObject) : Prop :=
  isMaximalIn x y

/-- An LI that doesn't project: +minimal AND +maximal

    This is an LI that is simultaneously at the bottom (is a leaf)
    and top (doesn't project) of its chain. Not a "head" per (22b). -/
def isNonProjectingLI (x y : SyntacticObject) : Prop :=
  isMinimalIn x y ∧ isMaximalIn x y

-- ============================================================================
-- Part 7: Concrete Examples for Testing
-- ============================================================================

/-- A verb "eat" that selects D (needs an object) -/
def verbEat : LIToken := ⟨.simple .V [.D], 1⟩

/-- A noun "pizza" with no selectional requirements -/
def nounPizza : LIToken := ⟨.simple .N [], 2⟩

/-- A determiner "the" that selects N -/
def detThe : LIToken := ⟨.simple .D [.N], 3⟩

/-- Build: [D the] merges with [N pizza] → D projects (D selects N) -/
def theDP : SyntacticObject := .node (.leaf detThe) (.leaf nounPizza)

#eval selectsB (.leaf detThe) (.leaf nounPizza)  -- true: D selects N
#eval labelCat theDP  -- some .D (the determiner projects)

/-- Build: [V eat] merges with [DP the pizza] → V projects (V selects D) -/
def eatPizzaVP : SyntacticObject := .node (.leaf verbEat) theDP

#eval selectsB (.leaf verbEat) theDP  -- true: V selects D
#eval labelCat eatPizzaVP  -- some .V (the verb projects)

-- ============================================================================
-- Part 8: Understanding Min/Max with Examples
-- ============================================================================

/-
## How Minimality and Maximality Work (Corrected)

From Harizanov's text:
- **+minimal**: "does not contain anything (and is therefore an LI)" = is a leaf
- **+maximal**: doesn't project (nothing contains it with same label)
- **Head (22b)**: +min AND -max = "an LI which projects"
- **Phrase (22a)**: +max (and ±min) = maximal projection

Given the definitions:
- X projects in Z ⟺ Z immediately contains X AND label(X) = label(Z)
- +minimal: X is a leaf (doesn't contain anything)
- +maximal: X doesn't project in anything (top of projection chain)

For our example structures:

**theDP = {D, N}** where D selects N, so D projects:
- label(theDP) = D's LI
- D projects in theDP (theDP contains D, same label)

Status of D in theDP:
- D is a leaf → D is +minimal
- D projects in theDP → D is -maximal
- D: +min, -max = HEAD ✓

Status of theDP in theDP:
- theDP is a node → theDP is -minimal
- theDP doesn't project in anything (it's the root) → theDP is +maximal
- theDP: -min, +max = PHRASE ✓

**eatPizzaVP = {V, theDP}** where V selects D, so V projects:
- label(eatPizzaVP) = V's LI

Status of V in eatPizzaVP:
- V is a leaf → V is +minimal
- V projects in eatPizzaVP → V is -maximal
- V: +min, -max = HEAD ✓

**Summary Table:**
| Element    | +min?        | +max?           | Status  |
|------------|--------------|-----------------|---------|
| Leaf (LI)  | Yes (leaf)   | No (projects)   | HEAD    |
| Phrase     | No (node)    | Yes (top)       | PHRASE  |
| Non-proj LI| Yes (leaf)   | Yes (no proj)   | ±min,+max |

The key insight: a HEAD is an LI that projects. A PHRASE is a maximal projection.
-/

-- Verify with computation
#eval projectsInB (.leaf detThe) theDP        -- true: D projects in DP
#eval projectsInB (.leaf nounPizza) theDP     -- false: N doesn't project
#eval projectsInB (.leaf verbEat) eatPizzaVP  -- true: V projects in VP
#eval projectsInB theDP eatPizzaVP            -- false: DP doesn't project in VP

-- ============================================================================
-- Part 9: Position-Indexed Maximality (Collins & Stabler 2016)
-- ============================================================================

/-
## Position vs Occurrence (Harizanov footnote 11, p.9)

Following Collins & Stabler (2016), a POSITION is a path from the root to
an element. An OCCURRENCE is a pair of (element, position).

In multidominant structures (copy theory), the same element can appear at
multiple positions with DIFFERENT maximality properties:
- At Spec-CP: verb is maximal (doesn't project there)
- At VP: verb projects (not maximal there)

The global `isMaximalIn` checks ALL positions. For head-to-specifier movement,
we need position-specific maximality: the element is maximal AT ITS DERIVED POSITION.
-/

/-- A position in a tree: path from root to an element.
    `here` = at this node
    `left p` = go left, then follow p
    `right p` = go right, then follow p -/
inductive TreePos where
  | here : TreePos
  | left : TreePos → TreePos
  | right : TreePos → TreePos
  deriving Repr, DecidableEq

/-- Get the SO at a given position (if it exists) -/
def atPosition : SyntacticObject → TreePos → Option SyntacticObject
  | so, .here => some so
  | .leaf _, .left _ => none
  | .leaf _, .right _ => none
  | .node a _, .left p => atPosition a p
  | .node _ b, .right p => atPosition b p

/-- The parent position (one step up toward root) -/
def parentPos : TreePos → Option TreePos
  | .here => none
  | .left p => some p
  | .right p => some p

/-- Get the parent SO of a position -/
def parentSO (root : SyntacticObject) (pos : TreePos) : Option SyntacticObject :=
  match parentPos pos with
  | none => none
  | some pp => atPosition root pp

/-- Get the sibling SO at a position -/
def siblingSO (root : SyntacticObject) (pos : TreePos) : Option SyntacticObject :=
  match parentSO root pos with
  | none => none
  | some parent =>
    match parent with
    | .leaf _ => none
    | .node a b =>
      match pos with
      | .here => none  -- root has no sibling
      | .left _ => some b  -- if we went left, sibling is right
      | .right _ => some a  -- if we went right, sibling is left

/-- X projects AT POSITION p in root iff:
    - X is at position p
    - The parent at p has the same label as X

    This is position-specific: checks projection only at this occurrence -/
def projectsAtPosition (x root : SyntacticObject) (pos : TreePos) : Prop :=
  atPosition root pos = some x ∧
  match parentSO root pos with
  | none => False  -- root cannot project (nothing contains it)
  | some parent => sameLabel x parent

/-- X is maximal AT POSITION p in root iff:
    - X is at position p
    - X does NOT project at position p (parent has different label or is root)

    This captures Harizanov's "maximal in its derived position" -/
def isMaximalAtPosition (x root : SyntacticObject) (pos : TreePos) : Prop :=
  atPosition root pos = some x ∧
  ¬projectsAtPosition x root pos

/-- X is a specifier at position p iff:
    - X is at position p
    - X is maximal at p (doesn't project)
    - X's sibling DOES project (the sibling is the "head" of the phrase) -/
def isSpecifierAtPosition (x root : SyntacticObject) (pos : TreePos) : Prop :=
  isMaximalAtPosition x root pos ∧
  match siblingSO root pos with
  | none => False
  | some sib =>
    match parentSO root pos with
    | none => False
    | some parent => sameLabel sib parent

/-- Find positions where x occurs in root -/
def findPositions (x root : SyntacticObject) : List TreePos :=
  let rec go (so : SyntacticObject) (pos : TreePos) (acc : List TreePos) : List TreePos :=
    let acc' := if so == x then pos :: acc else acc
    match so with
    | .leaf _ => acc'
    | .node a b => go b (.right pos) (go a (.left pos) acc')
  go root .here []

/-- The derived position in head-to-specifier movement is the specifier position.
    In {X, Y} where Y is the target (projects), X is at the LEFT (Spec) position -/
def derivedSpecPosition : TreePos := .left .here

end Minimalism.Harizanov
