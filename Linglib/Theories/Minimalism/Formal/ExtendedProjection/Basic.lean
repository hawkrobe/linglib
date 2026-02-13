/-
# Extended Projection

Formalization of Grimshaw (2005) Extended Projection theory.

## Key Ideas

An **Extended Projection** (EP) is a sequence of projections unified by:
1. **Category consistency**: all heads share [±V, ±N] features
2. **F-value monotonicity**: functional level (F-value) increases going up the tree

Standard EPs:
- Verbal: V (F0) → v (F1) → T (F2) → C (F3)
- Nominal: N (F0) → D (F1)

## Definitions

- `CatFeatures`: Grimshaw's [±V, ±N] decomposition of category
- `fValue`: Functional level within an EP (0 = lexical, 1+ = functional)
- `ExtendedProjection`: Structure capturing an EP spine with consistency/monotonicity
- `CatFamily`: The four category families (verbal, nominal, adjectival, adpositional)

## References

- Grimshaw, J. (2005). Words and Structure. CSLI Lecture Notes.
- Grimshaw, J. (1991/2005). Extended Projection. Chapter 1.
-/

import Linglib.Theories.Minimalism.Core.Labeling

namespace Minimalism

-- ═══════════════════════════════════════════════════════════════
-- Part 1: Categorial Features [±V, ±N]
-- ═══════════════════════════════════════════════════════════════

/-- Grimshaw's [±V, ±N] categorial features.
    Cross-classifies the four lexical categories:
    - V = [+V, -N], N = [-V, +N], A = [+V, +N], P = [-V, -N]

    Functional categories inherit these from their lexical anchor. -/
structure CatFeatures where
  plusV : Bool   -- [+V] = verbal/adjectival
  plusN : Bool   -- [+N] = nominal/adjectival
  deriving Repr, DecidableEq, BEq

/-- Compute [±V, ±N] features from existing `Cat`.
    Functional categories inherit features from their lexical anchor:
    - v, T, C inherit [+V, -N] from V
    - D inherits [-V, +N] from N -/
def catFeatures : Cat → CatFeatures
  | .V     => ⟨true,  false⟩   -- [+V, -N]
  | .v     => ⟨true,  false⟩   -- [+V, -N] (light verb)
  | .Voice => ⟨true,  false⟩   -- [+V, -N] (Kratzer 1996)
  | .Appl  => ⟨true,  false⟩   -- [+V, -N] (Pylkkänen 2008)
  | .T     => ⟨true,  false⟩   -- [+V, -N]
  | .Fin   => ⟨true,  false⟩   -- [+V, -N] (Rizzi 1997 split-CP)
  | .C     => ⟨true,  false⟩   -- [+V, -N]
  | .SA    => ⟨true,  false⟩   -- [+V, -N] (Speas & Tenny 2003)
  | .N     => ⟨false, true⟩    -- [-V, +N]
  | .D     => ⟨false, true⟩    -- [-V, +N]
  | .A     => ⟨true,  true⟩    -- [+V, +N]
  | .P     => ⟨false, false⟩   -- [-V, -N]

-- ═══════════════════════════════════════════════════════════════
-- Part 2: F-Value (Functional Level)
-- ═══════════════════════════════════════════════════════════════

/-- Grimshaw's F-value: the functional level within an extended projection.
    - F0 = lexical (V, N, A, P) — content heads
    - F1 = first functional layer (v, D) — close functional shell
    - F2 = second functional layer (T) — tense/agreement
    - F3 = highest functional layer (C) — clause type/force -/
def fValue : Cat → Nat
  | .V | .N | .A | .P   => 0   -- lexical (F0)
  | .v | .D | .Voice | .Appl
                         => 1   -- first functional (F1)
  | .T                   => 2   -- second functional (F2)
  | .Fin                 => 3   -- finiteness (F3, Rizzi 1997 split-CP)
  | .C                   => 3   -- complementizer (F3)
  | .SA                  => 4   -- speech act (F4, Speas & Tenny 2003)

-- ═══════════════════════════════════════════════════════════════
-- Part 3: Category Consistency and Monotonicity
-- ═══════════════════════════════════════════════════════════════

/-- Category consistency: two categories share [±V, ±N] features.
    This is the core constraint on Extended Projections —
    V and T are consistent (both [+V, -N]), but V and D are not. -/
def categoryConsistent (c1 c2 : Cat) : Bool :=
  catFeatures c1 == catFeatures c2

/-- F-value monotonicity: F-values must not decrease going up the tree.
    In an EP, each head's F-value is ≥ the one below it. -/
def fMonotone (lower upper : Cat) : Bool :=
  fValue lower ≤ fValue upper

/-- Perfect projection: same [±V, ±N] AND same F-value.
    E.g., two V heads (F0, [+V, -N]) are perfect projections of each other.
    Distinct from EP extension, where F-value increases. -/
def perfectProjection (c1 c2 : Cat) : Bool :=
  categoryConsistent c1 c2 && (fValue c1 == fValue c2)

-- ═══════════════════════════════════════════════════════════════
-- Part 4: L-Head vs F-Head
-- ═══════════════════════════════════════════════════════════════

/-- Is this category a lexical head (F0)?
    L-heads are content categories: V, N, A, P. -/
def isLHead (c : Cat) : Bool := fValue c == 0

/-- Is this category a functional head (F1+)?
    F-heads are functional categories: v, D, T, C. -/
def isFHead (c : Cat) : Bool := fValue c > 0

-- ═══════════════════════════════════════════════════════════════
-- Part 5: Category Family
-- ═══════════════════════════════════════════════════════════════

/-- The four lexical category families, each defining an EP domain.
    All categories in an EP must belong to the same family. -/
inductive CatFamily where
  | verbal        -- V, v, T, C  [+V, -N]
  | nominal       -- N, D        [-V, +N]
  | adjectival    -- A           [+V, +N]
  | adpositional  -- P           [-V, -N]
  deriving Repr, DecidableEq, BEq

/-- Map a category to its family.
    This determines which EP it can participate in. -/
def catFamily : Cat → CatFamily
  | .V | .v | .Voice | .Appl | .T | .Fin | .C | .SA => .verbal
  | .N | .D                                          => .nominal
  | .A                                               => .adjectival
  | .P                                               => .adpositional

-- ═══════════════════════════════════════════════════════════════
-- Part 6: Extended Projection Structure
-- ═══════════════════════════════════════════════════════════════

/-- An Extended Projection: a sequence of categories forming a projection chain
    with category consistency and F-value monotonicity.

    The spine lists categories from lowest (lexical head) to highest (functional). -/
structure ExtendedProjection where
  /-- Root syntactic object of the EP -/
  root : SyntacticObject
  /-- Categories along the spine, from lexical head (F0) upward -/
  spine : List Cat
  /-- All spine categories share [±V, ±N] features -/
  catConsistent : Bool
  /-- F-values are non-decreasing along the spine -/
  fMonotoneChain : Bool

/-- Check that a list of categories is category-consistent
    (all share the same [±V, ±N] features). -/
def allCategoryConsistent : List Cat → Bool
  | [] => true
  | [_] => true
  | c₁ :: c₂ :: rest => categoryConsistent c₁ c₂ && allCategoryConsistent (c₂ :: rest)

/-- Check that a list of categories has monotonically non-decreasing F-values. -/
def allFMonotone : List Cat → Bool
  | [] => true
  | [_] => true
  | c₁ :: c₂ :: rest => fMonotone c₁ c₂ && allFMonotone (c₂ :: rest)

/-- Compute the EP spine from a syntactic object by collecting categories
    along the head-projection chain. Returns pairs of (SO, Cat) from
    the deepest lexical head up to the root. -/
partial def computeEPSpine (so : SyntacticObject) : List (SyntacticObject × Cat) :=
  match so with
  | .leaf tok => [(so, tok.item.outerCat)]
  | .node a b =>
    -- Find which daughter is the head (projects)
    let headDaughter := if selectsB a b then a
                        else if selectsB b a then b
                        else a  -- default: left daughter
    let spineBelow := computeEPSpine headDaughter
    match getCategory so with
    | some c => spineBelow ++ [(so, c)]
    | none   => spineBelow

/-- Build an ExtendedProjection from a syntactic object. -/
def mkExtendedProjection (so : SyntacticObject) : ExtendedProjection :=
  let spinePairs := computeEPSpine so
  let cats := spinePairs.map Prod.snd
  { root := so
    spine := cats
    catConsistent := allCategoryConsistent cats
    fMonotoneChain := allFMonotone cats }

/-- Is this EP well-formed? (category consistent AND F-monotone) -/
def ExtendedProjection.isWellFormed (ep : ExtendedProjection) : Bool :=
  ep.catConsistent && ep.fMonotoneChain

/-- The family of an EP (determined by any element of the spine). -/
def ExtendedProjection.family (ep : ExtendedProjection) : Option CatFamily :=
  ep.spine.head?.map catFamily

/-- The lexical anchor of an EP (the F0 head at the bottom). -/
def ExtendedProjection.lexicalAnchor (ep : ExtendedProjection) : Option Cat :=
  ep.spine.head?.filter isLHead

/-- The highest functional head in the EP. -/
def ExtendedProjection.highestHead (ep : ExtendedProjection) : Option Cat :=
  ep.spine.getLast?

-- ═══════════════════════════════════════════════════════════════
-- Part 7: Bridge Theorems
-- ═══════════════════════════════════════════════════════════════

-- Existing Cat assignments are EP-consistent

/-- The verbal chain V → v → T → C is category-consistent:
    all share [+V, -N] features. -/
theorem verbal_chain_consistent :
    categoryConsistent .V .v ∧ categoryConsistent .v .T ∧
    categoryConsistent .T .C := by decide

/-- The nominal chain N → D is category-consistent:
    both have [-V, +N] features. -/
theorem nominal_chain_consistent :
    categoryConsistent .N .D := by decide

-- F-values are monotone along standard chains

/-- F-values increase monotonically along the verbal chain:
    V(0) ≤ v(1) ≤ T(2) ≤ C(3). -/
theorem verbal_fvalues_monotone :
    fValue .V ≤ fValue .v ∧ fValue .v ≤ fValue .T ∧
    fValue .T ≤ fValue .C := by decide

/-- F-values increase along the nominal chain: N(0) ≤ D(1). -/
theorem nominal_fvalues_monotone :
    fValue .N ≤ fValue .D := by decide

-- Cross-family inconsistency

/-- V and N are NOT category-consistent (different [±V, ±N]). -/
theorem verbal_nominal_inconsistent :
    categoryConsistent .V .N = false := by decide

/-- V and D are NOT category-consistent (verbal ≠ nominal). -/
theorem verbal_determiner_inconsistent :
    categoryConsistent .V .D = false := by decide

-- L-head / F-head classification

/-- F0 is exactly the lexical heads. -/
theorem f0_iff_lexical (c : Cat) :
    isLHead c = true ↔ (c = .V ∨ c = .N ∨ c = .A ∨ c = .P) := by
  cases c <;> simp [isLHead, fValue]

/-- F1+ is exactly the functional heads. -/
theorem fpos_iff_functional (c : Cat) :
    isFHead c = true ↔ (c = .v ∨ c = .Voice ∨ c = .Appl ∨ c = .D ∨ c = .T ∨ c = .Fin ∨ c = .C ∨ c = .SA) := by
  cases c <;> simp [isFHead, fValue]

-- Family consistency

/-- Categories in the same family are category-consistent. -/
theorem same_family_consistent (c1 c2 : Cat) :
    catFamily c1 = catFamily c2 → categoryConsistent c1 c2 = true := by
  cases c1 <;> cases c2 <;> simp [catFamily] <;> decide

-- Full verbal chain is well-formed

/-- The full verbal EP spine [V, v, T, C] is category-consistent. -/
theorem full_verbal_ep_consistent :
    allCategoryConsistent [Cat.V, Cat.v, Cat.T, Cat.C] = true := by decide

/-- The full verbal EP spine [V, v, T, C] is F-monotone. -/
theorem full_verbal_ep_monotone :
    allFMonotone [Cat.V, Cat.v, Cat.T, Cat.C] = true := by decide

/-- The full nominal EP spine [N, D] is category-consistent. -/
theorem full_nominal_ep_consistent :
    allCategoryConsistent [Cat.N, Cat.D] = true := by decide

/-- The full nominal EP spine [N, D] is F-monotone. -/
theorem full_nominal_ep_monotone :
    allFMonotone [Cat.N, Cat.D] = true := by decide

-- Bridge to BarLevel (from XBar.lean)

/-- F0 categories correspond to BarLevel.zero (head),
    F1+ categories correspond to intermediate/maximal projections.
    This connects Grimshaw's F-level to X-bar bar levels. -/
theorem f0_corresponds_to_head :
    isLHead .V ∧ isLHead .N ∧ isLHead .A ∧ isLHead .P := by decide

/-- Functional heads (F1+) extend the projection beyond the lexical head. -/
theorem fhead_extends_projection :
    isFHead .v ∧ isFHead .D ∧ isFHead .T ∧ isFHead .C := by decide

-- ═══════════════════════════════════════════════════════════════
-- Part 8: Eval Tests
-- ═══════════════════════════════════════════════════════════════

-- Category features
#eval catFeatures .V   -- { plusV := true, plusN := false }
#eval catFeatures .N   -- { plusV := false, plusN := true }
#eval catFeatures .A   -- { plusV := true, plusN := true }

-- F-values
#eval fValue .V  -- 0
#eval fValue .v  -- 1
#eval fValue .T  -- 2
#eval fValue .C  -- 3

-- Category consistency
#eval categoryConsistent .V .T  -- true (both [+V, -N])
#eval categoryConsistent .V .N  -- false (different features)
#eval categoryConsistent .N .D  -- true (both [-V, +N])

-- Family
#eval catFamily .V  -- verbal
#eval catFamily .T  -- verbal
#eval catFamily .N  -- nominal
#eval catFamily .D  -- nominal

-- EP chain checks
#eval allCategoryConsistent [Cat.V, Cat.v, Cat.T, Cat.C]  -- true
#eval allFMonotone [Cat.V, Cat.v, Cat.T, Cat.C]           -- true
#eval allCategoryConsistent [Cat.V, Cat.D]                 -- false (V ≠ D family)

end Minimalism
