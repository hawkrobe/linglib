import Linglib.Core.Relativization.Basic

/-!
# Accessibility Hierarchy: Ordering and Contiguity
@cite{keenan-comrie-1977}

Defines the rank function and contiguity predicate for the Accessibility
Hierarchy. Mirrors `Core.Case.Hierarchy` for Blake's case hierarchy.
-/

namespace Core

-- ============================================================================
-- § 1: Rank
-- ============================================================================

/-- Numeric rank of a position on the Accessibility Hierarchy.
    Higher rank = more accessible = more languages can relativize it. -/
def AHPosition.rank : AHPosition → Nat
  | .subject        => 6
  | .directObject   => 5
  | .indirectObject => 4
  | .oblique        => 3
  | .genitive       => 2
  | .objComparison  => 1

/-- Position p1 is at least as accessible as p2 on the hierarchy. -/
def AHPosition.atLeastAsAccessible (p1 p2 : AHPosition) : Prop :=
  p1.rank ≥ p2.rank

instance (p1 p2 : AHPosition) : Decidable (p1.atLeastAsAccessible p2) :=
  inferInstanceAs (Decidable (_ ≥ _))

/-- Position p1 is strictly more accessible than p2. -/
def AHPosition.moreAccessible (p1 p2 : AHPosition) : Prop :=
  p1.rank > p2.rank

instance (p1 p2 : AHPosition) : Decidable (p1.moreAccessible p2) :=
  inferInstanceAs (Decidable (_ > _))

/-- All AH positions in descending order of accessibility. -/
def AHPosition.all : List AHPosition :=
  [.subject, .directObject, .indirectObject, .oblique, .genitive, .objComparison]

-- ============================================================================
-- § 2: Contiguity Predicate
-- ============================================================================

/-- Whether a list of AH positions contains at least one position at rank r. -/
def hasAHRank (positions : List AHPosition) (r : Nat) : Bool :=
  positions.any fun p => p.rank == r

/-- A set of AH positions forms a contiguous segment on the hierarchy:
    for every pair of positions in the set, all intermediate ranks
    are also represented.

    Mirrors `Core.validInventory` for the case hierarchy (@cite{blake-1994}).

    This formalizes HC₂ of @cite{keenan-comrie-1977}: "Any RC-forming
    strategy must apply to a continuous segment of the AH." -/
def contiguousOnAH (positions : List AHPosition) : Bool :=
  positions.all fun p1 =>
    positions.all fun p2 =>
      if p2.rank > p1.rank then
        let lo := p1.rank
        let hi := p2.rank
        List.range hi |>.all fun r =>
          if r > lo && r < hi then hasAHRank positions r
          else true
      else true

/-- A marker's positions form a contiguous segment of the AH. -/
def RelClauseMarker.isContinuous (m : RelClauseMarker) : Bool :=
  contiguousOnAH m.positions

-- ============================================================================
-- § 3: Ordering Theorems
-- ============================================================================

/-- The hierarchy rank is injective — no two positions share a rank.
    Combined with the natural order on ℕ, this makes the AH a total order. -/
theorem ah_rank_injective (a b : AHPosition) (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> simp_all [AHPosition.rank]

/-- All ranks are between 1 and 6. -/
theorem ah_rank_bounded (p : AHPosition) : 1 ≤ p.rank ∧ p.rank ≤ 6 := by
  cases p <;> simp [AHPosition.rank]

/-- Accessibility is reflexive (follows from `≥` on ℕ). -/
theorem ah_reflexive (p : AHPosition) : p.atLeastAsAccessible p := by
  simp [AHPosition.atLeastAsAccessible]

/-- Accessibility is transitive (follows from `≥` on ℕ). -/
theorem ah_transitive (a b c : AHPosition)
    (h1 : a.atLeastAsAccessible b) (h2 : b.atLeastAsAccessible c) :
    a.atLeastAsAccessible c := by
  simp [AHPosition.atLeastAsAccessible] at *; omega

/-! The K&C-anchored contiguity examples and the Primary Relativization
Constraint general proof live in `Phenomena/Relativization/Studies/KeenanComrie1977.lean`. -/

end Core
