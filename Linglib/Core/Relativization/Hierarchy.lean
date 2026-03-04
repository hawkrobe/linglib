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
def AHPosition.atLeastAsAccessible (p1 p2 : AHPosition) : Bool :=
  p1.rank >= p2.rank

/-- Position p1 is strictly more accessible than p2. -/
def AHPosition.moreAccessible (p1 p2 : AHPosition) : Bool :=
  p1.rank > p2.rank

/-- All AH positions in descending order of accessibility. -/
def AHPosition.all : List AHPosition :=
  [.subject, .directObject, .indirectObject, .oblique, .genitive, .objComparison]

-- ============================================================================
-- § 2: Contiguity Predicate
-- ============================================================================

/-- Whether a list of AH positions contains at least one position at rank r. -/
private def hasAHRank (positions : List AHPosition) (r : Nat) : Bool :=
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

/-- The hierarchy is strictly ordered: each position is more accessible
    than the one below it. -/
theorem ah_strictly_ordered :
    AHPosition.moreAccessible .subject .directObject = true ∧
    AHPosition.moreAccessible .directObject .indirectObject = true ∧
    AHPosition.moreAccessible .indirectObject .oblique = true ∧
    AHPosition.moreAccessible .oblique .genitive = true ∧
    AHPosition.moreAccessible .genitive .objComparison = true := by
  native_decide

/-- Subject is the most accessible position (rank 6). -/
theorem subject_most_accessible :
    AHPosition.rank .subject = 6 := by native_decide

/-- Object of comparison is the least accessible position (rank 1). -/
theorem objComparison_least_accessible :
    AHPosition.rank .objComparison = 1 := by native_decide

/-- Accessibility is reflexive. -/
theorem ah_reflexive :
    AHPosition.all.all (λ p => p.atLeastAsAccessible p) = true := by
  native_decide

/-- Accessibility is transitive. -/
theorem ah_transitive :
    AHPosition.all.all (λ p1 =>
      AHPosition.all.all (λ p2 =>
        AHPosition.all.all (λ p3 =>
          if p1.atLeastAsAccessible p2 && p2.atLeastAsAccessible p3
          then p1.atLeastAsAccessible p3
          else true))) = true := by
  native_decide

-- ============================================================================
-- § 4: Contiguity Examples
-- ============================================================================

/-- The full hierarchy [SU, DO, IO, OBL, GEN, OCOMP] is contiguous. -/
theorem full_ah_contiguous :
    contiguousOnAH AHPosition.all = true := by native_decide

/-- A single position is trivially contiguous. -/
theorem singleton_contiguous :
    contiguousOnAH [AHPosition.subject] = true := by native_decide

/-- [SU, DO] is contiguous. -/
theorem su_do_contiguous :
    contiguousOnAH [AHPosition.subject, .directObject] = true := by native_decide

/-- [IO, OBL, GEN] is contiguous (a non-primary segment). -/
theorem io_obl_gen_contiguous :
    contiguousOnAH [AHPosition.indirectObject, .oblique, .genitive] = true := by
  native_decide

/-- [SU, DO, OBL] is NOT contiguous (skips IO at rank 4). -/
theorem su_do_obl_not_contiguous :
    contiguousOnAH [AHPosition.subject, .directObject, .oblique] = false := by
  native_decide

end Core
