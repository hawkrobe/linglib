import Linglib.Core.Case.Basic

/-!
# The Mayan Alignment Puzzle
@cite{imanishi-2020} @cite{coon-2013a} @cite{dixon-1994}

Theory-neutral observations about the accusative side of Mayan split
ergativity. In perfective aspect, Mayan languages uniformly show ergative
alignment. In non-perfective aspect, they switch to accusative alignment —
but the specific alignment patterns differ across languages.

## The Puzzle

Kaqchikel, Chol, and Q'anjob'al have (nearly) identical biclausal structures
for non-perfective clauses, yet display contrastive alignment patterns.

**Kaqchikel type** (S = ABS, O = ERG/GEN):
  Both S and A are cross-referenced by absolutive (set B) markers.
  The transitive object is cross-referenced by ergative/genitive (set A).

**Chol/Q'anjob'al type** (S = ERG/GEN, O = ABS):
  Both S and A are cross-referenced by ergative/genitive (set A) markers.
  The transitive object is cross-referenced by absolutive (set B).
-/

namespace Phenomena.Ergativity

-- ============================================================================
-- § 1: Marker Sets
-- ============================================================================

/-- The two agreement marker paradigms found in Mayan languages.
    Set A and set B are the traditional Mayanist labels for the two
    cross-referencing paradigms on the verb. -/
inductive MarkerSet where
  /-- Set A: cross-references ergative arguments (transitive agent) and
      genitives (possessors). Ergative and genitive are homophonous. -/
  | setA
  /-- Set B: cross-references absolutive arguments (intransitive subject
      and, in ergative alignment, transitive patient). -/
  | setB
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Accusative-Side Alignment Patterns
-- ============================================================================

/-- Alignment pattern in the accusative (non-perfective) side of the split.
    Records which marker set cross-references S (= A on accusative side)
    and which cross-references O. -/
structure AccSidePattern where
  /-- Marker set cross-referencing S (intransitive subject) and
      A (transitive subject) — these pattern together on the accusative side. -/
  sMarker : MarkerSet
  /-- Marker set cross-referencing O (transitive object). -/
  oMarker : MarkerSet
  deriving DecidableEq, BEq, Repr

/-- Kaqchikel-type accusative alignment: S/A = set B (ABS), O = set A (ERG/GEN). -/
def kaqchikelPattern : AccSidePattern :=
  { sMarker := .setB, oMarker := .setA }

/-- Chol/Q'anjob'al-type accusative alignment: S/A = set A (ERG/GEN), O = set B (ABS). -/
def cholPattern : AccSidePattern :=
  { sMarker := .setA, oMarker := .setB }

-- ============================================================================
-- § 3: Observations
-- ============================================================================

/-- The two accusative-side patterns are distinct. -/
theorem patterns_distinct : kaqchikelPattern ≠ cholPattern := by decide

/-- The two patterns are mirror images: the marker sets are swapped. -/
theorem patterns_mirror :
    kaqchikelPattern.sMarker = cholPattern.oMarker ∧
    kaqchikelPattern.oMarker = cholPattern.sMarker := ⟨rfl, rfl⟩

end Phenomena.Ergativity
