import Linglib.Datasets.WALS.Features.F132A
import Linglib.Datasets.WALS.Features.F133A
import Linglib.Datasets.WALS.Features.F134A
import Linglib.Datasets.WALS.Features.F135A

/-!
# Color-term typology — substrate types and WALS data
@cite{wals-2013} (Chs 132–135) @cite{berlin-kay-1969} @cite{kay-maffi-2013}

Type-level enums + per-language profile struct for cross-linguistic color
naming across @cite{wals-2013} chapters 132–135 (Kay & Maffi: number of basic
color categories; green/blue and red/yellow boundary patterns), plus WALS
distribution data and the principal cross-linguistic generalizations from
the Berlin & Kay tradition.

## Schema

- `NonDerivedColorCount` (Ch 132): number of non-derived basic color categories
- `BasicColorCount` (Ch 133): total number of basic color categories
- `GreenBlueRelation` (Ch 134): green/blue boundary (the classic *grue*
  distinction)
- `RedYellowRelation` (Ch 135): red/yellow boundary
- `ColorProfile`: per-language bundle (all four chapters)

Per-language data lives in `Fragments/{Lang}/Color.lean`.
-/

set_option autoImplicit false

namespace Typology

-- ============================================================================
-- WALS Ch 132: Number of non-derived basic color categories
-- ============================================================================

/-- Number of non-derived basic color categories (WALS Ch 132,
    @cite{kay-maffi-2013}). Ranges from 3 to 6 along the Berlin & Kay
    sequence; transitional half-values represent languages with one
    composite category undergoing splitting. -/
inductive NonDerivedColorCount where
  | three
  | threeHalf
  | four
  | fourHalf
  | five
  | fiveHalf
  | six
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Ch 133: Total number of basic color categories
-- ============================================================================

/-- Total number of basic color categories including derived ones
    (WALS Ch 133, @cite{kay-maffi-2013}). Ranges from 3–4 (minimal systems)
    to 11 (maximal, e.g., English, Russian). -/
inductive BasicColorCount where
  | v3to4
  | v4to5
  | v6to6h
  | v7to7h
  | v8to8h
  | v9to10
  | v11
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Ch 134: Green and blue
-- ============================================================================

/-- How a language treats the green-blue region of color space
    (WALS Ch 134, @cite{kay-maffi-2013}). The classic *grue* / green-blue
    composite distinction, with several other composite patterns
    (with black, with yellow). -/
inductive GreenBlueRelation where
  /-- Separate terms for green and blue. -/
  | distinct
  /-- A single *grue* term covering both green and blue. -/
  | merged
  /-- A single term covering black, green, and blue. -/
  | blackGreenBlue
  /-- Black/blue merged, green separate. -/
  | blackBlueVsGreen
  /-- Yellow, green, blue all merged. -/
  | yellowGreenBlue
  /-- Yellow/green merged, blue separate. -/
  | yellowGreenVsBlue
  /-- No green or blue term at all. -/
  | noTerm
  deriving DecidableEq, Repr

-- ============================================================================
-- WALS Ch 135: Red and yellow
-- ============================================================================

/-- How a language treats the red-yellow region of color space
    (WALS Ch 135, @cite{kay-maffi-2013}). -/
inductive RedYellowRelation where
  /-- Separate terms for red and yellow. -/
  | distinct
  /-- A single term covering both red and yellow. -/
  | merged
  /-- Yellow/green/blue merged, vs red. -/
  | yellowGreenBlueVsRed
  /-- Yellow/green merged, vs red. -/
  | yellowGreenVsRed
  /-- No red or yellow term at all. -/
  | noTerm
  deriving DecidableEq, Repr

-- ============================================================================
-- Per-language profile
-- ============================================================================

/-- A language's color-naming profile across @cite{wals-2013} Chs 132–135.
    Coverage is sparse (~120 languages); fields are optional. -/
structure ColorProfile where
  language : String
  iso : String := ""
  family : String := ""
  /-- Ch 132: non-derived basic color categories. -/
  nonDerived : Option NonDerivedColorCount := none
  /-- Ch 133: total basic color categories. -/
  basic : Option BasicColorCount := none
  /-- Ch 134: green-blue relation. -/
  greenBlue : Option GreenBlueRelation := none
  /-- Ch 135: red-yellow relation. -/
  redYellow : Option RedYellowRelation := none
  deriving Repr

-- ============================================================================
-- WALS converters
-- ============================================================================

/-- Convert WALS 132A non-derived-color-count values into the substrate enum. -/
def fromWALS132A : Datasets.WALS.F132A.NumberOfNonDerivedBasicColourCategories → NonDerivedColorCount
  | .v3  => .three
  | .v35 => .threeHalf
  | .v4  => .four
  | .v45 => .fourHalf
  | .v5  => .five
  | .v55 => .fiveHalf
  | .v6  => .six

/-- Convert WALS 133A basic-color-count values into the substrate enum. -/
def fromWALS133A : Datasets.WALS.F133A.NumberOfBasicColourCategories → BasicColorCount
  | .v34   => .v3to4
  | .v4555 => .v4to5
  | .v665  => .v6to6h
  | .v775  => .v7to7h
  | .v885  => .v8to8h
  | .v910  => .v9to10
  | .v11   => .v11

/-- Convert WALS 134A green-blue values into the substrate enum. -/
def fromWALS134A : Datasets.WALS.F134A.GreenAndBlue → GreenBlueRelation
  | .greenVsBlue       => .distinct
  | .greenBlue         => .merged
  | .blackGreenBlue    => .blackGreenBlue
  | .blackBlueVsGreen  => .blackBlueVsGreen
  | .yellowGreenBlue   => .yellowGreenBlue
  | .yellowGreenVsBlue => .yellowGreenVsBlue
  | .none              => .noTerm

/-- Convert WALS 135A red-yellow values into the substrate enum. -/
def fromWALS135A : Datasets.WALS.F135A.RedAndYellow → RedYellowRelation
  | .redVsYellow          => .distinct
  | .redYellow            => .merged
  | .yellowGreenBlueVsRed => .yellowGreenBlueVsRed
  | .yellowGreenVsRed     => .yellowGreenVsRed
  | .none                 => .noTerm

-- ============================================================================
-- WALS distribution data
-- ============================================================================

/-- WALS Ch 134 distribution: green-blue boundary patterns
    (@cite{kay-maffi-2013}, n = 120). -/
structure GreenBlueCounts where
  distinct : Nat
  merged : Nat
  other : Nat
  deriving Repr

def GreenBlueCounts.total (c : GreenBlueCounts) : Nat :=
  c.distinct + c.merged + c.other

/-- WALS Ch 134 counts (120 languages). -/
def walsGreenBlue : GreenBlueCounts :=
  { distinct := 30
  , merged := 68
  , other := 22 }

/-- WALS Ch 135 distribution: red-yellow boundary patterns
    (@cite{kay-maffi-2013}, n = 120). -/
structure RedYellowCounts where
  distinct : Nat
  merged : Nat
  other : Nat
  deriving Repr

def RedYellowCounts.total (c : RedYellowCounts) : Nat :=
  c.distinct + c.merged + c.other

/-- WALS Ch 135 counts (120 languages). -/
def walsRedYellow : RedYellowCounts :=
  { distinct := 98
  , merged := 15
  , other := 7 }

-- ============================================================================
-- Cross-linguistic generalizations
-- ============================================================================

/-- The *grue* pattern (merged green/blue) is the majority for the green-blue
    dimension (68 of 120 = 57%), more than double the distinct-terms pattern
    (30). Berlin & Kay's classic finding: mid-evolution color systems collapse
    green and blue. -/
theorem grue_majority :
    walsGreenBlue.merged > walsGreenBlue.distinct := by decide

/-- Red and yellow are almost always distinguished: 98 of 120 = 82% of
    languages have separate terms. The red/yellow split appears very early in
    the Berlin & Kay sequence. -/
theorem red_yellow_usually_distinct :
    walsRedYellow.distinct * 5 > walsRedYellow.total * 4 := by decide

/-- Red/yellow merger is rare (15 languages) — much rarer than green/blue
    merger (68). The Berlin & Kay sequence predicts this asymmetry: red
    appears before any blue/green term. -/
theorem red_yellow_merger_rarer_than_grue :
    walsGreenBlue.merged > walsRedYellow.merged := by decide

end Typology
