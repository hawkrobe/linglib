import Linglib.Core.Case
import Linglib.Fragments.Mayan.Params

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
-- § 1: Marker Sets (canonical definition in Fragments.Mayan.Params)
-- ============================================================================

open Fragments.Mayan (MarkerSet)
export Fragments.Mayan (MarkerSet)

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
  deriving DecidableEq, Repr

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

-- ============================================================================
-- § 4: Mayan Absolutive Parameter (observable basis)
-- ============================================================================

-- `ABSPosition` is defined in `Fragments.Mayan.Params` and re-exported here
-- for backward compatibility.
export Fragments.Mayan (ABSPosition)

-- ============================================================================
-- § 5: Tada's Generalization
-- ============================================================================

/-- A Mayan language's observable extraction behavior. -/
structure MayanExtractionDatum where
  name : String
  absPosition : ABSPosition
  /-- Does the language ban A-bar extraction of transitive subjects? -/
  hasExtractionAsymmetry : Bool
  deriving DecidableEq, Repr

/-- Tada's Generalization data (table (19) of @cite{coon-mateo-pedro-preminger-2014},
    extending @cite{tada-1993}).

    The two noted outliers are Yucatec and Ixil (LOW-ABS with extraction
    asymmetries). Yucatec's AF differs significantly from other Mayan AF;
    Ixil's absolutive morphemes behave like full pronominal forms. -/
def tadasTable : List MayanExtractionDatum :=
  -- HIGH-ABS, +extraction asymmetries
  [ ⟨"Q'anjob'al",  .high, true⟩
  , ⟨"Akatek",      .high, true⟩
  , ⟨"Popti'",      .high, true⟩
  , ⟨"Chuj",        .high, true⟩
  , ⟨"Q'eqchi'",    .high, true⟩
  , ⟨"Uspantek",    .high, true⟩
  , ⟨"Poqomchi'",   .high, true⟩
  , ⟨"Poqomam",     .high, true⟩
  , ⟨"K'ichee'",    .high, true⟩
  , ⟨"Kaqchikel",   .high, true⟩
  , ⟨"Tz'utujil",   .high, true⟩
  , ⟨"Sakapultek",  .high, true⟩
  , ⟨"Sipakapense", .high, true⟩
  , ⟨"Mam",         .high, true⟩
  , ⟨"Awakatek",    .high, true⟩
  -- LOW-ABS, +extraction asymmetries (outliers)
  , ⟨"Yucatec",     .low,  true⟩
  , ⟨"Ixil",        .low,  true⟩
  -- LOW-ABS, -extraction asymmetries
  , ⟨"Lakantun",    .low,  false⟩
  , ⟨"Mopan",       .low,  false⟩
  , ⟨"Itzaj",       .low,  false⟩
  , ⟨"Chol",        .low,  false⟩
  , ⟨"Chontal",     .low,  false⟩
  , ⟨"Tseltal",     .low,  false⟩
  , ⟨"Tojol-ab'al", .low,  false⟩ ]

/-- All HIGH-ABS languages in the sample exhibit extraction asymmetries. -/
theorem high_abs_all_have_asymmetries :
    (tadasTable.filter (fun l => l.absPosition == .high)).all
      (fun l => l.hasExtractionAsymmetry) = true := by native_decide

/-- All LOW-ABS languages except the two noted outliers lack
    extraction asymmetries. -/
theorem low_abs_mostly_lack_asymmetries :
    (tadasTable.filter (fun l => l.absPosition == .low &&
      l.name != "Yucatec" && l.name != "Ixil")).all
      (fun l => !l.hasExtractionAsymmetry) = true := by native_decide

/-- No HIGH-ABS language lacks extraction asymmetries (unattested cell). -/
theorem high_abs_none_lack_asymmetries :
    (tadasTable.filter (fun l => l.absPosition == .high &&
      !l.hasExtractionAsymmetry)).length = 0 := by native_decide

end Phenomena.Ergativity
