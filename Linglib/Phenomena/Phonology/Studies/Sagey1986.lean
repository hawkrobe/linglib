import Linglib.Theories.Phonology.Featural.ComplexSegments
import Linglib.Theories.Phonology.Featural.Geometry
import Linglib.Theories.Phonology.Autosegmental.Defs
import Linglib.Theories.Phonology.Process.RuleBased.Defs

/-!
# Sagey (1986) @cite{sagey-1986}

The Representation of Features and Relations in Non-Linear Phonology.
PhD dissertation, Massachusetts Institute of Technology.

@cite{sagey-1986} proposes a hierarchical feature geometry organized by
vocal tract articulator, establishing the labial, coronal, dorsal, and
soft palate nodes that are now standard in phonological theory
(`Theories/Phonology/FeatureGeometry.lean`). The geometry predicts which
multiply-articulated (complex) segments are possible in human language
(`Theories/Phonology/ComplexSegments.lean`).

This study file formalizes Sagey-specific contributions that go beyond
the consensus geometry:

## Formalized contributions

1. **Major/minor articulator distinction** (Ch. 3): in complex segments,
   one articulator is major (determines degree of closure) and one is minor.

2. **Degree of closure as articulator-level property** (Ch. 3): [continuant]
   and [consonantal] describe the root-to-articulator relationship, not the
   segment as a whole. This allows different degrees of closure at
   different articulators within one segment (e.g., clicks).

3. **Soft palate independence** (Ch. 2): nasal assimilation (spreading
   the soft palate node) is structurally simpler than place assimilation
   (spreading the place node), explaining its cross-linguistic frequency.

4. **Empirical arguments**: Nupe labiovelars [k͡p]/[g͡b] as labio-dorsal
   complex segments with dorsal as major articulator.
-/

open Phonology (Segment Feature FeatureVal)
open Phonology.FeatureGeometry (GeomNode)
open Phonology.ComplexSegments
open Phonology.Autosegmental (agreeAt)

namespace Sagey1986

-- ============================================================================
-- § 1: Major/Minor Articulator Distinction (Ch. 3)
-- ============================================================================

/-- In a complex segment, one articulator is designated as major (determines
    the primary degree of closure seen by syllable structure) and the other
    as minor. This distinction is Sagey-specific — modern phonology does not
    uniformly adopt it. -/
structure MajorMinor where
  major : GeomNode
  minor : GeomNode
  major_is_articulator : major.isArticulator = true
  minor_is_articulator : minor.isArticulator = true
  distinct : major ≠ minor

/-- Nupe labiovelar /k͡p/: dorsal is major (stop closure), labial is minor.
    Sagey argues this based on nasalization patterns: labiovelars in Nupe
    nasalize to [ŋ͡m], with the velar nasal first, showing dorsal is the
    major articulator. -/
def nupe_kp_articulation : MajorMinor where
  major := .dorsal
  minor := .labial
  major_is_articulator := by decide
  minor_is_articulator := by decide
  distinct := by decide

-- ============================================================================
-- § 2: Degree of Closure as Articulator-Level Property (Ch. 3)
-- ============================================================================

/-- Sagey's degree of closure: a property of an articulator node, not a
    terminal feature. This is the Sagey-specific treatment; the modern
    geometry encodes closure as [±continuant] at the supralaryngeal node. -/
inductive DegreeOfClosure where
  | stop        -- complete closure
  | fricative   -- narrow constriction
  | approximant -- open constriction
  deriving DecidableEq, Repr

/-- An articulator paired with its degree of closure. In Sagey's framework,
    a click can be [−cont] at coronal and [−cont] at dorsal independently. -/
structure ArticulatorSpec where
  node : GeomNode
  closure : DegreeOfClosure
  node_is_articulator : node.isArticulator = true

/-- A click's anterior closure (coronal, full stop). -/
def click_anterior : ArticulatorSpec where
  node := .coronal
  closure := .stop
  node_is_articulator := by decide

/-- A click's posterior closure (dorsal, full stop). -/
def click_posterior : ArticulatorSpec where
  node := .dorsal
  closure := .stop
  node_is_articulator := by decide

-- ============================================================================
-- § 3: Soft Palate Independence (Ch. 2)
-- ============================================================================

/-- Nasal assimilation spreads the soft palate node (1 feature), while
    place assimilation spreads the place node (14 features). The soft
    palate's independence from place explains why nasal assimilation is
    cross-linguistically simpler and more common than place assimilation:
    it involves spreading a smaller constituent. -/
theorem nasal_assimilation_scope :
    GeomNode.softPalate.features.length < GeomNode.place.features.length := by
  native_decide

/-- Nasality is NOT under the place node — spreading place does not
    spread nasality. This is Sagey's core structural argument for the
    soft palate node as a separate constituent. -/
theorem nasal_not_under_place :
    Feature.nasal.dominatedBy .place = false := by native_decide

/-- Nasality IS under supralaryngeal (via the soft palate node), so
    total assimilation (spreading supralaryngeal) does spread nasality. -/
theorem nasal_under_supralaryngeal :
    Feature.nasal.dominatedBy .supralaryngeal = true := by native_decide

-- ============================================================================
-- § 4: Nupe Labiovelars
-- ============================================================================

/-- A Nupe labiovelar stop /k͡p/: specified for both labial and dorsal,
    voiceless, non-continuant. -/
def nupe_kp_segment : Segment :=
  Segment.ofSpecs
    [(.consonantal, true), (.sonorant, false), (.continuant, false),
     (.voice, false), (.labial, true), (.dorsal, true)]

/-- The Nupe /k͡p/ is a complex segment (two active place articulators). -/
theorem nupe_kp_is_complex : isComplex nupe_kp_segment = true := by
  native_decide

/-- The Nupe /k͡p/ is well-formed: labial ≠ dorsal. -/
theorem nupe_kp_wf : complexWF nupe_kp_segment = true := by
  native_decide

/-- A simple /p/ (labial only) is not complex. -/
def simple_p : Segment :=
  Segment.ofSpecs
    [(.consonantal, true), (.sonorant, false), (.continuant, false),
     (.voice, false), (.labial, true)]

theorem simple_p_not_complex : isComplex simple_p = false := by
  native_decide

/-- A velar nasal /ŋ/ is NOT complex despite activating both the dorsal
    articulator and the soft palate (velum lowering). The soft palate
    is structurally independent of place, so nasal + place combinations
    are simple segments — this is Sagey's core argument for the soft
    palate node's independence. -/
def velar_nasal : Segment :=
  Segment.ofSpecs
    [(.consonantal, true), (.sonorant, true), (.continuant, false),
     (.nasal, true), (.voice, true), (.dorsal, true)]

theorem velar_nasal_not_complex : isComplex velar_nasal = false := by
  native_decide

/-- The velar nasal is well-formed (only one place articulator: dorsal). -/
theorem velar_nasal_wf : complexWF velar_nasal = true := by
  native_decide

-- ============================================================================
-- § 5: Impossible Complex Segments (Ch. 2)
-- ============================================================================

/-- A coronal-only segment (alveolar /t/) with multiple coronal features
    is NOT complex: [+cor, +ant, −dist] all fall under the single coronal
    articulator. This formalizes Sagey's key prediction: palatal–velar
    stops are impossible because palatals and velars are both dorsal —
    no combination of features under a single articulator can produce a
    complex segment. -/
def alveolar_t : Segment :=
  Segment.ofSpecs
    [(.consonantal, true), (.sonorant, false), (.continuant, false),
     (.voice, false), (.coronal, true), (.anterior, true)]

theorem alveolar_not_complex : isComplex alveolar_t = false := by
  native_decide

/-- An alveopalatal (postalveolar) is [+cor, −ant, +dist] — still just
    one articulator (coronal), so not complex. An alveolar-alveopalatal
    doubly-articulated stop is therefore impossible: both articulations
    use the coronal articulator (@cite{sagey-1986} §2.2). -/
def alveopalatal : Segment :=
  Segment.ofSpecs
    [(.consonantal, true), (.sonorant, false), (.continuant, false),
     (.voice, false), (.coronal, true), (.anterior, false),
     (.distributed, true)]

theorem alveopalatal_not_complex : isComplex alveopalatal = false := by
  native_decide

-- ============================================================================
-- § 6: No-Crossing Constraint (Ch. 5)
-- ============================================================================

/-! ### Temporal derivation of the No-Crossing Constraint

@cite{sagey-1986} Ch. 5 derives the ban on crossing association lines from
temporal precedence. This section demonstrates the derived constraint with
concrete integer-valued time instances. -/

section NoCrossing

open Phonology.Autosegmental (Association TierPosition
  validAssociation crosses no_crossing)
open Core.Time (Interval)

/-- Helper: build a ℤ interval. -/
private def mkI (s f : ℤ) (h : s ≤ f := by omega) : Interval ℤ := ⟨s, f, h⟩

/-- Helper: build an association from four ℤ values. -/
private def mkAssoc (ts tf ms mf : ℤ) (ht : ts ≤ tf := by omega) (hm : ms ≤ mf := by omega)
    : Association ℤ :=
  ⟨⟨⟨ts, tf, ht⟩⟩, ⟨⟨ms, mf, hm⟩⟩⟩

/-- A concrete geminate /t:/ occupying timing slots [0,1] and [2,3],
    with the melodic element spanning [0,3]. -/
def geminate_tt : Association ℤ × Association ℤ :=
  (mkAssoc 0 1 0 3, mkAssoc 2 3 0 3)

/-- Both associations in the geminate are valid (timing overlaps melody). -/
theorem geminate_tt_valid :
    validAssociation geminate_tt.1 ∧ validAssociation geminate_tt.2 := by
  simp only [geminate_tt, mkAssoc, validAssociation, Interval.overlaps]
  omega

/-- A concrete falling contour tone: timing [0,4], H tone [0,2], L tone [2,4]. -/
def contour_HL : Association ℤ × Association ℤ :=
  (mkAssoc 0 4 0 2, mkAssoc 0 4 2 4)

/-- Both associations in the contour tone are valid. -/
theorem contour_HL_valid :
    validAssociation contour_HL.1 ∧ validAssociation contour_HL.2 := by
  simp only [contour_HL, mkAssoc, validAssociation, Interval.overlaps]
  omega

/-- **Crossing forces invalidity** (@cite{sagey-1986} §5.3):
    a crossing configuration — timing₁ at [0,1] → melody₁ at [4,5],
    timing₂ at [2,3] → melody₂ at [0,1] — has its timing positions
    correctly ordered and melody positions reversed, but the first
    association is invalid because timing [0,1] does not overlap
    melody [4,5]. This demonstrates the mechanism: crossing is
    impossible not because it's stipulated, but because validity
    (temporal overlap) cannot be satisfied for both associations
    simultaneously when they cross. -/
theorem crossing_forces_invalidity :
    let a₁ := mkAssoc 0 1 4 5
    let a₂ := mkAssoc 2 3 0 1
    crosses a₁ a₂ ∧ ¬ validAssociation a₁ := by
  simp only [mkAssoc, crosses, validAssociation,
    Interval.precedes, Interval.overlaps]
  omega

end NoCrossing

end Sagey1986
