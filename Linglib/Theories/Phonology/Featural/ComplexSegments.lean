import Linglib.Theories.Phonology.Featural.Geometry

/-!
# Complex and Contour Segments @cite{sagey-1986}

Segments with multiple simultaneous or sequential articulations.

**Complex segments** have one root node with multiple *place* articulator
nodes active simultaneously (e.g., labiovelars [k͡p], [g͡b]; corono-velar
clicks). They occupy a single timing slot and their articulations are
unordered. The soft palate is an articulator in the vocal tract but sits
outside the place node, so nasal + place combinations (e.g., [ŋ]) are
simple segments, not complex ones.

**Contour segments** have two root nodes linked to a single timing slot,
with articulations in sequence (e.g., affricates [ts], [tʃ]; prenasalized
stops [ⁿd], [ᵐb]).

The distinction was established by @cite{sagey-1986} and is now standard
in phonological theory. The feature geometry predicts exactly which
complex segments are possible: only those combining *distinct* articulator
nodes. Palatal–velar stops are impossible because both use the dorsal
articulator; labio-velars are possible because labial and dorsal are
independent.
-/

-- Define `isArticulator` in the FeatureGeometry namespace so dot notation
-- works on GeomNode values across the codebase.
namespace Phonology.FeatureGeometry

/-- Is this a place articulator node? The three place articulators —
    labial (lips), coronal (tongue blade/tip), dorsal (tongue body) —
    are the independent articulators whose combinations give rise to
    complex segments (@cite{sagey-1986} Ch. 2). The soft palate is an
    articulator in the vocal tract but sits outside the place node
    (as a sibling under supralaryngeal), so it does not participate
    in complex segment formation: a velar nasal [ŋ] is simple despite
    activating both dorsal and soft palate. -/
def GeomNode.IsArticulator : GeomNode → Prop
  | .labial | .coronal | .dorsal => True
  | _ => False

instance : DecidablePred GeomNode.IsArticulator := fun n => by
  cases n <;> unfold GeomNode.IsArticulator <;> infer_instance

end Phonology.FeatureGeometry

namespace Phonology.ComplexSegments

open Phonology (Segment Feature FeatureVal)
open Phonology.FeatureGeometry (GeomNode)

-- ============================================================================
-- § 1: Articulator Nodes
-- ============================================================================

/-- The articulator nodes in the geometry. -/
def articulatorNodes : List GeomNode :=
  GeomNode.allNodes.filter (fun n => decide (GeomNode.IsArticulator n))

theorem articulatorNodes_count : articulatorNodes.length = 3 := by native_decide

-- ============================================================================
-- § 2: Active Articulators
-- ============================================================================

/-- Which articulator nodes have at least one specified feature in segment `s`? -/
def activeArticulators (s : Segment) : List GeomNode :=
  articulatorNodes.filter λ n =>
    n.features.any λ f => s.spec f |>.isSome

/-- Number of active articulator nodes in a segment. -/
def articulatorCount (s : Segment) : Nat :=
  (activeArticulators s).length

-- ============================================================================
-- § 3: Segment Classification
-- ============================================================================

/-- A complex segment has two or more simultaneously active articulator
    nodes — e.g., labiovelars [k͡p] (labial + dorsal). -/
def IsComplex (s : Segment) : Prop :=
  articulatorCount s ≥ 2

instance : DecidablePred IsComplex := fun _ =>
  inferInstanceAs (Decidable (_ ≥ _))

-- ============================================================================
-- § 4: Well-Formedness
-- ============================================================================

/-- Complex segment well-formedness: active articulators must be distinct
    nodes. This is trivially satisfied by `activeArticulators` (which returns
    a duplicate-free sublist of `articulatorNodes`), but we state it
    explicitly as the standard WFC. -/
def ComplexWF (s : Segment) : Prop :=
  let aa := activeArticulators s
  aa.length = aa.eraseDups.length

instance : DecidablePred ComplexWF := fun _ =>
  inferInstanceAs (Decidable (_ = _))

-- ============================================================================
-- § 5: Verification
-- ============================================================================

/-- Articulators are exactly the leaf-level nodes (no children). -/
theorem articulators_are_leaves :
    ∀ n ∈ articulatorNodes, n.children = [] := by decide

/-- Every articulator is dominated by root. -/
theorem articulators_under_root :
    ∀ n ∈ articulatorNodes, GeomNode.Dominates .root n := by decide

/-- Labial and dorsal are distinct (required for labiovelars). -/
theorem labial_ne_dorsal : GeomNode.labial ≠ GeomNode.dorsal := by decide

/-- Soft palate is not a place node — it is a sibling of Place under
    Supralaryngeal, not a child. This means nasal assimilation (spreading
    soft palate) is independent of place assimilation (spreading place). -/
theorem softPalate_not_under_place :
    ¬ GeomNode.Dominates .place .softPalate := by decide

/-- Soft palate is not a place articulator — nasals are simple segments
    even though they involve velum lowering plus an oral place of
    articulation. This follows from `softPalate` being a sibling of
    `place` under `supralaryngeal`, not a child of `place`. -/
theorem softPalate_not_articulator :
    ¬ GeomNode.IsArticulator .softPalate := by decide

/-- The three place articulators are all distinct from each other —
    this gives rise to three possible complex segment types:
    labio-coronal, labio-dorsal, corono-dorsal. -/
theorem place_articulators_distinct :
    GeomNode.labial ≠ GeomNode.coronal ∧
    GeomNode.labial ≠ GeomNode.dorsal ∧
    GeomNode.coronal ≠ GeomNode.dorsal := by decide

/-- Every place articulator is under the place node. -/
theorem articulators_under_place :
    ∀ n ∈ articulatorNodes, GeomNode.Dominates .place n := by decide

end Phonology.ComplexSegments
