import Linglib.Phonology.Segmental.Defs
import Mathlib.Logic.Relation

/-!
# Feature Geometry [clements-1985] [sagey-1986]

The hierarchical organization of phonological features as autosegmental class
nodes ([clements-hume-1995]):

    Root [±syll, ±cons, ±son, ±approx, ±del.rel., ±tap, ±trill]
    ├── Laryngeal [±voice, ±s.g., ±c.g.]
    └── Supralaryngeal [±cont]
        ├── Soft Palate [±nasal]
        └── Place
            ├── Labial [±lab, ±round, ±labiodental]
            ├── Coronal [±cor, ±ant, ±dist, ±lat, ±strid]
            └── Dorsal [±dor, ±high, ±low, ±front, ±back, ±tense]

The constituency from Root down to the three Place articulators is the consensus
of [clements-1985] and [sagey-1986]. The placement of the individual terminal
features — notably `[continuant]`, `[nasal]`, and `[lateral]`/`[strident]` — is
theory-specific and contested: [sagey-1986] argues `[continuant]` is an
articulator-level property, against its Supralaryngeal placement here. That
divergence is formalized in `Studies/Sagey1986.lean`.

A feature's geometric node is distinct from its manner-class (`Feature.category`):
a manner feature like `[lateral]` attaches geometrically under Coronal, so the
flat predicates (`Feature.IsPlace` &c.) do not coincide with single-node
dominance — see the subsumption theorems below.
-/

namespace Phonology.FeatureGeometry

/-! ### Geometric nodes -/

/-- Class nodes in the feature geometry tree. -/
inductive GeomNode where
  | root           -- Root node (dominates everything)
  | laryngeal      -- Laryngeal node ([clements-1985])
  | supralaryngeal -- Supralaryngeal node ([clements-1985])
  | softPalate     -- Soft palate node ([sagey-1986])
  | place          -- Place node ([clements-1985])
  | labial         -- Labial articulator ([sagey-1986])
  | coronal        -- Coronal articulator ([sagey-1986])
  | dorsal         -- Dorsal articulator ([sagey-1986])
  deriving DecidableEq, Repr

/-! ### Tree structure -/

/-- Parent of each node in the geometry tree. The supralaryngeal node
    ([clements-1985]) mediates between root and place. -/
def GeomNode.parent : GeomNode → Option GeomNode
  | .root           => none
  | .laryngeal      => some .root
  | .supralaryngeal => some .root
  | .softPalate     => some .supralaryngeal
  | .place          => some .supralaryngeal
  | .labial         => some .place
  | .coronal        => some .place
  | .dorsal         => some .place

/-- All geometric nodes. -/
def GeomNode.allNodes : List GeomNode :=
  [.root, .laryngeal, .supralaryngeal, .softPalate, .place, .labial, .coronal, .dorsal]

/-- Children of a node: nodes whose parent is `n`. -/
def GeomNode.children (n : GeomNode) : List GeomNode :=
  GeomNode.allNodes.filter (λ m => m.parent == some n)

/-! ### Dominance -/

/-- `n` dominates `m`: `n` is `m` or one of its ancestors — the reflexive-
    transitive closure of "is the parent of", reached by walking up from `m`.
    Depth-agnostic, unlike a fixed unrolling. -/
def GeomNode.Dominates (n m : GeomNode) : Prop :=
  Relation.ReflTransGen (fun a b => a.parent = some b) m n

/-- Dominance unrolls to the bounded parent-chain: the geometry has depth ≤ 3,
    so `n` dominates `m` iff `n` is reached within three steps up. This is the
    decidable face of `Dominates` that the `decide`-checked facts below run
    through. -/
theorem GeomNode.dominates_iff (n m : GeomNode) :
    n.Dominates m ↔ n = m ∨ m.parent = some n ∨
      (m.parent.bind GeomNode.parent) = some n ∨
      ((m.parent.bind GeomNode.parent).bind GeomNode.parent) = some n := by
  unfold GeomNode.Dominates
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
      rcases ih with rfl | h | h | h
      · exact Or.inr (Or.inl hbc)
      · exact Or.inr (Or.inr (Or.inl (by rw [h, Option.bind_some]; exact hbc)))
      · exact Or.inr (Or.inr (Or.inr (by rw [h, Option.bind_some]; exact hbc)))
      · exfalso; revert h hbc; cases m <;> cases b <;> cases c <;> decide
  · rintro (rfl | h | h | h)
    · exact .refl
    · exact .single h
    · obtain ⟨p, hmp, hpn⟩ := Option.bind_eq_some_iff.mp h
      exact Relation.ReflTransGen.tail (.single hmp) hpn
    · obtain ⟨q, hq, hqn⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨p, hmp, hpq⟩ := Option.bind_eq_some_iff.mp hq
      exact Relation.ReflTransGen.tail (.tail (.single hmp) hpq) hqn

instance : DecidableRel GeomNode.Dominates := fun n m =>
  decidable_of_iff _ (GeomNode.dominates_iff n m).symm

end Phonology.FeatureGeometry

/-! ### Feature-to-node mapping -/

namespace Phonology

open FeatureGeometry in
/-- Each terminal feature maps to its dominating class node.

    - Root: [syllabic], [consonantal], [sonorant], [approximant],
      [delayedRelease], [tap], [trill]
    - Laryngeal: [voice], [spreadGlottis], [constrGlottis]
    - Supralaryngeal: [continuant]
    - Soft Palate: [nasal]
    - Labial: [labial], [round], [labiodental]
    - Coronal: [coronal], [anterior], [distributed], [lateral], [strident]
    - Dorsal: [dorsal], [high], [low], [front], [back], [tense] -/
def Feature.node : Feature → GeomNode
  | .syllabic | .consonantal | .sonorant | .approximant
  | .delayedRelease | .tap | .trill => .root
  | .voice | .spreadGlottis | .constrGlottis => .laryngeal
  | .continuant => .supralaryngeal
  | .nasal => .softPalate
  | .labial | .round | .labiodental => .labial
  | .coronal | .anterior | .distributed | .lateral | .strident => .coronal
  | .dorsal | .high | .low | .front | .back | .tense => .dorsal

open FeatureGeometry in
/-- Does node `n` dominate the node that feature `f` belongs to? -/
@[reducible] def Feature.DominatedBy (f : Feature) (n : GeomNode) : Prop :=
  GeomNode.Dominates n f.node

end Phonology

namespace Phonology.FeatureGeometry

/-! ### Natural classes -/

/-- Features dominated by node `n` — a natural class in the feature-geometric
    sense: the features that pattern together under processes targeting `n`. -/
def GeomNode.features (n : GeomNode) : List Feature :=
  Feature.allFeatures.filter (λ f => decide (GeomNode.Dominates n f.node))

/-! ### Verification theorems -/

-- Tree structure

theorem root_has_no_parent : GeomNode.root.parent = none := rfl

theorem nonroot_has_parent (n : GeomNode) (h : n ≠ .root) :
    n.parent.isSome = true := by
  cases n <;> simp_all [GeomNode.parent]

theorem allNodes_complete (n : GeomNode) : n ∈ GeomNode.allNodes := by
  cases n <;> simp [GeomNode.allNodes]

-- Natural class counts ([hayes-2009] complete inventory: 26 features)

theorem root_features_count : GeomNode.root.features.length = 26 := rfl
theorem laryngeal_features_count : GeomNode.laryngeal.features.length = 3 := rfl
theorem supralaryngeal_features_count :
    GeomNode.supralaryngeal.features.length = 16 := rfl
theorem softPalate_features_count :
    GeomNode.softPalate.features.length = 1 := rfl
theorem place_features_count : GeomNode.place.features.length = 14 := rfl
theorem labial_features_count : GeomNode.labial.features.length = 3 := rfl
theorem coronal_features_count : GeomNode.coronal.features.length = 5 := rfl
theorem dorsal_features_count : GeomNode.dorsal.features.length = 6 := rfl

-- Subsumption of existing flat predicates
--
-- isLaryngeal matches the geometry exactly.
-- isDorsal matches the geometry exactly.
-- isPlace now matches the geometry exactly (includes labiodental, front, tense).
-- The manner/root features have no single geometric counterpart: they are
-- distributed across root, supralaryngeal, softPalate, and coronal.

theorem IsLaryngeal_iff_laryngeal_DominatedBy (f : Feature) :
    f.IsLaryngeal ↔ f.DominatedBy .laryngeal := by
  cases f <;> decide

theorem IsDorsal_iff_dorsal_DominatedBy (f : Feature) :
    f.IsDorsal ↔ f.DominatedBy .dorsal := by
  cases f <;> decide

-- IsPlace is a strict subset of geometric place dominance
-- (manner features like lateral and strident are geometrically under coronal)
theorem IsPlace_implies_place_DominatedBy (f : Feature) :
    f.IsPlace → f.DominatedBy .place := by
  cases f <;> decide

theorem lateral_geometrically_under_place :
    Feature.lateral.DominatedBy .place := by decide

theorem strident_geometrically_under_place :
    Feature.strident.DominatedBy .place := by decide

end Phonology.FeatureGeometry

/-!
## Complex and contour segments [sagey-1986]

Segments with multiple simultaneous or sequential articulations.

**Complex segments** have one root node with multiple *place* articulator
nodes active simultaneously (e.g., labiovelars [k͡p], [g͡b]; corono-velar
clicks). They occupy a single timing slot and their articulations are
unordered. The soft palate is an articulator in the vocal tract but sits
outside the place node, so nasal + place combinations (e.g., [ŋ]) are
simple segments, not complex ones.

**Contour segments** have two root nodes linked to a single timing slot,
with articulations in sequence (e.g., affricates [ts], [tʃ]; prenasalized
stops [ⁿd], [ᵐb]). A single-bundle `Segment` has one value per feature and so
cannot host two root nodes: only *complex* (simultaneous, one-root) segments are
modeled here, via `activeArticulators`. Sequential contour structures need the
multi-anchor autosegmental representation (`Autosegmental/`), where they belong
([sagey-1986]).

The feature geometry predicts which complex segments are possible: only those
combining *distinct* articulator nodes. Palatal–velar stops are impossible
because both use the dorsal articulator; labio-velars are possible because
labial and dorsal are independent.
-/

namespace Phonology.FeatureGeometry

/-! ### Articulator nodes -/

/-- Is this a place articulator node? The three place articulators —
    labial (lips), coronal (tongue blade/tip), dorsal (tongue body) —
    are the independent articulators whose combinations give rise to
    complex segments ([sagey-1986]). The soft palate is an
    articulator in the vocal tract but sits outside the place node
    (as a sibling under supralaryngeal), so it does not participate
    in complex segment formation: a velar nasal [ŋ] is simple despite
    activating both dorsal and soft palate. -/
def GeomNode.IsArticulator : GeomNode → Prop
  | .labial | .coronal | .dorsal => True
  | _ => False

instance : DecidablePred GeomNode.IsArticulator := fun n => by
  cases n <;> unfold GeomNode.IsArticulator <;> infer_instance

/-- The articulator nodes in the geometry. -/
def articulatorNodes : List GeomNode :=
  GeomNode.allNodes.filter (fun n => decide (GeomNode.IsArticulator n))

theorem articulatorNodes_count : articulatorNodes.length = 3 := rfl

/-! ### Articulator geometry (verification) -/

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

end Phonology.FeatureGeometry

namespace Phonology

open Phonology.FeatureGeometry (GeomNode articulatorNodes)

/-! ### Active articulators of a segment -/

/-- Which articulator nodes have at least one specified feature in segment `s`? -/
def Segment.activeArticulators (s : Segment) : List GeomNode :=
  articulatorNodes.filter λ n =>
    n.features.any λ f => s f |>.isSome

/-- Number of active articulator nodes in a segment. -/
def Segment.articulatorCount (s : Segment) : Nat :=
  s.activeArticulators.length

/-! ### Segment classification and well-formedness -/

/-- A complex segment has two or more simultaneously active articulator
    nodes — e.g., labiovelars [k͡p] (labial + dorsal). -/
def Segment.IsComplex (s : Segment) : Prop :=
  s.articulatorCount ≥ 2

instance : DecidablePred Segment.IsComplex := fun _ =>
  inferInstanceAs (Decidable (_ ≥ _))

/-- **The complex-segment well-formedness condition holds by construction**: a
    segment's active articulators are always distinct, because they are filtered
    from the duplicate-free `articulatorNodes`. The condition that articulations
    occupy distinct articulator nodes is therefore not a separate constraint but a
    theorem ([sagey-1986]). -/
theorem Segment.activeArticulators_nodup (s : Segment) :
    s.activeArticulators.Nodup := by
  unfold Segment.activeArticulators
  exact (by decide : articulatorNodes.Nodup).filter _

end Phonology
