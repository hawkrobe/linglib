import Linglib.Phonology.Segmental.Defs
import Mathlib.Logic.Relation

/-!
# Feature geometry
[clements-1985] [sagey-1986]

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
of [clements-1985] and [sagey-1986]. The placement of individual terminals —
notably `[continuant]`, `[nasal]`, and `[lateral]`/`[strident]` — is theory-specific
and contested: [sagey-1986] argues `[continuant]` is articulator-level, against its
Supralaryngeal placement here (the divergence is formalized in `Studies/Sagey1986.lean`).
A feature's geometric node is also distinct from its manner-class (`Feature.category`):
`[lateral]` attaches under Coronal yet is a manner feature, so the flat predicates
(`Feature.IsPlace` &c.) do not coincide with single-node dominance.

## Main definitions

* `Node`, `Node.parent`, `Node.Dominates` — the class nodes, the tree,
  and the reflexive-transitive ancestor relation.
* `Feature.node` — each feature's dominating node (this geometry's assignment;
  rivals live in their study files).
* `Node.features` — the natural class a node dominates.
* `Node.IsArticulator`, `Segment.activeArticulators`, `Segment.IsComplex` — the
  place articulators and a segment's simultaneous (complex) articulations.

## Main results

* `Node.dominates_iff` — dominance unrolls to the depth-≤ 3 parent chain, the
  decidable face the `decide` facts run through.
* `IsLaryngeal_iff_laryngeal_DominatedBy`, `IsDorsal_iff_dorsal_DominatedBy` — two
  flat predicates coincide with single-node dominance; `IsPlace` is only a subset.
* `Segment.activeArticulators_nodup` — complex-segment well-formedness holds by
  construction ([sagey-1986]).
-/

namespace Phonology.FeatureGeometry

/-! ### Geometric nodes -/

/-- The class nodes of the feature-geometry tree ([clements-1985]; [sagey-1986]). -/
inductive Node where
  /-- The root node, dominating all others. -/
  | root
  /-- The laryngeal node: voicing and glottal features. -/
  | laryngeal
  /-- The supralaryngeal node, mediating root and place. -/
  | supralaryngeal
  /-- The soft-palate (velum) node: nasality. -/
  | softPalate
  /-- The place node, over the three oral articulators. -/
  | place
  /-- The labial articulator (the lips). -/
  | labial
  /-- The coronal articulator (the tongue blade/tip). -/
  | coronal
  /-- The dorsal articulator (the tongue body). -/
  | dorsal
  deriving DecidableEq, Repr

variable (n m : Node)

/-! ### Tree structure -/

/-- The parent of each node; `root` alone has none. -/
def Node.parent : Node → Option Node
  | .root           => none
  | .laryngeal      => some .root
  | .supralaryngeal => some .root
  | .softPalate     => some .supralaryngeal
  | .place          => some .supralaryngeal
  | .labial         => some .place
  | .coronal        => some .place
  | .dorsal         => some .place

/-- All eight nodes. -/
def Node.allNodes : List Node :=
  [.root, .laryngeal, .supralaryngeal, .softPalate, .place, .labial, .coronal, .dorsal]

/-- The children of `n`: the nodes whose parent is `n`. -/
def Node.children : List Node := allNodes.filter (λ k => k.parent == some n)

/-! ### Dominance -/

/-- `n` dominates `m`: it is `m` or one of its ancestors — the reflexive-transitive
    closure of "is the parent of", walked up from `m`. Depth-agnostic. -/
def Node.Dominates : Prop := Relation.ReflTransGen (λ a b => a.parent = some b) m n

/-- Dominance unrolls to the depth-≤ 3 parent chain — the decidable face the
    `decide` facts below run through. -/
theorem Node.dominates_iff :
    n.Dominates m ↔ n = m ∨ m.parent = some n ∨
      (m.parent.bind Node.parent) = some n ∨
      ((m.parent.bind Node.parent).bind Node.parent) = some n := by
  unfold Node.Dominates
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
      exact .tail (.single hmp) hpn
    · obtain ⟨q, hq, hqn⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨p, hmp, hpq⟩ := Option.bind_eq_some_iff.mp hq
      exact .tail (.tail (.single hmp) hpq) hqn

instance : DecidableRel Node.Dominates := λ n m => decidable_of_iff _ (Node.dominates_iff n m).symm

end Phonology.FeatureGeometry

/-! ### Feature-to-node mapping -/

namespace Phonology

open FeatureGeometry

/-- Each terminal feature's dominating class node — this geometry's assignment
    (contested for `[continuant]`/`[nasal]`/`[lateral]`; see the module docstring). -/
def Feature.node : Feature → Node
  | .syllabic | .consonantal | .sonorant | .approximant
  | .delayedRelease | .tap | .trill => .root
  | .voice | .spreadGlottis | .constrGlottis => .laryngeal
  | .continuant => .supralaryngeal
  | .nasal => .softPalate
  | .labial | .round | .labiodental => .labial
  | .coronal | .anterior | .distributed | .lateral | .strident => .coronal
  | .dorsal | .high | .low | .front | .back | .tense => .dorsal

/-- Does node `n` dominate the node feature `f` belongs to? -/
@[reducible] def Feature.DominatedBy (f : Feature) (n : Node) : Prop := n.Dominates f.node

end Phonology

namespace Phonology.FeatureGeometry

variable (n : Node) (f : Feature)

/-! ### Natural classes -/

/-- The features dominated by `n` — its natural class, the features that pattern
    together under processes targeting `n`. -/
def Node.features : List Feature := Feature.allFeatures.filter (λ g => decide (n.Dominates g.node))

/-! ### Tree structure (verification) -/

theorem root_has_no_parent : Node.root.parent = none := rfl

theorem nonroot_has_parent (h : n ≠ .root) : n.parent.isSome = true := by
  cases n <;> simp_all [Node.parent]

theorem allNodes_complete : n ∈ Node.allNodes := by cases n <;> simp [Node.allNodes]

/-! ### Natural class sizes
[hayes-2009]'s complete 26-feature inventory. -/

theorem root_features_count : Node.root.features.length = 26 := rfl
theorem laryngeal_features_count : Node.laryngeal.features.length = 3 := rfl
theorem supralaryngeal_features_count : Node.supralaryngeal.features.length = 16 := rfl
theorem softPalate_features_count : Node.softPalate.features.length = 1 := rfl
theorem place_features_count : Node.place.features.length = 14 := rfl
theorem labial_features_count : Node.labial.features.length = 3 := rfl
theorem coronal_features_count : Node.coronal.features.length = 5 := rfl
theorem dorsal_features_count : Node.dorsal.features.length = 6 := rfl

/-! ### Flat-predicate subsumption

`IsLaryngeal`/`IsDorsal` coincide with single-node dominance; `IsPlace` is only a
*subset* (manner features like `[lateral]`/`[strident]` sit geometrically under Coronal). -/

theorem IsLaryngeal_iff_laryngeal_DominatedBy : f.IsLaryngeal ↔ f.DominatedBy .laryngeal := by
  cases f <;> decide

theorem IsDorsal_iff_dorsal_DominatedBy : f.IsDorsal ↔ f.DominatedBy .dorsal := by cases f <;> decide

theorem IsPlace_implies_place_DominatedBy : f.IsPlace → f.DominatedBy .place := by cases f <;> decide

theorem lateral_geometrically_under_place : Feature.lateral.DominatedBy .place := by decide

theorem strident_geometrically_under_place : Feature.strident.DominatedBy .place := by decide

/-!
## Complex and contour segments
[sagey-1986]

**Complex segments** have one root node with several *place* articulators active
simultaneously (e.g. labiovelars [k͡p]); they fill one timing slot and their
articulations are unordered. **Contour segments** have two root nodes on one timing
slot, with articulations in sequence (e.g. affricates [ts]). A single-bundle
`Segment` has one value per feature, so it can host only complex (one-root)
segments, via `activeArticulators`; sequential contours need the multi-anchor
autosegmental representation (`Autosegmental/`).

The geometry predicts which complex segments are possible: only those combining
*distinct* articulators. Palatal–velar stops are impossible (both are dorsal);
labiovelars are possible (labial and dorsal are independent).
-/

/-! ### Articulator nodes -/

/-- A place articulator — labial, coronal, or dorsal — the independent articulators
    whose distinct combinations give complex segments ([sagey-1986]). -/
def Node.IsArticulator : Node → Prop
  | .labial | .coronal | .dorsal => True
  | _ => False

instance : DecidablePred Node.IsArticulator :=
  λ n => by cases n <;> unfold Node.IsArticulator <;> infer_instance

/-- The articulator nodes. -/
def articulatorNodes : List Node := Node.allNodes.filter (λ n => decide n.IsArticulator)

/-! ### Articulator geometry (verification) -/

theorem articulatorNodes_count : articulatorNodes.length = 3 := rfl

/-- Articulators are exactly the leaf nodes. -/
theorem articulators_are_leaves : ∀ n ∈ articulatorNodes, n.children = [] := by decide

/-- Every articulator is dominated by root. -/
theorem articulators_under_root : ∀ n ∈ articulatorNodes, Node.root.Dominates n := by decide

/-- Every articulator is dominated by place. -/
theorem articulators_under_place : ∀ n ∈ articulatorNodes, Node.place.Dominates n := by decide

/-- The three place articulators are pairwise distinct — giving three complex types
    (labio-coronal, labio-dorsal, corono-dorsal). -/
theorem place_articulators_distinct :
    Node.labial ≠ .coronal ∧ Node.labial ≠ .dorsal ∧ Node.coronal ≠ .dorsal := by decide

/-- The soft palate is a *sibling* of place, not under it — so nasal assimilation
    (spreading soft palate) is independent of place assimilation. -/
theorem softPalate_not_under_place : ¬ Node.place.Dominates .softPalate := by decide

/-- The soft palate is not an articulator — a velar nasal [ŋ] is simple despite
    activating both dorsal and soft palate. -/
theorem softPalate_not_articulator : ¬ Node.softPalate.IsArticulator := by decide

end Phonology.FeatureGeometry

namespace Phonology

open FeatureGeometry (Node articulatorNodes)

variable (s : Segment)

/-! ### Active articulators -/

/-- The articulator nodes with at least one specified feature in `s`. -/
def Segment.activeArticulators : List Node :=
  articulatorNodes.filter (λ n => n.features.any (λ g => (s g).isSome))

/-- The number of active articulator nodes in `s`. -/
def Segment.articulatorCount : Nat := s.activeArticulators.length

/-! ### Complex segments -/

/-- A complex segment has two or more simultaneously active articulators — e.g. a
    labiovelar [k͡p] (labial + dorsal). -/
def Segment.IsComplex : Prop := s.articulatorCount ≥ 2

instance : DecidablePred Segment.IsComplex := λ _ => inferInstanceAs (Decidable (_ ≥ _))

/-- **Complex-segment well-formedness holds by construction**: a segment's active
    articulators are always distinct, being filtered from the duplicate-free
    `articulatorNodes`. The distinct-articulator condition is a theorem, not a
    separate constraint ([sagey-1986]). -/
theorem Segment.activeArticulators_nodup : s.activeArticulators.Nodup := by
  unfold Segment.activeArticulators
  exact (by decide : articulatorNodes.Nodup).filter _

end Phonology
