import Linglib.Theories.Phonology.Features

/-!
# Feature Geometry @cite{clements-1985}

Hierarchical organization of phonological features following the standard
feature geometry model. The tree synthesizes three sources:

- **Clements (1985)**: root, laryngeal, supralaryngeal, and place nodes
- **Sagey (1986)**: articulator sub-nodes under Place (labial, coronal, dorsal)
- **Hayes (2009, Ch 4)**: complete 26-feature inventory mapped to geometric nodes

    Root [±syll, ±cons, ±son, ±approx, ±nas, ±del.rel., ±tap, ±trill]
    ├── Laryngeal [±voice, ±s.g., ±c.g.]
    └── Supralaryngeal [±cont]
        └── Place
            ├── Labial [±lab, ±round, ±labiodental]
            ├── Coronal [±cor, ±ant, ±dist, ±lat, ±strid]
            └── Dorsal [±dor, ±high, ±low, ±front, ±back, ±tense]

The flat classification predicates in `Features.lean` (`isMajorClass`, `isPlace`)
do not exactly correspond to any single geometric node —
see the subsumption theorems below.
-/

namespace Theories.Phonology.FeatureGeometry

-- ============================================================================
-- § 1: Geometric Nodes
-- ============================================================================

/-- Class nodes in the feature geometry tree. -/
inductive GeomNode where
  | root           -- Root node (dominates everything)
  | laryngeal      -- Laryngeal node (Clements 1985)
  | supralaryngeal -- Supralaryngeal node (Clements 1985)
  | place          -- Place node (Clements 1985)
  | labial         -- Labial articulator (Sagey 1986)
  | coronal        -- Coronal articulator (Sagey 1986)
  | dorsal         -- Dorsal articulator (Sagey 1986)
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Tree Structure
-- ============================================================================

/-- Parent of each node in the geometry tree. The supralaryngeal node
    (Clements 1985, diagram (4)) mediates between root and place. -/
def GeomNode.parent : GeomNode → Option GeomNode
  | .root           => none
  | .laryngeal      => some .root
  | .supralaryngeal => some .root
  | .place          => some .supralaryngeal
  | .labial         => some .place
  | .coronal        => some .place
  | .dorsal         => some .place

/-- All geometric nodes. -/
def GeomNode.allNodes : List GeomNode :=
  [.root, .laryngeal, .supralaryngeal, .place, .labial, .coronal, .dorsal]

/-- Children of a node: nodes whose parent is `n`. -/
def GeomNode.children (n : GeomNode) : List GeomNode :=
  GeomNode.allNodes.filter (λ m => m.parent == some n)

/-- Depth of a node in the tree (root = 0). -/
def GeomNode.depth : GeomNode → Nat
  | .root => 0
  | .laryngeal | .supralaryngeal => 1
  | .place => 2
  | .labial | .coronal | .dorsal => 3

-- ============================================================================
-- § 4: Dominance
-- ============================================================================

/-- Does node `n` dominate node `m`? Reflexive-transitive closure of the
    parent relation, unrolled to depth 3 (the tree's maximum depth). -/
def GeomNode.dominates (n m : GeomNode) : Bool :=
  n == m || match m.parent with
    | none => false
    | some p => n == p || match p.parent with
      | none => false
      | some pp => n == pp || match pp.parent with
        | none => false
        | some ppp => n == ppp

end Theories.Phonology.FeatureGeometry

-- ============================================================================
-- § 3: Feature-to-Node Mapping
-- ============================================================================

namespace Theories.Phonology

open FeatureGeometry in
/-- Each terminal feature maps to its dominating class node.

    - Root: [syllabic], [consonantal], [sonorant], [approximant], [nasal],
      [delayedRelease], [tap], [trill]
    - Laryngeal: [voice], [spreadGlottis], [constrGlottis]
    - Supralaryngeal: [continuant]
    - Labial: [labial], [round], [labiodental]
    - Coronal: [coronal], [anterior], [distributed], [lateral], [strident]
    - Dorsal: [dorsal], [high], [low], [front], [back], [tense] -/
def Feature.node : Feature → GeomNode
  | .syllabic | .consonantal | .sonorant | .approximant
  | .nasal | .delayedRelease | .tap | .trill => .root
  | .voice | .spreadGlottis | .constrGlottis => .laryngeal
  | .continuant => .supralaryngeal
  | .labial | .round | .labiodental => .labial
  | .coronal | .anterior | .distributed | .lateral | .strident => .coronal
  | .dorsal | .high | .low | .front | .back | .tense => .dorsal

open FeatureGeometry in
/-- Does node `n` dominate the node that feature `f` belongs to? -/
def Feature.dominatedBy (f : Feature) (n : GeomNode) : Bool :=
  n.dominates f.node

end Theories.Phonology

-- ============================================================================
-- § 5–7: Natural Classes, Verification, Spreading/Delinking
-- ============================================================================

namespace Theories.Phonology.FeatureGeometry

/-- Features dominated by node `n` — a natural class in the feature-geometric
    sense: the features that pattern together under processes targeting `n`. -/
def GeomNode.features (n : GeomNode) : List Feature :=
  Feature.allFeatures.filter (λ f => n.dominates f.node)

-- ============================================================================
-- § 6: Verification Theorems
-- ============================================================================

-- Tree structure

theorem root_has_no_parent : GeomNode.root.parent = none := rfl

theorem nonroot_has_parent (n : GeomNode) (h : n ≠ .root) :
    n.parent.isSome = true := by
  cases n <;> simp_all [GeomNode.parent]

theorem parent_decreases_depth (n p : GeomNode) (h : n.parent = some p) :
    p.depth < n.depth := by
  cases n <;> simp [GeomNode.parent] at h <;> subst h <;> decide

theorem allNodes_complete (n : GeomNode) : n ∈ GeomNode.allNodes := by
  cases n <;> simp [GeomNode.allNodes]

-- Depth

theorem root_depth : GeomNode.root.depth = 0 := rfl
theorem supralaryngeal_depth : GeomNode.supralaryngeal.depth = 1 := rfl
theorem place_depth : GeomNode.place.depth = 2 := rfl
theorem labial_depth : GeomNode.labial.depth = 3 := rfl
theorem coronal_depth : GeomNode.coronal.depth = 3 := rfl
theorem dorsal_depth : GeomNode.dorsal.depth = 3 := rfl

-- Natural class counts (Hayes 2009 complete inventory: 26 features)

theorem root_features_count : GeomNode.root.features.length = 26 := by native_decide
theorem laryngeal_features_count : GeomNode.laryngeal.features.length = 3 := by native_decide
theorem supralaryngeal_features_count :
    GeomNode.supralaryngeal.features.length = 15 := by native_decide
theorem place_features_count : GeomNode.place.features.length = 14 := by native_decide
theorem labial_features_count : GeomNode.labial.features.length = 3 := by native_decide
theorem coronal_features_count : GeomNode.coronal.features.length = 5 := by native_decide
theorem dorsal_features_count : GeomNode.dorsal.features.length = 6 := by native_decide

-- Subsumption of existing flat predicates
--
-- isLaryngeal matches the geometry exactly.
-- isDorsal matches the geometry exactly.
-- isPlace now matches the geometry exactly (includes labiodental, front, tense).
-- isMajorClass has no single geometric counterpart: its features are
-- distributed across root, supralaryngeal, and coronal.

theorem isLaryngeal_iff_laryngeal_dominates (f : Feature) :
    f.isLaryngeal = f.dominatedBy .laryngeal := by
  cases f <;> rfl

theorem isDorsal_iff_dorsal_dominates (f : Feature) :
    f.isDorsal = f.dominatedBy .dorsal := by
  cases f <;> rfl

-- isPlace is a strict subset of geometric place dominance
-- (isMajorClass features like lateral and strident are geometrically under coronal)
theorem isPlace_implies_place_dominates (f : Feature) :
    f.isPlace = true → f.dominatedBy .place = true := by
  cases f <;> decide

theorem lateral_geometrically_under_place :
    Feature.lateral.dominatedBy .place = true := by rfl

theorem strident_geometrically_under_place :
    Feature.strident.dominatedBy .place = true := by rfl

-- ============================================================================
-- § 7: Spreading / Delinking Predicates
-- ============================================================================

/-- Can feature `f` spread under node `n`? True when `f` is dominated by `n`. -/
def canSpreadUnder (n : GeomNode) (f : Feature) : Bool :=
  n.dominates f.node

/-- Does delinking node `n` remove feature `f`? True when `n` dominates `f`'s
    node and `n` is not Root (delinking Root = deleting the segment). -/
def delinkedBy (n : GeomNode) (f : Feature) : Bool :=
  n.dominates f.node && n != .root

end Theories.Phonology.FeatureGeometry
