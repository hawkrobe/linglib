import Linglib.Theories.Phonology.Features

/-!
# Feature Geometry

Hierarchical organization of phonological features following the feature geometry
model (Clements 1985; Sagey 1986; Clements & Hume 1995). Class nodes organize
terminal features into groups whose members pattern together under phonological
processes (spreading, delinking, assimilation).

Tree structure (Clements & Hume 1995, "The Internal Structure of Speech Sounds"):

    Root [±cons, ±son]
    ├── Laryngeal [±voice, ±s.g., ±c.g.]
    ├── Manner [±cont, ±nas, ±lat, ±strid]
    └── Place
        ├── Labial [±lab, ±round]
        ├── Coronal [±cor, ±ant, ±dist]
        └── Dorsal [±dor, ±high, ±low, ±back, ±atr]

This module subsumes the flat classification predicates in `Features.lean`
(`isMajorClass`, `isLaryngeal`, `isPlace`, `isDorsal`) and proves equivalence.
-/

namespace Theories.Phonology.FeatureGeometry

-- ============================================================================
-- § 1: Geometric Nodes
-- ============================================================================

/-- Class nodes in the feature geometry tree. Organizational nodes that
    dominate terminal features. -/
inductive GeomNode where
  | root        -- Root node (dominates everything)
  | laryngeal   -- Laryngeal node
  | manner      -- Manner node (continuant, nasal, lateral, strident)
  | place       -- Supralaryngeal Place node
  | labial      -- Labial articulator
  | coronal     -- Coronal articulator
  | dorsal      -- Dorsal articulator
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Tree Structure
-- ============================================================================

/-- Parent of each node in the geometry tree. -/
def GeomNode.parent : GeomNode → Option GeomNode
  | .root      => none
  | .laryngeal => some .root
  | .manner    => some .root
  | .place     => some .root
  | .labial    => some .place
  | .coronal   => some .place
  | .dorsal    => some .place

/-- All geometric nodes. -/
def GeomNode.allNodes : List GeomNode :=
  [.root, .laryngeal, .manner, .place, .labial, .coronal, .dorsal]

/-- Children of a node: nodes whose parent is `n`. -/
def GeomNode.children (n : GeomNode) : List GeomNode :=
  GeomNode.allNodes.filter (λ m => m.parent == some n)

/-- Depth of a node in the tree (root = 0). -/
def GeomNode.depth : GeomNode → Nat
  | .root => 0
  | .laryngeal | .manner | .place => 1
  | .labial | .coronal | .dorsal => 2

-- ============================================================================
-- § 4: Dominance
-- ============================================================================

/-- Does node `n` dominate node `m`? Reflexive-transitive closure of the
    parent relation, unrolled to depth 2 (the tree's maximum depth). -/
def GeomNode.dominates (n m : GeomNode) : Bool :=
  n == m || match m.parent with
    | none => false
    | some p => n == p || match p.parent with
      | none => false
      | some pp => n == pp

end Theories.Phonology.FeatureGeometry

-- ============================================================================
-- § 3: Feature-to-Node Mapping
-- ============================================================================

namespace Theories.Phonology

open FeatureGeometry in
/-- Each terminal feature is dominated by exactly one class node.
    `Feature.labial` maps to `GeomNode.labial`, `Feature.coronal` to
    `GeomNode.coronal`, `Feature.dorsal` to `GeomNode.dorsal`. -/
def Feature.node : Feature → GeomNode
  | .consonantal | .sonorant => .root
  | .voice | .spreadGlottis | .constrGlottis => .laryngeal
  | .continuant | .nasal | .lateral | .strident => .manner
  | .labial | .round => .labial
  | .coronal | .anterior | .distributed => .coronal
  | .dorsal | .high | .low | .back | .atr => .dorsal

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
theorem labial_depth : GeomNode.labial.depth = 2 := rfl
theorem coronal_depth : GeomNode.coronal.depth = 2 := rfl
theorem dorsal_depth : GeomNode.dorsal.depth = 2 := rfl

-- Natural class counts

theorem root_features_count : GeomNode.root.features.length = 19 := by native_decide
theorem laryngeal_features_count : GeomNode.laryngeal.features.length = 3 := by native_decide
theorem manner_features_count : GeomNode.manner.features.length = 4 := by native_decide
theorem place_features_count : GeomNode.place.features.length = 10 := by native_decide
theorem labial_features_count : GeomNode.labial.features.length = 2 := by native_decide
theorem coronal_features_count : GeomNode.coronal.features.length = 3 := by native_decide
theorem dorsal_features_count : GeomNode.dorsal.features.length = 5 := by native_decide

-- Subsumption of existing predicates

theorem isPlace_iff_place_dominates (f : Feature) :
    f.isPlace = f.dominatedBy .place := by
  cases f <;> rfl

theorem isDorsal_iff_dorsal_dominates (f : Feature) :
    f.isDorsal = f.dominatedBy .dorsal := by
  cases f <;> rfl

theorem isLaryngeal_iff_laryngeal_dominates (f : Feature) :
    f.isLaryngeal = f.dominatedBy .laryngeal := by
  cases f <;> rfl

theorem isMajorClass_iff_root_or_manner (f : Feature) :
    f.isMajorClass = (f.node == GeomNode.root || f.node == GeomNode.manner) := by
  cases f <;> rfl

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
