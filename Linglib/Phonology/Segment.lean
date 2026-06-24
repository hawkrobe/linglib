/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Feature
import Linglib.Features.Basic

/-!
# Segments

A **segment** is a partial binary specification of phonological `Feature`s —
i.e. a feature bundle. Its `spec` field is `Features.Bundle Feature (fun _ => Bool)`
in unfolded form (`Feature → Option Bool`), so the shared bundle algebra
(`Features.Bundle.merge`/`set`/`delete`) operates on it directly while the
`Option` face keeps the ergonomic dot-notation.

## Main definitions

* `Segment` — a feature bundle over `Feature`
* `Segment.Specified` / `Segment.HasValue` — the valuation API
* `Segment.ofSpecs` / `Segment.matchesPattern` — natural-class construction and membership
* `Segment.applyChanges` — SPE structural change, via `Features.Bundle.merge`
* `Segment.IsVowel`, `IsConsonant`, `IsStop`, … — the natural-class predicates

[hayes-2009] [chomsky-halle-1968]
-/

namespace Phonology

/-! ### The segment bundle -/

/-- A segment: a `Features.Bundle Feature (fun _ => Bool)` (in unfolded
    `Feature → Option Bool` form) — a partial binary-feature specification
    (`none` = unspecified). -/
structure Segment where
  spec : Feature → Option Bool

/-- Is feature `f` specified (either [+F] or [−F])? -/
def Segment.Specified (s : Segment) (f : Feature) : Prop :=
  (s.spec f).isSome = true

instance (s : Segment) : DecidablePred (Segment.Specified s) := fun _ =>
  inferInstanceAs (Decidable (_ = true))

/-- Does feature `f` have value `v`? -/
def Segment.HasValue (s : Segment) (f : Feature) (v : Bool) : Prop :=
  s.spec f = some v

instance (s : Segment) (f : Feature) (v : Bool) :
    Decidable (Segment.HasValue s f v) :=
  inferInstanceAs (Decidable (_ = _))

/-- Decidable equality on segments via exhaustive feature comparison.
    Enables `decide` on segment-level goals and OT tableaux
    over `List Segment` candidates. -/
instance : DecidableEq Segment := fun s1 s2 =>
  if h : (Feature.allFeatures.all fun f => s1.spec f == s2.spec f) = true
  then isTrue (by
    cases s1; cases s2; congr; funext f
    exact eq_of_beq (List.all_eq_true.mp h f (allFeatures_complete f)))
  else isFalse (fun heq => by
    subst heq
    exact h (List.all_eq_true.mpr fun f _ => beq_self_eq_true (s1.spec f)))

/-! ### Pattern matching and feature changes -/

/-- Build a segment from a list of (feature, value) pairs.
    Unmentioned features are unspecified (`none`), giving natural-class
    semantics: `ofSpecs [(continuant, false)]` matches all [-cont] segments. -/
def Segment.ofSpecs (specs : List (Feature × Bool)) : Segment where
  spec f := match specs.find? (λ p => p.1 == f) with
    | some (_, v) => some v
    | none => none

/-- Bool: does segment `s` match natural-class pattern `p`? True when every
    feature specified in `p` agrees with `s`; unspecified features in `p`
    match anything. -/
def Segment.matchesPattern (s : Segment) (p : Segment) : Bool :=
  Feature.allFeatures.all λ f =>
    match p.spec f with
    | none => true
    | some v => s.spec f == some v

/-- Prop wrapper around `matchesPattern` (mirrors `Segment.HasValue`). Lets
    consumers write mathlib-style universally-quantified theorems with
    Decidable inference via the Bool computation. -/
def Segment.MatchesPattern (s p : Segment) : Prop := s.matchesPattern p = true

instance (s p : Segment) : Decidable (Segment.MatchesPattern s p) :=
  inferInstanceAs (Decidable (_ = _))

/-- Merge feature changes from `change` into `s`: features specified in
    `change` override `s`'s values; unspecified features in `change` are
    preserved. Implements the SPE structural change `A → B` (when `B` is a
    partial bundle) as the shared `Features.Bundle.merge`. -/
def Segment.applyChanges (s change : Segment) : Segment :=
  ⟨Features.Bundle.merge change.spec s.spec⟩

/-- Two segments are equal iff their `spec` functions agree on every feature. -/
@[ext] theorem Segment.ext {s t : Segment} (h : ∀ f, s.spec f = t.spec f) :
    s = t := by
  cases s; cases t; congr; funext f; exact h f

/-- Every segment matches itself as a pattern. -/
@[simp] theorem Segment.matchesPattern_self (s : Segment) :
    s.matchesPattern s = true := by
  unfold Segment.matchesPattern
  rw [List.all_eq_true]
  intro f _
  cases s.spec f
  · rfl
  · exact beq_self_eq_true _

/-- Applying the empty change list is the identity. -/
@[simp] theorem Segment.applyChanges_ofSpecs_nil (s : Segment) :
    s.applyChanges (Segment.ofSpecs []) = s := by
  ext f; simp [Segment.applyChanges, Segment.ofSpecs, Features.Bundle.merge]

/-- Applying the same change twice equals applying it once. -/
@[simp] theorem Segment.applyChanges_idem (s change : Segment) :
    (s.applyChanges change).applyChanges change = s.applyChanges change := by
  ext f
  simp only [Segment.applyChanges, Features.Bundle.merge]
  cases change.spec f <;> rfl

/-! ### Natural-class predicates

Language-neutral natural-class membership predicates, by the SPE feature
decompositions standard since [chomsky-halle-1968] and codified in textbook
form by [hayes-2009]. Pure substrate: they project information already encoded
in a segment's feature bundle, consumed by per-language Fragment files rather
than redefined locally. -/

/-- A segment is a vowel iff it is [+syllabic]. -/
def Segment.IsVowel (s : Segment) : Prop := s.HasValue .syllabic true

instance (s : Segment) : Decidable s.IsVowel := by
  unfold Segment.IsVowel; infer_instance

/-- A segment is a consonant iff it is [+consonantal]. -/
def Segment.IsConsonant (s : Segment) : Prop := s.HasValue .consonantal true

instance (s : Segment) : Decidable s.IsConsonant := by
  unfold Segment.IsConsonant; infer_instance

/-- A segment is an oral stop iff it is [+cons, -son, -cont]. -/
def Segment.IsStop (s : Segment) : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant false ∧
    s.HasValue .continuant false

instance (s : Segment) : Decidable s.IsStop := by
  unfold Segment.IsStop; infer_instance

/-- A segment is a fricative iff it is [+cons, -son, +cont]. -/
def Segment.IsFricative (s : Segment) : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant false ∧
    s.HasValue .continuant true

instance (s : Segment) : Decidable s.IsFricative := by
  unfold Segment.IsFricative; infer_instance

/-- A segment is a nasal iff it is [+nasal]. -/
def Segment.IsNasal (s : Segment) : Prop := s.HasValue .nasal true

instance (s : Segment) : Decidable s.IsNasal := by
  unfold Segment.IsNasal; infer_instance

/-- A segment is a liquid iff it is [+cons, +son] and one of
[+lateral], [+trill], [+tap] — admitting the lateral /l/, the trill /r/,
and the flap /ɾ/ under a single textbook class. -/
def Segment.IsLiquid (s : Segment) : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant true ∧
    (s.HasValue .lateral true ∨ s.HasValue .trill true ∨ s.HasValue .tap true)

instance (s : Segment) : Decidable s.IsLiquid := by
  unfold Segment.IsLiquid; infer_instance

/-- A segment is a glide iff it is [-cons, -syllabic, +approximant]. -/
def Segment.IsGlide (s : Segment) : Prop :=
  s.HasValue .consonantal false ∧ s.HasValue .syllabic false ∧
    s.HasValue .approximant true

instance (s : Segment) : Decidable s.IsGlide := by
  unfold Segment.IsGlide; infer_instance

/-! ### Underspecification

A segment is **underspecified** for a feature `f` when its spec returns `none`.
These segment-level operations are thin lifts of the shared `Features.Bundle`
algebra. Three-valued (`+ / − / ∅`) specification is standard in [keating-1988],
[inkelas-orgun-1995], and [steriade-1995]; `fillFeature` uses `merge`
(default-fill, preserving existing values) per [kiparsky-1982] [archangeli-1988],
while `setFeature` overrides. The Latin coda /l/ analysis in [sen-2015] Ch 2 is a
worked example. -/

namespace Segment

/-! ### Underspecification predicate -/

/-- A segment is **unspecified** for feature `f` iff its spec returns `none`. -/
def Unspecified (s : Segment) (f : Feature) : Prop := s.spec f = none

instance (s : Segment) (f : Feature) : Decidable (s.Unspecified f) :=
  inferInstanceAs (Decidable (_ = none))

/-- Specification and unspecification are mutually exclusive and exhaustive. -/
theorem specified_iff_not_unspecified (s : Segment) (f : Feature) :
    s.Specified f ↔ ¬ s.Unspecified f := by
  unfold Specified Unspecified
  cases s.spec f <;> simp

/-! ### Operations -/

/-- Remove the specification of feature `f` from `s` (lift of
    `Features.Bundle.delete`). The result is unspecified for `f` and agrees
    with `s` on every other feature. -/
def unsetFeature (s : Segment) (f : Feature) : Segment :=
  ⟨Features.Bundle.delete f s.spec⟩

/-- Set feature `f` to value `v`, overriding any existing specification
    (lift of `Features.Bundle.set`). For default-fill semantics that only
    assigns when `f` is currently unspecified, use `fillFeature`. -/
def setFeature (s : Segment) (f : Feature) (v : Bool) : Segment :=
  ⟨Features.Bundle.set f v s.spec⟩

/-- Fill feature `f` with value `v` only if `s` is currently unspecified
    for `f`; existing specifications are preserved. This implements the
    default-fill semantics of feature-filling rules in lexical phonology
    [kiparsky-1982] [archangeli-1988]. -/
def fillFeature (s : Segment) (f : Feature) (v : Bool) : Segment :=
  ⟨Features.Bundle.merge s.spec
    (Function.update (fun _ => none : Feature → Option Bool) f (some v))⟩

/-- Categorical feature spreading from context: the target `s`, when
    unspecified for `f`, takes the `f`-value of `ctx`; already-specified
    targets and features other than `f` are untouched. When `ctx` is
    itself unspecified for `f`, the target stays unspecified.

    This is a [keating-1988] *context rule*: the target acquires a categorical
    feature value from its neighbour and that value blocks further
    interactions. It is **distinct from** her gradient phonetic interpolation
    (her unspecified /h/ example), in which an unspecified segment stays
    unspecified and the phonetics builds a continuous trajectory through it;
    gradient phonetic interpolation is out of scope at this categorical-featural
    substrate. -/
def fillFromContext (s : Segment) (f : Feature) (ctx : Segment) : Segment :=
  ⟨Features.Bundle.merge s.spec
    (Function.update (fun _ => none : Feature → Option Bool)
       f (ctx.spec f))⟩

/-! ### Effect on the modified feature -/

@[simp] theorem unsetFeature_unspecified (s : Segment) (f : Feature) :
    (s.unsetFeature f).Unspecified f :=
  Function.update_self _ _ _

@[simp] theorem setFeature_hasValue (s : Segment) (f : Feature) (v : Bool) :
    (s.setFeature f v).HasValue f v :=
  Function.update_self _ _ _

theorem fillFeature_hasValue_of_unspecified
    (s : Segment) {f : Feature} (h : s.Unspecified f) (v : Bool) :
    (s.fillFeature f v).HasValue f v := by
  simp only [Segment.fillFeature, Segment.HasValue, Features.Bundle.merge,
    show s.spec f = none from h, Function.update_self]

theorem fillFeature_spec_of_specified
    (s : Segment) {f : Feature} {w : Bool} (h : s.HasValue f w) (v : Bool) :
    (s.fillFeature f v).spec f = some w := by
  simp only [Segment.fillFeature, Features.Bundle.merge,
    show s.spec f = some w from h]

theorem fillFromContext_spec_self_of_unspecified
    (s : Segment) {f : Feature} (h : s.Unspecified f) (ctx : Segment) :
    (s.fillFromContext f ctx).spec f = ctx.spec f := by
  simp only [Segment.fillFromContext, Features.Bundle.merge,
    show s.spec f = none from h, Function.update_self]

theorem fillFromContext_spec_self_of_specified
    (s : Segment) {f : Feature} {w : Bool} (h : s.HasValue f w) (ctx : Segment) :
    (s.fillFromContext f ctx).spec f = some w := by
  simp only [Segment.fillFromContext, Features.Bundle.merge,
    show s.spec f = some w from h]

/-! ### Spec preserved on other features -/

@[simp] theorem unsetFeature_spec_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) :
    (s.unsetFeature f).spec g = s.spec g :=
  Function.update_of_ne (Ne.symm h) _ _

@[simp] theorem setFeature_spec_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) (v : Bool) :
    (s.setFeature f v).spec g = s.spec g :=
  Function.update_of_ne (Ne.symm h) _ _

@[simp] theorem fillFeature_spec_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) (v : Bool) :
    (s.fillFeature f v).spec g = s.spec g := by
  simp only [Segment.fillFeature, Features.Bundle.merge,
    Function.update_of_ne (Ne.symm h)]
  cases s.spec g <;> rfl

@[simp] theorem fillFromContext_spec_of_ne
    (s : Segment) {f g : Feature} (h : f ≠ g) (ctx : Segment) :
    (s.fillFromContext f ctx).spec g = s.spec g := by
  simp only [Segment.fillFromContext, Features.Bundle.merge,
    Function.update_of_ne (Ne.symm h)]
  cases s.spec g <;> rfl

end Segment

end Phonology

/-!
## Feature geometry [clements-1985] [sagey-1986]

Hierarchical organization of phonological features following the standard
feature geometry model — the hierarchical organization of autosegmental
tiers ([clements-hume-1995]). The tree synthesizes three sources:

- **[clements-1985]**: root, laryngeal, supralaryngeal, and place nodes
- **[sagey-1986]**: articulator sub-nodes under Place (labial, coronal, dorsal);
  soft palate node under Supralaryngeal
- **[hayes-2009]**: complete 26-feature inventory mapped to geometric nodes

    Root [±syll, ±cons, ±son, ±approx, ±del.rel., ±tap, ±trill]
    ├── Laryngeal [±voice, ±s.g., ±c.g.]
    └── Supralaryngeal [±cont]
        ├── Soft Palate [±nasal]
        └── Place
            ├── Labial [±lab, ±round, ±labiodental]
            ├── Coronal [±cor, ±ant, ±dist, ±lat, ±strid]
            └── Dorsal [±dor, ±high, ±low, ±front, ±back, ±tense]

The flat classification predicates in `Feature.lean` (`isMajorClass`, `isPlace`)
do not exactly correspond to any single geometric node —
see the subsumption theorems below.
-/

namespace Phonology.FeatureGeometry

-- ============================================================================
-- § 1: Geometric Nodes
-- ============================================================================

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

-- ============================================================================
-- § 2: Tree Structure
-- ============================================================================

/-- Parent of each node in the geometry tree. The supralaryngeal node
    ([clements-1985], diagram (4)) mediates between root and place. -/
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

/-- Depth of a node in the tree (root = 0). -/
def GeomNode.depth : GeomNode → Nat
  | .root => 0
  | .laryngeal | .supralaryngeal => 1
  | .softPalate | .place => 2
  | .labial | .coronal | .dorsal => 3

-- ============================================================================
-- § 4: Dominance
-- ============================================================================

/-- Does node `n` dominate node `m`? Reflexive-transitive closure of the
    parent relation, unrolled to depth 3 (the tree's maximum depth). -/
@[reducible] def GeomNode.Dominates (n m : GeomNode) : Prop :=
  n = m ∨ m.parent = some n ∨
    (m.parent.bind GeomNode.parent) = some n ∨
    ((m.parent.bind GeomNode.parent).bind GeomNode.parent) = some n

end Phonology.FeatureGeometry

-- ============================================================================
-- § 3: Feature-to-Node Mapping
-- ============================================================================

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

-- ============================================================================
-- § 5–7: Natural Classes, Verification, Spreading/Delinking
-- ============================================================================

namespace Phonology.FeatureGeometry

/-- Features dominated by node `n` — a natural class in the feature-geometric
    sense: the features that pattern together under processes targeting `n`. -/
def GeomNode.features (n : GeomNode) : List Feature :=
  Feature.allFeatures.filter (λ f => decide (GeomNode.Dominates n f.node))

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
theorem softPalate_depth : GeomNode.softPalate.depth = 2 := rfl
theorem place_depth : GeomNode.place.depth = 2 := rfl
theorem labial_depth : GeomNode.labial.depth = 3 := rfl
theorem coronal_depth : GeomNode.coronal.depth = 3 := rfl
theorem dorsal_depth : GeomNode.dorsal.depth = 3 := rfl

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
-- isMajorClass has no single geometric counterpart: its features are
-- distributed across root, supralaryngeal, softPalate, and coronal.

theorem IsLaryngeal_iff_laryngeal_DominatedBy (f : Feature) :
    f.IsLaryngeal ↔ f.DominatedBy .laryngeal := by
  cases f <;> decide

theorem IsDorsal_iff_dorsal_DominatedBy (f : Feature) :
    f.IsDorsal ↔ f.DominatedBy .dorsal := by
  cases f <;> decide

-- IsPlace is a strict subset of geometric place dominance
-- (IsMajorClass features like lateral and strident are geometrically under coronal)
theorem IsPlace_implies_place_DominatedBy (f : Feature) :
    f.IsPlace → f.DominatedBy .place := by
  cases f <;> decide

theorem lateral_geometrically_under_place :
    Feature.lateral.DominatedBy .place := by decide

theorem strident_geometrically_under_place :
    Feature.strident.DominatedBy .place := by decide

-- ============================================================================
-- § 7: Spreading / Delinking Predicates
-- ============================================================================

/-- Can feature `f` spread under node `n`? True when `f` is dominated by `n`. -/
@[reducible] def CanSpreadUnder (n : GeomNode) (f : Feature) : Prop :=
  GeomNode.Dominates n f.node

/-- Does delinking node `n` remove feature `f`? True when `n` dominates `f`'s
    node and `n` is not Root (delinking Root = deleting the segment). -/
@[reducible] def DelinkedBy (n : GeomNode) (f : Feature) : Prop :=
  GeomNode.Dominates n f.node ∧ n ≠ .root

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
stops [ⁿd], [ᵐb]).

The distinction was established by [sagey-1986] and is now standard
in phonological theory. The feature geometry predicts exactly which
complex segments are possible: only those combining *distinct* articulator
nodes. Palatal–velar stops are impossible because both use the dorsal
articulator; labio-velars are possible because labial and dorsal are
independent.
-/

namespace Phonology.FeatureGeometry

/-- Is this a place articulator node? The three place articulators —
    labial (lips), coronal (tongue blade/tip), dorsal (tongue body) —
    are the independent articulators whose combinations give rise to
    complex segments ([sagey-1986] Ch. 2). The soft palate is an
    articulator in the vocal tract but sits outside the place node
    (as a sibling under supralaryngeal), so it does not participate
    in complex segment formation: a velar nasal [ŋ] is simple despite
    activating both dorsal and soft palate. -/
def GeomNode.IsArticulator : GeomNode → Prop
  | .labial | .coronal | .dorsal => True
  | _ => False

instance : DecidablePred GeomNode.IsArticulator := fun n => by
  cases n <;> unfold GeomNode.IsArticulator <;> infer_instance

-- ============================================================================
-- § 1: Articulator Nodes
-- ============================================================================

/-- The articulator nodes in the geometry. -/
def articulatorNodes : List GeomNode :=
  GeomNode.allNodes.filter (fun n => decide (GeomNode.IsArticulator n))

theorem articulatorNodes_count : articulatorNodes.length = 3 := rfl

-- ============================================================================
-- § 4: Geometry of articulators (verification)
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

end Phonology.FeatureGeometry

namespace Phonology

open Phonology.FeatureGeometry (GeomNode articulatorNodes)

-- ============================================================================
-- § 2: Active articulators of a segment
-- ============================================================================

/-- Which articulator nodes have at least one specified feature in segment `s`? -/
def Segment.activeArticulators (s : Segment) : List GeomNode :=
  articulatorNodes.filter λ n =>
    n.features.any λ f => s.spec f |>.isSome

/-- Number of active articulator nodes in a segment. -/
def Segment.articulatorCount (s : Segment) : Nat :=
  s.activeArticulators.length

-- ============================================================================
-- § 3: Segment classification + well-formedness
-- ============================================================================

/-- A complex segment has two or more simultaneously active articulator
    nodes — e.g., labiovelars [k͡p] (labial + dorsal). -/
def Segment.IsComplex (s : Segment) : Prop :=
  s.articulatorCount ≥ 2

instance : DecidablePred Segment.IsComplex := fun _ =>
  inferInstanceAs (Decidable (_ ≥ _))

/-- Complex segment well-formedness: active articulators must be distinct
    nodes. This is trivially satisfied by `activeArticulators` (which returns
    a duplicate-free sublist of `articulatorNodes`), but we state it
    explicitly as the standard WFC. -/
def Segment.ComplexWF (s : Segment) : Prop :=
  let aa := s.activeArticulators
  aa.length = aa.eraseDups.length

instance : DecidablePred Segment.ComplexWF := fun _ =>
  inferInstanceAs (Decidable (_ = _))

end Phonology
