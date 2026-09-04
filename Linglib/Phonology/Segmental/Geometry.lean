import Linglib.Phonology.Segmental.Defs
import Linglib.Core.Data.Fintype.Sets
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Finset.Card
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Interval.Set.Defs

/-!
# Feature geometry

A feature geometry is a finite rooted tree of class nodes with each terminal feature attached
below at most one node: dominance is `≤`, the root is `⊥`, and every principal downset is a
chain, so the natural classes (the features a node dominates) are nested along dominance and
disjoint across incomparable nodes. The class-node idea and the thesis that assimilation
spreads a single node are [clements-1985]'s; the articulator nodes are [sagey-1986]'s;
[halle-vaux-wolfe-2000] lists the four innovations since then (Unified Feature Theory,
Vowel-Place Theory, Partial Spreading, Strict Locality) and records that no consensus exists on
which to adopt, while [padgett-2002] drops constituency and lets constraints refer to classes as
sets. Current analyses refer to classes rather than to trees — [brown-meyer-2024]'s
AGREE[place] is agreement on the place features — so the class-set is the primitive here:
`FeatureGeometry` is a typeclass any node type can instantiate, natural classes are `Finset`s,
spreading a class from `src` onto `tgt` is `Finset.piecewise`, and agreement on a class is
`Set.EqOn`. The only instance in the substrate is the theory-neutral `Feature.Category`
grouping of [hayes-2009]'s chart (manner, laryngeal, labial, coronal, dorsal under a root),
with Place the union of the three articulator classes rather than a node; the trees of
[clements-1985], [sagey-1986] and [halle-vaux-wolfe-2000] are instances in their studies.

## Main definitions

* `FeatureGeometry` — the class: `isChain_Iic` (principal downsets are chains) and `node`
  (each feature's class node, if any).
* `FeatureGeometry.naturalClass` — the features a node dominates.
* `Feature.Category`, `Feature.category`, `Feature.Category.place` — the consensus grouping
  and the place class.
* `Segment.articulators`, `Segment.IsComplex` — designated articulators as features and
  complex segments.

## Main results

* `naturalClass_anti`, `disjoint_naturalClass` — natural classes shrink along dominance and
  are disjoint across incomparable nodes.
* `eqOn_piecewise_of_le`, `eqOn_piecewise_of_not_le` — spreading a node carries every class it
  dominates and leaves every incomparable class untouched.
* `mem_naturalClass_bot` — the root's class is every attached feature: total assimilation.

## Implementation notes

Instances build dominance from a parent function: `up n` is `n` with its ancestors,
`PartialOrder.lift up` is dominance, the root is `⊥`, and the chain axiom is `decide`d.
`node` is `Option`-valued so a geometry may leave features unplaced; the consensus grouping is
total. Spreading an arbitrary set of terminals ([halle-vaux-wolfe-2000]'s partial spreading,
[padgett-2002]'s partial class behaviour) is `Finset.piecewise` on that set with no further
apparatus, and single-feature spreading is `Features.Bundle.assimilate`
(`Finset.piecewise_singleton`). The linking of a spread node to several anchors is the
tier-association object `AR` (`Autosegmental/AR.lean`), not recorded on segments.

## References

* [clements-1985] — class nodes and single-node spreading.
* [sagey-1986] — articulator nodes and complex segments.
* [halle-vaux-wolfe-2000] — the four innovations and the absence of consensus (§1.1),
  designated articulators as features (§1.2.2), terminal spreading (§1.2.3).
* [padgett-2002] — feature classes as sets targeted by constraints.
* [brown-meyer-2024] — AGREE[place] and AGREE[voice] over classes.
* [hayes-2009] — the feature inventory and its chart grouping.
-/

namespace Phonology

/-! ### The class -/

/-- A feature geometry: a finite rooted tree of class nodes — dominance `≤`, root `⊥`, every
principal downset a chain — with each terminal feature attached below at most one node. -/
class FeatureGeometry (N : Type*) [PartialOrder N] [OrderBot N] where
  /-- Every principal downset is a chain: the nodes dominating a node are linearly ordered. -/
  isChain_Iic (c : N) : IsChain (· ≤ ·) (Set.Iic c)
  /-- The class node a terminal feature hangs from, if the geometry places it. -/
  node : Feature → Option N

namespace FeatureGeometry

variable {N : Type*} [PartialOrder N] [OrderBot N] [FeatureGeometry N] [DecidableLE N]

/-! ### Natural classes -/

/-- The natural class of a node: the features attached at or below it. -/
def naturalClass (a : N) : Finset Feature :=
  Finset.univ.filter λ f => ∃ m ∈ (node f : Option N), a ≤ m

variable {a b : N} {f : Feature}

theorem mem_naturalClass : f ∈ naturalClass a ↔ ∃ m ∈ (node f : Option N), a ≤ m := by
  simp [naturalClass]

/-- The root's class is every attached feature: spreading it is total assimilation. -/
theorem mem_naturalClass_bot : f ∈ naturalClass (⊥ : N) ↔ (node f : Option N).isSome := by
  simp [mem_naturalClass, Option.isSome_iff_exists]

/-- Natural classes shrink along dominance. -/
theorem naturalClass_anti (h : a ≤ b) : naturalClass b ⊆ naturalClass a := λ g hg => by
  rw [mem_naturalClass] at hg ⊢
  obtain ⟨m, hm, hbm⟩ := hg
  exact ⟨m, hm, h.trans hbm⟩

/-- Incomparable nodes have disjoint natural classes. -/
theorem disjoint_naturalClass (h₁ : ¬ a ≤ b) (h₂ : ¬ b ≤ a) :
    Disjoint (naturalClass a) (naturalClass b) := by
  rw [Finset.disjoint_left]
  intro g hga hgb
  rw [mem_naturalClass] at hga hgb
  obtain ⟨m, hm, ham⟩ := hga
  obtain ⟨m', hm', hbm⟩ := hgb
  rw [Option.mem_def] at hm hm'
  rw [hm, Option.some.injEq] at hm'
  subst hm'
  rcases eq_or_ne a b with rfl | hab
  · exact h₁ le_rfl
  · exact (isChain_Iic m ham hbm hab).elim h₁ h₂

/-! ### Spreading -/

variable (src tgt : Segment)

/-- Spreading node `a` from `src` onto `tgt` carries every class `a` dominates. -/
theorem eqOn_piecewise_of_le (h : a ≤ b) :
    Set.EqOn ((naturalClass a).piecewise src tgt) src ↑(naturalClass b) :=
  λ _ hg => Finset.piecewise_eq_of_mem _ _ _ (naturalClass_anti h hg)

/-- Spreading node `a` leaves every class incomparable with `a` untouched. -/
theorem eqOn_piecewise_of_not_le (h₁ : ¬ a ≤ b) (h₂ : ¬ b ≤ a) :
    Set.EqOn ((naturalClass a).piecewise src tgt) tgt ↑(naturalClass b) :=
  λ _ hg =>
    Finset.piecewise_eq_of_notMem _ _ _ (Finset.disjoint_right.1 (disjoint_naturalClass h₁ h₂) hg)

instance (s₁ s₂ : Segment) (a : N) : Decidable (Set.EqOn s₁ s₂ ↑(naturalClass a)) :=
  Set.decidableEqOnOfFintype _ _ _

end FeatureGeometry

/-! ### The consensus classification -/

/-- The theory-neutral grouping of the features, [hayes-2009]'s chart read as [padgett-2002]'s
classes: the manner and major-class features, the laryngeal features, and the features of the
three oral articulators, under a root standing for the whole segment. Place is the union of
the articulator classes and not a node, since whether it is a constituent and how vowel place
relates to it is where the geometries of `Studies/Clements1985.lean`, `Studies/Sagey1986.lean`
and `Studies/HalleVauxWolfe2000.lean` part ways. -/
inductive Feature.Category where
  | root | manner | laryngeal | labial | coronal | dorsal
  deriving DecidableEq, Repr, Fintype

namespace Feature.Category

/-- Every class hangs from the root. -/
def parent : Category → Option Category
  | .root => none
  | _ => some .root

/-- A class and its ancestors. -/
def up (c : Category) : Finset Category :=
  ((List.range 2).filterMap λ i => (· >>= parent)^[i] (some c)).toFinset

instance : PartialOrder Category := PartialOrder.lift up (by decide)

instance : DecidableLE Category := λ a b => inferInstanceAs (Decidable (up a ⊆ up b))

instance : OrderBot Category where
  bot := .root
  bot_le := by decide

end Feature.Category

/-- The class of each feature, by [hayes-2009]'s chart. -/
def Feature.category : Feature → Feature.Category
  | .syllabic | .consonantal | .sonorant | .approximant | .continuant | .delayedRelease
  | .nasal | .lateral | .strident | .tap | .trill => .manner
  | .voice | .spreadGlottis | .constrGlottis => .laryngeal
  | .labial | .round | .labiodental => .labial
  | .coronal | .anterior | .distributed => .coronal
  | .dorsal | .high | .low | .front | .back | .tense => .dorsal

instance : FeatureGeometry Feature.Category where
  isChain_Iic := by unfold IsChain Set.Pairwise; decide +revert
  node f := some f.category

open FeatureGeometry in
/-- The place class: the union of the three articulator classes ([padgett-2002] p. 83's
"Place simply stands for the set {[labial], [coronal], [dorsal], …}"). -/
def Feature.Category.place : Finset Feature :=
  naturalClass labial ∪ naturalClass coronal ∪ naturalClass dorsal

/-! ### Complex segments -/

/-- The designated articulators of a segment, as the articulator features it is specified `+`
for ([halle-vaux-wolfe-2000] §1.2.2). -/
def Segment.articulators (s : Segment) : Finset Feature :=
  ({.labial, .coronal, .dorsal} : Finset Feature).filter (s · = some true)

/-- A complex segment has more than one designated articulator: the labiovelar [k͡p] carries
[labial] and [dorsal], the labialised [kʷ] only [dorsal] beside [+round] ([sagey-1986];
[halle-vaux-wolfe-2000] p. 435). -/
def Segment.IsComplex (s : Segment) : Prop := 1 < s.articulators.card

instance : DecidablePred Segment.IsComplex := λ _ => inferInstanceAs (Decidable (1 < _))

end Phonology
