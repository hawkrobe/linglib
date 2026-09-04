import Linglib.Core.Data.Fintype.Sets
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Finset.Card
import Mathlib.Order.Preorder.Chain
import Mathlib.Order.Interval.Set.Defs

/-!
# Feature geometry

A feature geometry over a feature type `F` is a finite rooted tree of class nodes with each
feature attached below at most one node: dominance is `≤`, the root is `⊥`, every principal
downset is a chain, and the natural class of a node is the finite set of features it
dominates, so natural classes are nested along dominance and disjoint across incomparable
nodes. The class-node idea and the thesis that assimilation spreads one node are
Clements's; Halle, Vaux and Wolfe record that no consensus exists among the later
revisions and lets rules spread any set of terminals, and Padgett drops constituency
altogether and lets constraints refer to classes as sets, which is how current analyses use
them (Brown and Meyer's AGREE[place]). The class-set is therefore the primitive: spreading
a class from `src` onto `tgt` is `Finset.piecewise`, agreement on a class is `Set.EqOn`, and a
geometry is an instance naming which sets are natural. The feature type is a parameter, so an
instance may range over a binary inventory, over feature tokens indexed by position as in
Vowel-Place Theory, over privative elements, or over tone features; the flat segmental
classes are `Phonology/Segmental/FeatureClass.lean`, and the trees of Clements, Sagey
and Halle, Vaux and Wolfe are instances in their studies.

## Main definitions

* `FeatureGeometry` — the class: `isChain_Iic` (principal downsets are chains) and `node`
  (each feature's class node, if the geometry places it).
* `FeatureGeometry.naturalClass` — the features a node dominates.

## Main results

* `naturalClass_anti`, `disjoint_naturalClass` — natural classes shrink along dominance and
  are disjoint across incomparable nodes.
* `eqOn_piecewise_of_le`, `eqOn_piecewise_of_not_le` — spreading a node carries every class it
  dominates and leaves every incomparable class untouched.
* `mem_naturalClass_bot` — the root's class is every attached feature: total assimilation.

## Implementation notes

The feature type is an `outParam`: a node type determines its features. Instances build
dominance from a parent function: `up n` is `n` with its ancestors, `PartialOrder.lift up` is
dominance, the root is `⊥`, and the chain axiom is `decide`d. `node` is `Option`-valued so a
geometry may leave features unplaced. Spreading an arbitrary set of terminals
(Halle, Vaux and Wolfe's partial spreading, Padgett's partial class behaviour) is
`Finset.piecewise` on that set with no further apparatus, and single-feature spreading is
`Features.Bundle.assimilate` (`Finset.piecewise_singleton`). The linking of a spread node to
several anchors is the tier-association object `AR` (`Autosegmental/AR.lean`), not recorded
on feature bundles.

## References

* [G. N. Clements, *The Geometry of Phonological Features* (1985)][clements-1985]
* [M. Halle, B. Vaux and A. Wolfe, *On Feature Spreading and the Representation of Place of
  Articulation* (2000)][halle-vaux-wolfe-2000]
* [J. Padgett, *Feature Classes in Phonology* (2002)][padgett-2002]
* [J. Brown and J. Meyer, *Assimilation and Morpheme Boundaries in Mgira* (2024)][brown-meyer-2024]
* [E. C. Sagey, *The Representation of Features and Relations in Non-Linear Phonology*
  (1986)][sagey-1986]
-/

namespace Phonology

/-- A feature geometry over the features `F`: a finite rooted tree of class nodes — dominance
`≤`, root `⊥`, every principal downset a chain — with each feature attached below at most one
node. -/
class FeatureGeometry (F : outParam (Type*)) (N : Type*) [PartialOrder N] [OrderBot N] where
  /-- Every principal downset is a chain: the nodes dominating a node are linearly ordered. -/
  isChain_Iic (c : N) : IsChain (· ≤ ·) (Set.Iic c)
  /-- The class node a feature hangs from, if the geometry places it. -/
  node : F → Option N

namespace FeatureGeometry

variable {F N : Type*} [PartialOrder N] [OrderBot N] [FeatureGeometry F N] [DecidableLE N]
  [Fintype F]

/-! ### Natural classes -/

/-- The natural class of a node: the features attached at or below it. -/
def naturalClass (a : N) : Finset F :=
  Finset.univ.filter λ f => ∃ m ∈ (node f : Option N), a ≤ m

variable {a b : N} {f : F}

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

variable [DecidableEq F] {β : Type*} (src tgt : F → β)

/-- Spreading node `a` from `src` onto `tgt` carries every class `a` dominates. -/
theorem eqOn_piecewise_of_le (h : a ≤ b) :
    Set.EqOn ((naturalClass a).piecewise src tgt) src ↑(naturalClass b) :=
  λ _ hg => Finset.piecewise_eq_of_mem _ _ _ (naturalClass_anti h hg)

/-- Spreading node `a` leaves every class incomparable with `a` untouched. -/
theorem eqOn_piecewise_of_not_le (h₁ : ¬ a ≤ b) (h₂ : ¬ b ≤ a) :
    Set.EqOn ((naturalClass a).piecewise src tgt) tgt ↑(naturalClass b) :=
  λ _ hg =>
    Finset.piecewise_eq_of_notMem _ _ _ (Finset.disjoint_right.1 (disjoint_naturalClass h₁ h₂) hg)

instance [DecidableEq β] (s₁ s₂ : F → β) (a : N) : Decidable (Set.EqOn s₁ s₂ ↑(naturalClass a)) :=
  Set.decidableEqOnOfFintype _ _ _

end FeatureGeometry

end Phonology
