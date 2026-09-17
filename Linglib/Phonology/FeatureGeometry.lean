import Mathlib.Data.Finset.Piecewise
import Mathlib.Order.Comparable
import Mathlib.Order.SuccPred.Archimedean

/-!
# Feature geometry

A feature geometry over a feature type `F` places each feature below at most one node of a
rooted tree of class nodes, and the natural class of a node is the set of features placed at
or below it. The tree is mathlib's, a partial order with a bottom, a predecessor and archimedean
descent, so natural classes are the preimages of principal upper sets: they shrink along
dominance and are disjoint across incomparable nodes. Spreading a class from one segment onto
another is `Finset.piecewise` on it, and agreement on a class is `Set.EqOn`. The trees of
Clements, Sagey and Halle, Vaux and Wolfe are instances in their studies, as is the person and
number geometry of Harley and Ritter, whose nodes are its features.

## Main definitions

* `FeatureGeometry` — the placement of features below the nodes of a tree.
* `FeatureGeometry.naturalClass` — the features placed at or below a node.

## Main results

* `antitone_naturalClass`, `disjoint_naturalClass` — natural classes shrink along dominance
  and are disjoint across incomparable nodes.
* `eqOn_piecewise_of_le`, `eqOn_piecewise_of_incompRel` — spreading a node carries every
  class it dominates and leaves every incomparable class untouched.

## Implementation notes

The placement is `Option`-valued so that a geometry may leave features of the inventory
unplaced. A finite tree is built from its parent map by `PartialOrder.ofPred` and its
companions in `Core/Order/SuccPred/Tree.lean`. Spreading any set of terminals, Halle, Vaux and
Wolfe's partial spreading, is `Finset.piecewise` on that set, and single-feature spreading is
`Bundle.assimilate`.

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

/-- A feature geometry over the features `F`: each feature placed below at most one node of a
rooted tree of class nodes. -/
class FeatureGeometry (F : outParam (Type*)) (N : Type*) where
  /-- The node a feature is placed below, if the geometry places it. -/
  node : F → Option N

namespace FeatureGeometry

variable {F N : Type*} [PartialOrder N] [FeatureGeometry F N] [DecidableLE N] [Fintype F]

/-! ### Natural classes -/

/-- The natural class of a node: the features placed at or below it. -/
def naturalClass (a : N) : Finset F :=
  Finset.univ.filter fun f ↦ ∃ m ∈ (node f : Option N), a ≤ m

variable {a b : N} {f : F}

theorem mem_naturalClass : f ∈ naturalClass a ↔ ∃ m ∈ (node f : Option N), a ≤ m := by
  simp [naturalClass]

/-- The root's class is every placed feature: spreading it is total assimilation. -/
theorem mem_naturalClass_bot [OrderBot N] :
    f ∈ naturalClass (⊥ : N) ↔ (node f : Option N).isSome := by
  simp [mem_naturalClass, Option.isSome_iff_exists]

/-- Natural classes shrink along dominance. -/
theorem antitone_naturalClass : Antitone (naturalClass : N → Finset F) :=
  fun _ _ h _ hg ↦ by
    rw [mem_naturalClass] at hg ⊢
    obtain ⟨m, hm, hbm⟩ := hg
    exact ⟨m, hm, h.trans hbm⟩

/-- Incomparable nodes have disjoint natural classes: the nodes dominating a feature's node
are linearly ordered. -/
theorem disjoint_naturalClass [PredOrder N] [IsPredArchimedean N] (h : IncompRel (· ≤ ·) a b) :
    Disjoint (naturalClass a) (naturalClass b) := by
  rw [Finset.disjoint_left]
  intro g hga hgb
  rw [mem_naturalClass] at hga hgb
  obtain ⟨m, hm, ham⟩ := hga
  obtain ⟨m', hm', hbm⟩ := hgb
  rw [Option.mem_def] at hm hm'
  rw [hm, Option.some.injEq] at hm'
  subst hm'
  exact (le_total_of_directed ham hbm).elim h.2 h.1

/-! ### Spreading -/

variable [DecidableEq F] {β : Type*} (src tgt : F → β)

/-- Spreading node `a` from `src` onto `tgt` carries every class `a` dominates. -/
theorem eqOn_piecewise_of_le (h : a ≤ b) :
    Set.EqOn ((naturalClass a).piecewise src tgt) src ↑(naturalClass b) :=
  fun _ hg ↦ Finset.piecewise_eq_of_mem _ _ _ (antitone_naturalClass h hg)

/-- Spreading node `a` leaves every class incomparable with `a` untouched. -/
theorem eqOn_piecewise_of_incompRel [PredOrder N] [IsPredArchimedean N]
    (h : IncompRel (· ≤ ·) a b) :
    Set.EqOn ((naturalClass a).piecewise src tgt) tgt ↑(naturalClass b) :=
  fun _ hg ↦
    Finset.piecewise_eq_of_notMem _ _ _ (Finset.disjoint_right.1 (disjoint_naturalClass h) hg)

end FeatureGeometry

end Phonology
