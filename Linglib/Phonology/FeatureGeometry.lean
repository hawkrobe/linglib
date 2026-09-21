module

public import Linglib.Core.Order.SuccPred.Tree
public import Mathlib.Data.Finset.Piecewise

/-!
# Feature geometry

A feature geometry over a feature type `F` places each feature below at most one node of a
rooted tree of class nodes, a map `node : F → Option N`, and the natural class of a node is
the set of features placed at or below it. The tree is mathlib's, a partial order with a
bottom, a predecessor and archimedean descent, so natural classes are the preimages of
principal upper sets: they shrink along dominance and are disjoint across incomparable nodes.
Spreading a class from one segment onto another is `Finset.piecewise` on it, and agreement on
a class is `Set.EqOn`. The trees of Clements, Sagey and Halle, Vaux and Wolfe are built in
their studies.

## Main definitions

* `FeatureGeometry.naturalClass` — the features a placement puts at or below a node.

## Main results

* `antitone_naturalClass`, `disjoint_naturalClass` — natural classes shrink along dominance
  and are disjoint across incomparable nodes.
* `eqOn_piecewise_of_le`, `eqOn_piecewise_of_incompRel` — spreading a node carries every
  class it dominates and leaves every incomparable class untouched.

## Implementation notes

The placement is `Option`-valued so that a geometry may leave features of the inventory
unplaced. A study builds its tree from the parent map with the root fixed: `PartialOrder.lift`
along the set of a node's iterated parents, the root as `⊥`, and the parent as `Order.pred`,
every axiom decided. Spreading any set of terminals, Halle, Vaux and Wolfe's partial
spreading, is `Finset.piecewise` on that set, and single-feature spreading is
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

@[expose] public section

namespace Phonology.FeatureGeometry

variable {F N : Type*} [Fintype F] [Preorder N] [DecidableLE N] (node : F → Option N)

/-! ### Natural classes -/

/-- The natural class of a node: the features placed at or below it. -/
def naturalClass (a : N) : Finset F :=
  Finset.univ.filter fun f ↦ ∃ m ∈ node f, a ≤ m

variable {node} {a b : N} {f : F}

theorem mem_naturalClass : f ∈ naturalClass node a ↔ ∃ m ∈ node f, a ≤ m := by
  simp [naturalClass]

/-- The root's class is every placed feature: spreading it is total assimilation. -/
theorem mem_naturalClass_bot [OrderBot N] : f ∈ naturalClass node ⊥ ↔ (node f).isSome := by
  simp [mem_naturalClass, Option.isSome_iff_exists]

/-- Natural classes shrink along dominance. -/
theorem antitone_naturalClass : Antitone (naturalClass node) := fun _ _ h _ hg ↦ by
  rw [mem_naturalClass] at hg ⊢
  obtain ⟨m, hm, hbm⟩ := hg
  exact ⟨m, hm, h.trans hbm⟩

/-- Incomparable nodes have disjoint natural classes: their subtrees are disjoint. -/
theorem disjoint_naturalClass [PredOrder N] [IsPredArchimedean N] (h : IncompRel (· ≤ ·) a b) :
    Disjoint (naturalClass node a) (naturalClass node b) := by
  rw [Finset.disjoint_left]
  intro g hga hgb
  rw [mem_naturalClass] at hga hgb
  obtain ⟨m, hm, ham⟩ := hga
  obtain ⟨m', hm', hbm⟩ := hgb
  rw [Option.mem_def] at hm hm'
  rw [hm, Option.some.injEq] at hm'
  subst hm'
  exact Set.disjoint_left.1 (disjoint_Ici_of_incompRel h) ham hbm

/-! ### Spreading -/

variable [DecidableEq F] {β : Type*} (src tgt : F → β)

/-- Spreading node `a` from `src` onto `tgt` carries every class `a` dominates. -/
theorem eqOn_piecewise_of_le (h : a ≤ b) :
    Set.EqOn ((naturalClass node a).piecewise src tgt) src ↑(naturalClass node b) :=
  fun _ hg ↦ Finset.piecewise_eq_of_mem _ _ _ (antitone_naturalClass h hg)

/-- Spreading node `a` leaves every class incomparable with `a` untouched. -/
theorem eqOn_piecewise_of_incompRel [PredOrder N] [IsPredArchimedean N]
    (h : IncompRel (· ≤ ·) a b) :
    Set.EqOn ((naturalClass node a).piecewise src tgt) tgt ↑(naturalClass node b) :=
  fun _ hg ↦
    Finset.piecewise_eq_of_notMem _ _ _ (Finset.disjoint_right.1 (disjoint_naturalClass h) hg)

end Phonology.FeatureGeometry
