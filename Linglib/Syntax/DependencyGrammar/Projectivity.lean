/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.DependencyGrammar.Dominance
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Sort

/-!
# Projectivity and its relaxations

A dependency graph is projective when the positions each node dominates form
a contiguous stretch of the sentence. Natural language is not always
projective, so the literature weakens the constraint in several directions.
Planarity bans crossing arcs, well-nestedness bans interleaved subtrees, and
gap degree counts the discontinuities a single node may show.

In this file we define those constraints and prove the inclusions among them
that hold on trees. The fixtures witness that the constraints are genuinely
distinct: `planarNotProjective` is planar but not projective, and
`dutchCrossSerial` is well-nested but not planar.

## Main declarations

* `Graph.yield`, `Alternate` — the positions a node dominates, and the
  alternation `a < c < b < d` that both binary constraints forbid.
* `Graph.IsProjective` — the yields are intervals (Definition 3).
* `Graph.IsPlanar` — no two links cross (Definition 4), the Link Grammar
  notion, traced there to [melcuk-1988].
* `Graph.Interleave`, `Graph.IsWellNested` — Definition 8.
* `Graph.gapDegree` — Definitions 6–7. Gap degree + 1 is the block-degree,
  the fan-out of the LCFRS rule extracted for that node.
* `Graph.IsProjective.isPlanar`, `Graph.IsProjective.isWellNested` — the
  inclusions from projectivity.

## References

[kuhlmann-nivre-2006] — Mildly non-projective dependency structures, source
of the Definition numbers cited above and, in Figure 2a, of the forest that
`planarNotProjective` adapts to a single root
[kuhlmann-2013] — Mildly non-projective dependency grammar, whose Figure 1
is the `dutchCrossSerial`/`germanNested` pair
[melcuk-1988] — Dependency syntax: theory and practice
-/

namespace DependencyGrammar

open Morphology (Word)

variable {n : ℕ} (g : Graph n)

/-! ### The binary constraints: projectivity, planarity, well-nestedness -/

/-- The yield of `v` is the set of positions `v` dominates. `projection`
    lists the same positions in ascending order. -/
def Graph.yield (v : Fin n) : Set (Fin n) := {x | Dominates g v x}

@[simp] theorem Graph.mem_yield {g : Graph n} {v x : Fin n} :
    x ∈ g.yield v ↔ Dominates g v x := Iff.rfl

instance (v : Fin n) : DecidablePred (· ∈ g.yield v) :=
  λ x => inferInstanceAs (Decidable (Dominates g v x))

/-- A dependency graph is projective if the yield of every position is
    order-convex. -/
def Graph.IsProjective : Prop := ∀ v, (g.yield v).OrdConnected

/-- Positions `a b c d` alternate if `a < c < b < d`, so that the pairs
    `{a, b}` and `{c, d}` strictly interleave. -/
def Alternate (a b c d : Fin n) : Prop := a < c ∧ c < b ∧ b < d

instance (a b c d : Fin n) : Decidable (Alternate a b c d) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A dependency graph is planar if no two links alternate, so that its arcs
    can be drawn above the sentence without crossing. -/
def Graph.IsPlanar : Prop :=
  ∀ ⦃a b c d : Fin n⦄, Linked g a b → Linked g c d → ¬ Alternate a b c d

/-- The subtrees at `v` and `w` interleave if each contributes two positions
    and the two pairs alternate. -/
def Graph.Interleave (v w : Fin n) : Prop :=
  ∃ a ∈ g.yield v, ∃ b ∈ g.yield v, ∃ c ∈ g.yield w, ∃ d ∈ g.yield w,
    Alternate a b c d

/-- A dependency graph is well-nested if interleaved subtrees are never
    disjoint, one of the two roots always dominating the other. -/
def Graph.IsWellNested : Prop :=
  ∀ v w : Fin n, g.Interleave v w → Dominates g v w ∨ Dominates g w v

theorem Graph.isProjective_iff :
    g.IsProjective ↔ ∀ v x y, Dominates g v x → Dominates g v y →
      ∀ z, x ≤ z → z ≤ y → Dominates g v z := by
  simp only [IsProjective, Set.ordConnected_def, Set.subset_def, Set.mem_Icc,
    Graph.mem_yield, and_imp]
  exact ⟨λ h v x y hx hy z h1 h2 => h v hx hy z h1 h2,
         λ h v x hx y hy z h1 h2 => h v x y hx hy z h1 h2⟩

instance : Decidable g.IsProjective := decidable_of_iff _ g.isProjective_iff.symm
instance : Decidable g.IsPlanar := inferInstanceAs (Decidable (∀ _, _))
instance (v w : Fin n) : Decidable (g.Interleave v w) :=
  inferInstanceAs (Decidable (∃ _, _))
instance : Decidable g.IsWellNested := inferInstanceAs (Decidable (∀ _, _))

/-! ### Gap degree -/

/-- The projection of `v`, as position values. -/
def Graph.projectionVals (v : Fin n) : List Nat := (projection g v).map (·.val)

theorem Graph.projectionVals_sortedLT (v : Fin n) :
    (g.projectionVals v).SortedLT := by
  refine List.Pairwise.sortedLT (List.Pairwise.map _ (λ _ _ h => h) ?_)
  exact (List.pairwise_lt_finRange n).filter _

/-- The gap degree of a position counts the discontinuities in its
    projection, the adjacent members more than one position apart. -/
def Graph.gapDegreeAt (v : Fin n) : Nat :=
  ((g.projectionVals v).zip (g.projectionVals v).tail).countP
    (λ p => decide (1 < p.2 - p.1))

/-- The gap degree of a graph is the maximum over its positions. -/
def Graph.gapDegree : Nat := Finset.univ.sup g.gapDegreeAt

/-! ### The hierarchy on trees -/

variable {g}

/-- Every projective tree is planar. -/
theorem Graph.IsProjective.isPlanar (hT : g.IsTree) (hP : g.IsProjective) :
    g.IsPlanar := by
  rintro a b c d hL1 hL2 ⟨hac, hcb, hbd⟩
  rcases hL1 with h1 | h1 <;> rcases hL2 with h2 | h2
  · -- heads a and c
    have hac' : Dominates g a c := (hP a).out .refl (.single h1) ⟨hac.le, hcb.le⟩
    have hcb' : Dominates g c b := (hP c).out .refl (.single h2) ⟨hcb.le, hbd.le⟩
    exact hac.ne (Dominates.antisymm hT.acyclic hac'
      (Dominates.to_head hT hcb' hcb.ne h1))
  · -- heads a and d
    have hac' : Dominates g a c := (hP a).out .refl (.single h1) ⟨hac.le, hcb.le⟩
    have hdb' : Dominates g d b := (hP d).out (.single h2) .refl ⟨hcb.le, hbd.le⟩
    exact ((hac.trans hcb).trans hbd).ne (Dominates.antisymm hT.acyclic
      (Dominates.to_head hT hac' hac.ne h2) (Dominates.to_head hT hdb' hbd.ne' h1))
  · -- heads b and c
    have hbc' : Dominates g b c := (hP b).out (.single h1) .refl ⟨hac.le, hcb.le⟩
    have hcb' : Dominates g c b := (hP c).out .refl (.single h2) ⟨hcb.le, hbd.le⟩
    exact hcb.ne (Dominates.antisymm hT.acyclic hcb' hbc')
  · -- heads b and d
    have hbc' : Dominates g b c := (hP b).out (.single h1) .refl ⟨hac.le, hcb.le⟩
    have hdb' : Dominates g d b := (hP d).out (.single h2) .refl ⟨hcb.le, hbd.le⟩
    exact hbd.ne (Dominates.antisymm hT.acyclic
      (Dominates.to_head hT hbc' hcb.ne' h2) hdb')

/-- Every projective tree is well-nested. -/
theorem Graph.IsProjective.isWellNested (hT : g.IsTree) (hP : g.IsProjective) :
    g.IsWellNested := by
  rintro v w ⟨a, hva, b, hvb, c, hwc, -, -, hac, hcb, -⟩
  exact Dominates.comparable hT ((hP v).out hva hvb ⟨hac.le, hcb.le⟩) hwc

/-! ### Canonical fixtures

[kuhlmann-2013] Figure 1: Dutch cross-serial dependencies against German
nested infinitives — same dependencies, opposite verb-cluster orders. -/

/-- Dutch cross-serial: "dat Jan Piet Marie zag helpen lezen". -/
def dutchCrossSerial : Graph 7 :=
  .ofArcs
    [Word.mk' "dat" .SCONJ, Word.mk' "Jan" .PROPN, Word.mk' "Piet" .PROPN,
     Word.mk' "Marie" .PROPN, Word.mk' "zag" .VERB, Word.mk' "helpen" .VERB,
     Word.mk' "lezen" .VERB]
    0
    [(0, 4, .dep), (4, 1, .nsubj), (4, 5, .xcomp),
     (5, 2, .nsubj), (5, 6, .xcomp), (6, 3, .nsubj)]

/-- German nested: "dass Jan Piet Marie lesen helfen sah". -/
def germanNested : Graph 7 :=
  .ofArcs
    [Word.mk' "dass" .SCONJ, Word.mk' "Jan" .PROPN, Word.mk' "Piet" .PROPN,
     Word.mk' "Marie" .PROPN, Word.mk' "lesen" .VERB, Word.mk' "helfen" .VERB,
     Word.mk' "sah" .VERB]
    0
    [(0, 6, .dep), (6, 1, .nsubj), (6, 5, .xcomp),
     (5, 2, .nsubj), (5, 4, .xcomp), (4, 3, .nsubj)]

/-- Planar but **not** projective — no crossing links, yet the yield of
    position 0 is not an interval. A single-rooted adaptation of
    [kuhlmann-nivre-2006] Figure 2a (whose witness is a forest). -/
def planarNotProjective : Graph 4 :=
  .ofArcs
    [Word.mk' "w0" .X, Word.mk' "w1" .X, Word.mk' "w2" .X, Word.mk' "w3" .X]
    2
    [(2, 0, .dep), (2, 1, .dep), (0, 3, .dep)]

example : dutchCrossSerial.IsTree := by decide
example : germanNested.IsTree := by decide
example : planarNotProjective.IsTree := by decide
example : ¬ dutchCrossSerial.IsPlanar := by decide
example : ¬ dutchCrossSerial.IsProjective := by decide
example : dutchCrossSerial.IsWellNested := by decide
example : germanNested.IsPlanar := by decide
example : germanNested.IsProjective := by decide
example : planarNotProjective.IsPlanar := by decide
example : ¬ planarNotProjective.IsProjective := by decide
example : dutchCrossSerial.gapDegree = 1 := by decide
example : germanNested.gapDegree = 0 := by decide

/-- The Dutch fixture as a bundled `Tree`: the dominance-order API
    applies with no side conditions. -/
def dutchTree : Tree 7 := .mk' dutchCrossSerial

example : (⊥ : DominanceOrder dutchTree.toGraph) = 0 := by decide
example : Order.pred (5 : DominanceOrder dutchTree.toGraph) = 4 := by decide

end DependencyGrammar
