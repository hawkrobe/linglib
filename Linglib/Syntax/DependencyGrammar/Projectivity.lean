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

[kuhlmann-nivre-2006]'s hierarchy of structural constraints between
projective and unrestricted dependency structures: projectivity as
order-convexity of dominance cones (`Set.OrdConnected`; Definition 3),
planarity (Definition 4 — the Link Grammar notion, traced there to
[melcuk-1988]), gap degree (Definitions 6–7; gap degree + 1 is
[kuhlmann-2013]'s block-degree, the LCFRS fan-out), and well-nestedness
(Definition 8).

Of the §3.5 hierarchy `projective ⊂ planar ⊂ well-nested`,
`IsProjective.isPlanar` and `IsProjective.isWellNested` prove the
inclusions from projectivity on trees; strictness is witnessed by
`decide` on `planarNotProjective` (a single-rooted adaptation of
Figure 2a) and on `dutchCrossSerial` (well-nested but not planar),
[kuhlmann-2013] Figure 1's cross-serial half.
-/

namespace DependencyGrammar

open Morphology (Word)

section Defs

variable {n : ℕ}

/-! ### The binary constraints: projectivity, planarity, well-nestedness -/

/-- **Projectivity**: every dominance cone is order-convex. Equivalent
    to "the yields of all nodes are intervals"
    ([kuhlmann-nivre-2006], Definition 3). -/
def IsProjective (g : Graph n) : Prop :=
  ∀ v : Fin n, Set.OrdConnected {x | Dominates g v x}

/-- **Planarity**: no two links cross — spans, taken left-to-right, never
    strictly interleave. ([kuhlmann-nivre-2006], Definition 4; the Link
    Grammar notion, traced there to [melcuk-1988].) -/
def IsPlanar (g : Graph n) : Prop :=
  ∀ ⦃a b c d : Fin n⦄, a < b → c < d → Linked g a b → Linked g c d →
    ¬ (a < c ∧ c < b ∧ b < d)

/-- The subtrees at `v` and `w` interleave: each contributes two positions
    arranged strictly alternately. ([kuhlmann-nivre-2006], Definition 8) -/
def Interleave (g : Graph n) (v w : Fin n) : Prop :=
  ∃ a b, Dominates g v a ∧ Dominates g v b ∧
    ∃ c d, Dominates g w c ∧ Dominates g w d ∧ a < c ∧ c < b ∧ b < d

/-- **Well-nestedness**: disjoint subtrees (neither root dominating the
    other) never interleave. ([kuhlmann-nivre-2006], Definition 8) -/
def IsWellNested (g : Graph n) : Prop :=
  ∀ v w : Fin n, ¬ Dominates g v w → ¬ Dominates g w v → ¬ Interleave g v w

instance (g : Graph n) : Decidable (IsProjective g) :=
  decidable_of_iff (∀ v x, Dominates g v x → ∀ y, Dominates g v y → x ≤ y →
      ∀ z, x ≤ z → z ≤ y → Dominates g v z) <| by
    simp only [IsProjective, Set.ordConnected_iff, Set.subset_def, Set.mem_Icc,
      Set.mem_setOf_eq, and_imp]

instance (g : Graph n) : Decidable (IsPlanar g) :=
  inferInstanceAs (Decidable (∀ _, _))

instance (g : Graph n) (v w : Fin n) : Decidable (Interleave g v w) :=
  inferInstanceAs (Decidable (∃ _, _))

instance (g : Graph n) : Decidable (IsWellNested g) :=
  inferInstanceAs (Decidable (∀ _, _))

/-! ### The hierarchy on trees -/

/-- On trees, projective structures are planar ([kuhlmann-nivre-2006]
    §3.5): were two links to cross, convexity of the heads' cones and
    uniqueness of heads would force two distinct positions to dominate
    each other. -/
theorem IsProjective.isPlanar {g : Graph n} (hT : g.IsTree)
    (hP : IsProjective g) : IsPlanar g := by
  rintro a b c d hab hcd hL1 hL2 ⟨hac, hcb, hbd⟩
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

/-- On trees, projective structures are well-nested
    ([kuhlmann-nivre-2006] §3.5): interleaving would put a position
    under both subtree roots, which dominance comparability forbids. -/
theorem IsProjective.isWellNested {g : Graph n} (hT : g.IsTree)
    (hP : IsProjective g) : IsWellNested g := by
  rintro v w hvw hwv ⟨a, b, hva, hvb, c, _, hwc, _, hac, hcb, _⟩
  exact (Dominates.comparable hT ((hP v).out hva hvb ⟨hac.le, hcb.le⟩) hwc).elim
    hvw hwv

/-! ### Gap degree -/

/-- The projection as position values, for the gap combinatorics. -/
def projectionVals (g : Graph n) (v : Fin n) : List Nat :=
  (projection g v).map (·.val)

/-- The projection is strictly sorted: it filters the ascending
    `finRange`. -/
theorem projectionVals_sortedLT (g : Graph n) (v : Fin n) :
    (projectionVals g v).SortedLT := by
  refine List.Pairwise.sortedLT (List.Pairwise.map _ (λ _ _ h => h) ?_)
  exact (List.pairwise_lt_finRange n).filter _

/-- **Gap degree** of a position: the discontinuities in its projection —
    adjacent projection members more than one position apart.
    ([kuhlmann-nivre-2006], Definition 6) -/
def gapDegreeAt (g : Graph n) (v : Fin n) : Nat :=
  ((projectionVals g v).zip (projectionVals g v).tail).countP
    (λ p => decide (1 < p.2 - p.1))

/-- **Gap degree** of a graph: the maximum over positions
    ([kuhlmann-nivre-2006], Definition 7). Gap degree 0 is the paper's
    characterization of projectivity, and gap degree + 1 is
    [kuhlmann-2013]'s block-degree — the fan-out of the LCFRS rule
    extracted at a node, whose boundedness (with well-nestedness) gives
    polynomial parsing. -/
def Graph.gapDegree (g : Graph n) : Nat :=
  Finset.univ.sup (gapDegreeAt g)

end Defs

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
example : ¬ IsPlanar dutchCrossSerial := by decide
example : ¬ IsProjective dutchCrossSerial := by decide
example : IsWellNested dutchCrossSerial := by decide
example : IsPlanar germanNested := by decide
example : IsProjective germanNested := by decide
example : IsPlanar planarNotProjective := by decide
example : ¬ IsProjective planarNotProjective := by decide
example : dutchCrossSerial.gapDegree = 1 := by decide
example : germanNested.gapDegree = 0 := by decide

end DependencyGrammar
