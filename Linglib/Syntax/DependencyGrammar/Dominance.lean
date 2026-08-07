/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.DependencyGrammar.Basic
import Linglib.Core.Relation.ReflTransGen
import Mathlib.Logic.Relation

/-!
# Dominance

Dominance as the reflexive-transitive closure of the arc relation, the
projection (yield) it induces, tree well-formedness, and the order
theory of dominance on trees ([kuhlmann-nivre-2006] §2).

## Main declarations

* `Dominates`, `projection`, `mem_projection_iff` — the dominance
  relation, the yield of a position in ascending order, and the bridge
  between them.
* `Graph.IsTree` — no arc into the root, unique heads elsewhere,
  acyclicity; decidable.
* `Dominates.antisymm`, `Dominates.to_head`, `Dominates.comparable` —
  on trees dominance is a partial order under which the dominators of
  any position form a chain.

## Implementation notes

`Dominates` is an `abbrev` for `Relation.ReflTransGen g.Adj`, so
mathlib's closure API (`.refl`, `.tail`, `.trans`, `.single`,
`cases_tail`, `total_of_right_unique`, …) applies to dominance facts
directly; this file adds only what mentions the dependency carrier.
Decidability comes from `Core/Relation/ReflTransGen.lean`.
-/

namespace DependencyGrammar

section Dominance

variable {n : ℕ}

/-- `v` dominates `x` if a (possibly empty) chain of arcs leads from `v`
    to `x` ([kuhlmann-nivre-2006] §2). -/
abbrev Dominates (g : Graph n) : Fin n → Fin n → Prop :=
  Relation.ReflTransGen g.Adj

instance (g : Graph n) : DecidableRel (Dominates g) :=
  Relation.ReflTransGen.decidable_of_finite (List.finRange n)
    (λ _ b _ => List.mem_finRange b)

/-- **Projection** π(v): the yield of position v — all positions it
    dominates, including itself — in ascending position order
    ([kuhlmann-nivre-2006] §2). -/
def projection (g : Graph n) (v : Fin n) : List (Fin n) :=
  (List.finRange n).filter (λ x => decide (Dominates g v x))

@[simp] theorem mem_projection_iff {g : Graph n} {v x : Fin n} :
    x ∈ projection g v ↔ Dominates g v x := by
  simp [projection]

/-! ### Well-formedness -/

/-- The graph is a dependency tree: nothing points at the root, every other
    position has exactly one head, and no position dominates itself. On
    `Fin n` these imply rootedness and connectivity — every non-root
    position's head chain terminates at the unique headless position. -/
structure Graph.IsTree (g : Graph n) : Prop where
  not_adj_root : ∀ v, ¬ g.Adj v g.root
  existsUnique_adj : ∀ w, w ≠ g.root → ∃! v, g.Adj v w
  acyclic : ∀ v, ¬ Relation.TransGen g.Adj v v

theorem Graph.isTree_iff (g : Graph n) :
    g.IsTree ↔ (∀ v, ¬ g.Adj v g.root) ∧
      (∀ w, w ≠ g.root → ∃! v, g.Adj v w) ∧
      (∀ v, ¬ Relation.TransGen g.Adj v v) :=
  ⟨λ h => ⟨h.1, h.2, h.3⟩, λ h => ⟨h.1, h.2.1, h.2.2⟩⟩

instance (g : Graph n) (v w : Fin n) : Decidable (Relation.TransGen g.Adj v w) :=
  decidable_of_iff (∃ u, g.Adj v u ∧ Dominates g u w)
    Relation.TransGen.head'_iff.symm

instance (g : Graph n) (w : Fin n) : Decidable (∃! v, g.Adj v w) :=
  decidable_of_iff (∃ v, g.Adj v w ∧ ∀ u, g.Adj u w → u = v) Iff.rfl

instance (g : Graph n) : Decidable g.IsTree :=
  decidable_of_iff _ (g.isTree_iff).symm

/-! ### Dominance as an order on trees -/

variable {g : Graph n} {v w : Fin n}

/-- In a tree, a position has at most one head. -/
theorem Graph.IsTree.rightUnique_flip_adj (hT : g.IsTree) :
    Relator.RightUnique (flip g.Adj) := by
  intro y u u' hu hu'
  have hy : y ≠ g.root := λ he => hT.not_adj_root u (he ▸ hu)
  obtain ⟨z, _, hz⟩ := hT.existsUnique_adj y hy
  exact (hz u hu).trans (hz u' hu').symm

/-- No arc closes a dominance cycle, on acyclic graphs. -/
theorem not_adj_dominates (hacyc : ∀ v, ¬ Relation.TransGen g.Adj v v)
    (hadj : g.Adj v w) (hdom : Dominates g w v) : False :=
  hacyc v (Relation.TransGen.head' hadj hdom)

/-- Dominance is antisymmetric on acyclic graphs. -/
theorem Dominates.antisymm (hacyc : ∀ v, ¬ Relation.TransGen g.Adj v v)
    (hvw : Dominates g v w) (hwv : Dominates g w v) : v = w := by
  rcases Relation.ReflTransGen.cases_head hvw with rfl | ⟨u, hvu, huw⟩
  · rfl
  · exact absurd (huw.trans hwv) (λ h => not_adj_dominates hacyc hvu h)

/-- A strict dominator of `w` dominates `w`'s head. -/
theorem Dominates.to_head {u : Fin n} (hT : g.IsTree)
    (hvw : Dominates g v w) (hne : v ≠ w) (hu : g.Adj u w) :
    Dominates g v u := by
  rcases Relation.ReflTransGen.cases_tail hvw with rfl | ⟨z, hvz, hzw⟩
  · exact absurd rfl hne
  · exact hT.rightUnique_flip_adj hzw hu ▸ hvz

/-- On a tree, positions dominating a common position are comparable:
    the dominators of any position form a chain. -/
theorem Dominates.comparable {x : Fin n} (hT : g.IsTree)
    (hv : Dominates g v x) (hw : Dominates g w x) :
    Dominates g v w ∨ Dominates g w v :=
  (Relation.ReflTransGen.total_of_right_unique hT.rightUnique_flip_adj
      (Relation.reflTransGen_swap.mpr hv)
      (Relation.reflTransGen_swap.mpr hw)).symm.imp
    Relation.reflTransGen_swap.mp Relation.reflTransGen_swap.mp

end Dominance

end DependencyGrammar
