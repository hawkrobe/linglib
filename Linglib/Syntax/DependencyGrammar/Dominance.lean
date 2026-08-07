/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Syntax.DependencyGrammar.Basic
import Linglib.Core.Relation.ReflTransGen
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import Mathlib.Order.SuccPred.Basic
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Order.SuccPred.Tree
import Linglib.Core.Order.SuccPred.Tree

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
  acyclicity; decidable. `IsTree.root_dominates`: the root dominates
  every position, so dominance on a tree is a partial order with the
  root as bottom.
* `Dominates.antisymm`, `Dominates.to_head`, `Dominates.comparable` —
  on trees dominance is a partial order under which the dominators of
  any position form a chain.
* `Graph.headOf`, `DominanceOrder`, `Graph.toRootedTree` — the head
  function; `Fin n` re-ordered by dominance, with `[Fact g.IsTree]` a
  `PartialOrder` + `OrderBot` + `PredOrder` + `IsPredArchimedean` +
  `SemilatticeInf` (root as `⊥`, head as `Order.pred`, lowest common
  governor as `⊓`); and the bundling as mathlib's `RootedTree`.
* `Tree n` — well-formed graphs bundled with their tree-hood
  (`t.isTree`), so the dominance-order instances hold with no side
  conditions and the graph API is a parent projection away.

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

/-- The root dominates every position: head chains ascend, without
    repetition, to the unique headless position. -/
theorem Graph.IsTree.root_dominates (hT : g.IsTree) (v : Fin n) :
    Dominates g g.root v := by
  haveI : Std.Irrefl (Relation.TransGen g.Adj) := ⟨hT.acyclic⟩
  refine (Finite.wellFounded_of_trans_of_irrefl
    (Relation.TransGen g.Adj)).induction (C := (Dominates g g.root ·)) v ?_
  intro v ih
  by_cases hv : v = g.root
  · exact hv ▸ Relation.ReflTransGen.refl
  · obtain ⟨u, hu, -⟩ := hT.existsUnique_adj v hv
    exact (ih u (Relation.TransGen.single hu)).tail hu

/-- The root's projection is the whole sentence. -/
theorem projection_root (hT : g.IsTree) :
    projection g g.root = List.finRange n :=
  List.filter_eq_self.mpr λ x _ => decide_eq_true (hT.root_dominates x)

/-! ### The head function -/

/-- The first listed head of `v`, defaulting to `v` when headless —
    under `IsTree`, the unique head of a non-root position and the root
    at the root. -/
def Graph.headOf (g : Graph n) (v : Fin n) : Fin n :=
  (g.parents v).head?.getD v

theorem Graph.IsTree.adj_headOf (hT : g.IsTree) {v : Fin n} (hv : v ≠ g.root) :
    g.Adj (g.headOf v) v := by
  obtain ⟨u, hu, -⟩ := hT.existsUnique_adj v hv
  have hmem : u ∈ g.parents v := Graph.mem_parents.mpr hu
  unfold Graph.headOf
  cases hp : g.parents v with
  | nil => exact absurd (hp ▸ hmem) List.not_mem_nil
  | cons h t =>
    simp only [List.head?_cons, Option.getD_some]
    exact Graph.mem_parents.mp (hp ▸ List.mem_cons_self)

theorem Graph.IsTree.headOf_eq (hT : g.IsTree) {u v : Fin n} (h : g.Adj u v) :
    g.headOf v = u :=
  hT.rightUnique_flip_adj
    (hT.adj_headOf (λ he => hT.not_adj_root u (he ▸ h))) h

theorem Graph.IsTree.headOf_root (hT : g.IsTree) : g.headOf g.root = g.root := by
  unfold Graph.headOf
  cases hp : g.parents g.root with
  | nil => rfl
  | cons h t =>
    exact absurd (Graph.mem_parents.mp (hp ▸ List.mem_cons_self))
      (hT.not_adj_root h)

/-! ### The dominance order -/

/-- `Fin n` carrying the dominance order of `g` instead of the
    positional order. With `[Fact g.IsTree]` this is a partial order
    with the root as bottom, the head as predecessor, and finite
    descent — the order-theoretic reading of a rooted dependency tree
    (cf. mathlib's `RootedTree`). -/
def DominanceOrder (g : Graph n) := Fin n

namespace DominanceOrder

instance : Fintype (DominanceOrder g) := inferInstanceAs (Fintype (Fin n))
instance : DecidableEq (DominanceOrder g) := inferInstanceAs (DecidableEq (Fin n))

instance {i : ℕ} [OfNat (Fin n) i] : OfNat (DominanceOrder g) i :=
  inferInstanceAs (OfNat (Fin n) i)

instance [Fact g.IsTree] : PartialOrder (DominanceOrder g) where
  le v w := Dominates g v w
  le_refl _ := .refl
  le_trans _ _ _ h h' := h.trans h'
  le_antisymm _ _ h h' := Dominates.antisymm (Fact.out : g.IsTree).acyclic h h'

instance [Fact g.IsTree] : OrderBot (DominanceOrder g) where
  bot := g.root
  bot_le := (Fact.out : g.IsTree).root_dominates

instance [Fact g.IsTree] : PredOrder (DominanceOrder g) where
  pred := g.headOf
  pred_le v := by
    by_cases hv : v = g.root
    · subst hv
      exact le_of_eq ((Fact.out : g.IsTree).headOf_root)
    · exact Relation.ReflTransGen.single ((Fact.out : g.IsTree).adj_headOf hv)
  min_of_le_pred {v} h := by
    by_cases hv : v = g.root
    · subst hv
      exact λ w _ => (Fact.out : g.IsTree).root_dominates w
    · exact absurd h (λ hdom => not_adj_dominates (Fact.out : g.IsTree).acyclic
        ((Fact.out : g.IsTree).adj_headOf hv) hdom)
  le_pred_of_lt {v w} h := by
    have hw : w ≠ g.root := λ he => h.ne (Dominates.antisymm
      (Fact.out : g.IsTree).acyclic h.le
      (he ▸ (Fact.out : g.IsTree).root_dominates v))
    exact ((Fact.out : g.IsTree).headOf_eq
        ((Fact.out : g.IsTree).adj_headOf hw)).symm ▸
      Dominates.to_head (Fact.out : g.IsTree) h.le h.ne
        ((Fact.out : g.IsTree).adj_headOf hw)

instance [Fact g.IsTree] :
    DecidableRel ((· ≤ ·) : DominanceOrder g → DominanceOrder g → Prop) :=
  λ v w => inferInstanceAs (Decidable (Dominates g v w))

instance [Fact g.IsTree] : IsPredArchimedean (DominanceOrder g) where
  exists_pred_iterate_of_le {a b} h := by
    have h' : Relation.ReflTransGen g.Adj a b := h
    clear h
    induction h' with
    | refl => exact ⟨0, rfl⟩
    | @tail c d hac hcd ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      exact (show Order.pred d = c from (Fact.out : g.IsTree).headOf_eq hcd) ▸ hk

/-- Lowest common governor as the meet: the first head-iterate of one
    argument that dominates the other. -/
instance [Fact g.IsTree] : SemilatticeInf (DominanceOrder g) :=
  IsPredArchimedean.semilatticeInf

end DominanceOrder

/-- A well-formed dependency graph, as mathlib's rooted tree: positions
    ordered by dominance, the root as `⊥`, the head as `Order.pred`,
    and the lowest common governor as `⊓`. -/
def Graph.toRootedTree (g : Graph n) [Fact g.IsTree] : RootedTree :=
  { α := DominanceOrder g }

/-! ### Bundled trees -/

/-- A dependency tree: a graph bundled with its tree-hood, so that the
    dominance-order structure holds with no side conditions. Parent
    projections give direct access to the graph API (`t.root`,
    `t.label`, `t.gapDegree`, …). -/
structure Tree (n : ℕ) extends Graph n where
  /-- Well-formedness of the underlying graph. -/
  isTree : toGraph.IsTree

namespace Tree

instance : Coe (Tree n) (Graph n) := ⟨toGraph⟩

/-- Bundle a graph with `decide`-checked tree-hood. -/
def mk' (g : Graph n) (h : g.IsTree := by decide) : Tree n := ⟨g, h⟩

/-- A bundled tree's tree-hood, available to instance search: the
    `Fact`-gated dominance-order instances fire unconditionally. -/
instance instFact (t : Tree n) : Fact t.toGraph.IsTree := ⟨t.isTree⟩

/-- A dependency tree is a mathlib rooted tree. -/
def toRootedTree (t : Tree n) : RootedTree := Graph.toRootedTree t.toGraph

end Tree

end Dominance

end DependencyGrammar
