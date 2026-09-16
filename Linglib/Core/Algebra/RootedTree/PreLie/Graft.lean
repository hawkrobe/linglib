/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insert

/-!
# Multi-path grafting on `RoseTree α`

`multiGraft T pairs` grafts trees onto `T` at several paths **simultaneously**, every path read
in the original `T` (Foissy's convention). Several pairs may share a path; their trees are
prepended in pair-list order, so `multiGraft` is order-sensitive, and commutativity is recovered
at the multiset level in `Insertion.lean`.

## Main definitions and results

* `multiGraft`, `multiGraftChildren`: the mutual recursion. `multiGraftChildren` descends by
  shifting path indices: pairs starting `0 :: rest` go to the head child as `(rest, t)`, pairs
  starting `(k + 1) :: rest` go to the tail as `(k :: rest, t)`.
* `rootPrependFilter`, `headChildFilter`, `tailChildFilter`: the three pair projections, with
  their `List.filter` characterizations.
* `multiGraft_nil`: no pairs, no change.
* `multiGraft_singleton`: one pair is `insertAt`.

## References

* [foissy-typed-decorated-rooted-trees-2018]
* [foissy-introduction-hopf-algebras-trees]
-/

namespace RoseTree

namespace Pathed

variable {α : Type*}

/-! ## §1: Filter helpers (top-level for matcher stability)

The `multiGraft` recursion uses three pair-filtering functions: extracting
root-prepends (empty path), extracting head-child pairs (first index `0`),
and shifting tail-child pairs (first index `k+1`). Each is defined as a
top-level function so that all `filterMap` callers reference the *same*
elaborated matcher — `rw` with filter equalities then works cleanly across
files. Without this, Lean's inline-`match` elaboration generates fresh
`match_N` aux constants per scope, blocking unification.

Each helper carries unfolding `@[simp]` lemmas on every pattern so that
`simp` can reduce them where `rfl` would otherwise fail. -/

/-- Extract pair as root prepend iff its path is empty. -/
def rootPrependFilter (pair : Path × RoseTree α) : Option (RoseTree α) :=
  match pair.fst with
  | []     => some pair.snd
  | _ :: _ => none

@[simp] theorem rootPrependFilter_of_nil (T : RoseTree α) :
    rootPrependFilter ((([], T) : Path × RoseTree α)) = some T := rfl

@[simp] theorem rootPrependFilter_of_cons (i : ℕ) (rest : Path) (T : RoseTree α) :
    rootPrependFilter ((i :: rest, T) : Path × RoseTree α) = none := rfl

/-- Extract pair as head-child pair iff its path starts with `0`,
    stripping the leading index. -/
def headChildFilter (pair : Path × RoseTree α) : Option (Path × RoseTree α) :=
  match pair.fst with
  | 0 :: rest => some (rest, pair.snd)
  | _         => none

@[simp] theorem headChildFilter_of_nil (T : RoseTree α) :
    headChildFilter ((([], T) : Path × RoseTree α)) = none := rfl

@[simp] theorem headChildFilter_of_zero_cons (rest : Path) (T : RoseTree α) :
    headChildFilter ((0 :: rest, T) : Path × RoseTree α) = some (rest, T) := rfl

@[simp] theorem headChildFilter_of_succ_cons (k : ℕ) (rest : Path) (T : RoseTree α) :
    headChildFilter (((k + 1) :: rest, T) : Path × RoseTree α) = none := rfl

/-- Extract pair as tail-child pair iff its path starts with `k+1`,
    decrementing the leading index by one. -/
def tailChildFilter (pair : Path × RoseTree α) : Option (Path × RoseTree α) :=
  match pair.fst with
  | (k + 1) :: rest => some (k :: rest, pair.snd)
  | _               => none

@[simp] theorem tailChildFilter_of_nil (T : RoseTree α) :
    tailChildFilter ((([], T) : Path × RoseTree α)) = none := rfl

@[simp] theorem tailChildFilter_of_zero_cons (rest : Path) (T : RoseTree α) :
    tailChildFilter ((0 :: rest, T) : Path × RoseTree α) = none := rfl

@[simp] theorem tailChildFilter_of_succ_cons (k : ℕ) (rest : Path) (T : RoseTree α) :
    tailChildFilter (((k + 1) :: rest, T) : Path × RoseTree α) = some (k :: rest, T) := rfl

/-! ## §2: `multiGraft` mutual definition -/

mutual
/-- `multiGraft T pairs`: walk `T`, prepend the trees assigned to each
    path. Pairs whose path is `[]` graft at the root (prepended to the
    children list in pair-list order). Pairs whose path is `i :: rest`
    descend into the i-th child with the projected pair `(rest, _)`. -/
def multiGraft : RoseTree α → List (Path × RoseTree α) → RoseTree α
  | .node a cs, pairs =>
      RoseTree.node a (pairs.filterMap rootPrependFilter ++ multiGraftChildren cs pairs)
/-- Auxiliary: descend pair list into children. Pairs with first index
    `0` apply to the head child (with the rest of the path); pairs with
    first index `k+1` are forwarded to the tail (with the rest of the
    list and index decremented). -/
def multiGraftChildren :
    List (RoseTree α) → List (Path × RoseTree α) → List (RoseTree α)
  | [],      _     => []
  | c :: cs, pairs =>
      multiGraft c (pairs.filterMap headChildFilter) ::
        multiGraftChildren cs (pairs.filterMap tailChildFilter)
end

@[simp] theorem multiGraft_node (a : α) (cs : List (RoseTree α))
    (pairs : List (Path × RoseTree α)) :
    multiGraft (RoseTree.node a cs) pairs =
      RoseTree.node a (pairs.filterMap rootPrependFilter ++ multiGraftChildren cs pairs) := rfl

@[simp] theorem multiGraftChildren_nil_cs (pairs : List (Path × RoseTree α)) :
    multiGraftChildren ([] : List (RoseTree α)) pairs = [] := rfl

@[simp] theorem multiGraftChildren_cons_cs (c : RoseTree α) (cs : List (RoseTree α))
    (pairs : List (Path × RoseTree α)) :
    multiGraftChildren (c :: cs) pairs =
      multiGraft c (pairs.filterMap headChildFilter) ::
        multiGraftChildren cs (pairs.filterMap tailChildFilter) := rfl

/-! ### Filter characterizations

Each pair filter is a `List.filter` on the path followed by a projection, so pair lists can be
bucketed by a predicate on paths (`bind_listChoices_filter` in `Insertion.lean`). -/

theorem filterMap_rootPrependFilter (pairs : List (Path × RoseTree α)) :
    pairs.filterMap rootPrependFilter =
      (pairs.filter fun p => decide (p.1 = [])).map Prod.snd := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    obtain ⟨q, T⟩ := p
    cases q <;> simp [ih]

theorem filterMap_headChildFilter (pairs : List (Path × RoseTree α)) :
    pairs.filterMap headChildFilter =
      (pairs.filter fun p => decide (p.1.head? = some 0)).map (Prod.map List.tail id) := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    obtain ⟨q, T⟩ := p
    rcases q with _ | ⟨_ | k, rest⟩ <;> simp [ih]

theorem filterMap_tailChildFilter (pairs : List (Path × RoseTree α))
    (h : ∀ p ∈ pairs, p.1 ≠ []) :
    pairs.filterMap tailChildFilter =
      (pairs.filter fun p => decide (¬ p.1.head? = some 0)).map
        (Prod.map (List.modifyHead (· - 1)) id) := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    obtain ⟨q, T⟩ := p
    have ih := ih fun p hp => h p (List.mem_cons_of_mem _ hp)
    rcases q with _ | ⟨_ | k, rest⟩
    · exact absurd rfl (h ([], T) List.mem_cons_self)
    · simp [ih]
    · simp [ih]

/-- `multiGraftChildren` depends on its pair list only through the two child filters. -/
theorem multiGraftChildren_congr {cs : List (RoseTree α)}
    {pairs₁ pairs₂ : List (Path × RoseTree α)}
    (h₁ : pairs₁.filterMap headChildFilter = pairs₂.filterMap headChildFilter)
    (h₂ : pairs₁.filterMap tailChildFilter = pairs₂.filterMap tailChildFilter) :
    multiGraftChildren cs pairs₁ = multiGraftChildren cs pairs₂ := by
  cases cs with
  | nil => rfl
  | cons c cs => rw [multiGraftChildren_cons_cs, multiGraftChildren_cons_cs, h₁, h₂]

/-- Root pairs never reach the children. -/
theorem multiGraftChildren_filter_ne_nil (cs : List (RoseTree α))
    (pairs : List (Path × RoseTree α)) :
    multiGraftChildren cs (pairs.filter fun p => decide (¬ p.1 = [])) =
      multiGraftChildren cs pairs := by
  refine multiGraftChildren_congr ?_ ?_ <;>
  · rw [List.filterMap_filter]
    refine List.filterMap_congr fun p _ => ?_
    obtain ⟨q, T⟩ := p
    cases q <;> simp

/-- `multiGraftChildren cs pairs` has the same length as `cs`. -/
theorem multiGraftChildren_length :
    ∀ (cs : List (RoseTree α)) (pairs : List (Path × RoseTree α)),
    (multiGraftChildren cs pairs).length = cs.length
  | [], _ => rfl
  | c :: cs, pairs => by
    rw [multiGraftChildren_cons_cs, List.length_cons, List.length_cons,
      multiGraftChildren_length cs (pairs.filterMap tailChildFilter)]

/-! ## §3: Nil identity -/

mutual
/-- Empty pair list: `multiGraft` is the identity. -/
theorem multiGraft_nil : ∀ (T : RoseTree α), multiGraft T [] = T
  | .node a cs => by
    show RoseTree.node a ([] ++ multiGraftChildren cs []) = RoseTree.node a cs
    rw [List.nil_append, multiGraftChildren_nil_pairs cs]
/-- Empty pair list: `multiGraftChildren` is the identity on the
    children list. -/
theorem multiGraftChildren_nil_pairs : ∀ (cs : List (RoseTree α)),
    multiGraftChildren cs [] = cs
  | [] => rfl
  | c :: cs => by
    show multiGraft c [] :: multiGraftChildren cs [] = c :: cs
    rw [multiGraft_nil c, multiGraftChildren_nil_pairs cs]
end

/-! ## §4: Singleton bridge to `insertAt`

A single-pair `multiGraft` is exactly `insertAt`. The proof splits into:

- §4.1 `multiGraftChildren cs [([], T₂)] = cs` — the empty path
  contributes only to root prepends, not to the children.
- §4.2 `multiGraftChildren cs [(j :: rest, T₂)]` agrees with `cs.set j`
  when `j < cs.length`, else is the identity.
- §4.3 Top-level `multiGraft_singleton` combines these. -/

private theorem multiGraftChildren_singleton_nilPath :
    ∀ (cs : List (RoseTree α)) (T₂ : RoseTree α),
    multiGraftChildren cs [([], T₂)] = cs
  | [], _ => rfl
  | c :: cs, _ => by
    show multiGraft c [] :: multiGraftChildren cs [] = c :: cs
    rw [multiGraft_nil c, multiGraftChildren_nil_pairs cs]

mutual
/-- Single-pair `multiGraft` is `insertAt`. Bridges the multi-graft
    primitive to the single-vertex insertion in `Insert.lean`. -/
theorem multiGraft_singleton : ∀ (T : RoseTree α) (p : Path) (T₂ : RoseTree α),
    multiGraft T [(p, T₂)] = insertAt p T₂ T
  | .node a cs, [], T₂ => by
    show RoseTree.node a ([T₂] ++ multiGraftChildren cs [([], T₂)]) =
         RoseTree.node a (T₂ :: cs)
    rw [multiGraftChildren_singleton_nilPath cs T₂]
    rfl
  | .node a cs, j :: rest, T₂ => by
    show RoseTree.node a ([] ++ multiGraftChildren cs [(j :: rest, T₂)]) =
         insertAt (j :: rest) T₂ (RoseTree.node a cs)
    rw [List.nil_append, multiGraftChildren_singleton_cons cs j rest T₂]
    by_cases hj : j < cs.length
    · rw [insertAt_cons_of_lt _ _ _ _ _ hj]
      simp [hj]
    · rw [insertAt_cons_of_not_lt _ _ _ _ _ hj]
      simp [hj]
private theorem multiGraftChildren_singleton_cons :
    ∀ (cs : List (RoseTree α)) (j : ℕ) (rest : Path) (T₂ : RoseTree α),
    multiGraftChildren cs [(j :: rest, T₂)] =
      if hj : j < cs.length then
        cs.set j (insertAt rest T₂ (cs[j]'hj))
      else cs
  | [], j, rest, T₂ => by
    show ([] : List (RoseTree α)) = _
    simp
  | c :: cs, 0, rest, T₂ => by
    show multiGraft c [(rest, T₂)] :: multiGraftChildren cs [] = _
    rw [multiGraft_singleton c rest T₂, multiGraftChildren_nil_pairs cs]
    simp [List.set_cons_zero]
  | c :: cs, k + 1, rest, T₂ => by
    show multiGraft c [] :: multiGraftChildren cs [(k :: rest, T₂)] = _
    rw [multiGraft_nil c, multiGraftChildren_singleton_cons cs k rest T₂]
    by_cases hk : k < cs.length
    · have hk' : k + 1 < (c :: cs).length := by simp [List.length_cons]; omega
      simp only [hk, hk', ↓reduceDIte]
      rw [List.set_cons_succ, List.getElem_cons_succ]
    · have hk' : ¬ k + 1 < (c :: cs).length := by simp [List.length_cons]; omega
      simp only [hk, hk', ↓reduceDIte]
end

end Pathed

end RoseTree
