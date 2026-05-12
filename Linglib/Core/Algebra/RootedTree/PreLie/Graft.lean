/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insert

set_option autoImplicit false

/-!
# Multi-path multi-tree grafting for `Planar α`
@cite{foissy-typed-decorated-rooted-trees-2018}
@cite{foissy-introduction-hopf-algebras-trees}

`multiGraft T pairs` grafts trees onto `T` at multiple paths
**simultaneously**, with paths interpreted in the *original* `T`
(Foissy 2021 convention). The pair list `List (Path × Planar α)` allows
multiple grafts at the same vertex (preserving pair-list order, which
matters at the root and at each common host vertex; commutativity at the
multiset boundary is upstream in `Insertion.lean`).

Sibling to `Insert.lean` (single-vertex insertion). Lives under namespace
`RootedTree.Planar.Pathed`.

## Design

`multiGraftChildren` recurses over the children list by **shifting path
indices** rather than carrying an offset:

- pairs starting `0 :: rest` are projected to `(rest, t)` and apply to the
  current head child;
- pairs starting `(k+1) :: rest` are projected to `(k :: rest, t)` and
  apply to the remaining tail.

The index-shift design simplifies the singleton bridge to `insertAt`: no
arithmetic on offsets, just direct structural cases.

## File scope

- §1: `multiGraft` / `multiGraftChildren` mutual definitions + simp lemmas.
- §2: Nil identity (`multiGraft T [] = T`).
- §3: Singleton bridge (`multiGraft T [(p, T₂)] = insertAt p T₂ T`).

Perm-invariance helpers are deferred to a follow-up session — they
require a more involved Multiset/Perm setup that doesn't belong in the
foundational substrate file.

## Status

`[UPSTREAM]` candidate. Sorry-free, no `noncomputable`.
-/

namespace RootedTree

namespace Planar

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
def rootPrependFilter (pair : Path × Planar α) : Option (Planar α) :=
  match pair.fst with
  | []     => some pair.snd
  | _ :: _ => none

@[simp] theorem rootPrependFilter_of_nil (T : Planar α) :
    rootPrependFilter ((([], T) : Path × Planar α)) = some T := rfl

@[simp] theorem rootPrependFilter_of_cons (i : ℕ) (rest : Path) (T : Planar α) :
    rootPrependFilter ((i :: rest, T) : Path × Planar α) = none := rfl

/-- Extract pair as head-child pair iff its path starts with `0`,
    stripping the leading index. -/
def headChildFilter (pair : Path × Planar α) : Option (Path × Planar α) :=
  match pair.fst with
  | 0 :: rest => some (rest, pair.snd)
  | _         => none

@[simp] theorem headChildFilter_of_nil (T : Planar α) :
    headChildFilter ((([], T) : Path × Planar α)) = none := rfl

@[simp] theorem headChildFilter_of_zero_cons (rest : Path) (T : Planar α) :
    headChildFilter ((0 :: rest, T) : Path × Planar α) = some (rest, T) := rfl

@[simp] theorem headChildFilter_of_succ_cons (k : ℕ) (rest : Path) (T : Planar α) :
    headChildFilter (((k + 1) :: rest, T) : Path × Planar α) = none := rfl

/-- Extract pair as tail-child pair iff its path starts with `k+1`,
    decrementing the leading index by one. -/
def tailChildFilter (pair : Path × Planar α) : Option (Path × Planar α) :=
  match pair.fst with
  | (k + 1) :: rest => some (k :: rest, pair.snd)
  | _               => none

@[simp] theorem tailChildFilter_of_nil (T : Planar α) :
    tailChildFilter ((([], T) : Path × Planar α)) = none := rfl

@[simp] theorem tailChildFilter_of_zero_cons (rest : Path) (T : Planar α) :
    tailChildFilter ((0 :: rest, T) : Path × Planar α) = none := rfl

@[simp] theorem tailChildFilter_of_succ_cons (k : ℕ) (rest : Path) (T : Planar α) :
    tailChildFilter (((k + 1) :: rest, T) : Path × Planar α) = some (k :: rest, T) := rfl

/-! ## §2: `multiGraft` mutual definition -/

mutual
/-- `multiGraft T pairs`: walk `T`, prepend the trees assigned to each
    path. Pairs whose path is `[]` graft at the root (prepended to the
    children list in pair-list order). Pairs whose path is `i :: rest`
    descend into the i-th child with the projected pair `(rest, _)`. -/
def multiGraft : Planar α → List (Path × Planar α) → Planar α
  | .node a cs, pairs =>
      Planar.node a (pairs.filterMap rootPrependFilter ++ multiGraftChildren cs pairs)
/-- Auxiliary: descend pair list into children. Pairs with first index
    `0` apply to the head child (with the rest of the path); pairs with
    first index `k+1` are forwarded to the tail (with the rest of the
    list and index decremented). -/
def multiGraftChildren :
    List (Planar α) → List (Path × Planar α) → List (Planar α)
  | [],      _     => []
  | c :: cs, pairs =>
      multiGraft c (pairs.filterMap headChildFilter) ::
        multiGraftChildren cs (pairs.filterMap tailChildFilter)
end

@[simp] theorem multiGraft_node (a : α) (cs : List (Planar α))
    (pairs : List (Path × Planar α)) :
    multiGraft (Planar.node a cs) pairs =
      Planar.node a (pairs.filterMap rootPrependFilter ++ multiGraftChildren cs pairs) := rfl

@[simp] theorem multiGraftChildren_nil_cs (pairs : List (Path × Planar α)) :
    multiGraftChildren ([] : List (Planar α)) pairs = [] := rfl

@[simp] theorem multiGraftChildren_cons_cs (c : Planar α) (cs : List (Planar α))
    (pairs : List (Path × Planar α)) :
    multiGraftChildren (c :: cs) pairs =
      multiGraft c (pairs.filterMap headChildFilter) ::
        multiGraftChildren cs (pairs.filterMap tailChildFilter) := rfl

/-! ## §2: Nil identity -/

mutual
/-- Empty pair list: `multiGraft` is the identity. -/
theorem multiGraft_nil : ∀ (T : Planar α), multiGraft T [] = T
  | .node a cs => by
    show Planar.node a ([] ++ multiGraftChildren cs []) = Planar.node a cs
    rw [List.nil_append, multiGraftChildren_nil_pairs cs]
/-- Empty pair list: `multiGraftChildren` is the identity on the
    children list. -/
theorem multiGraftChildren_nil_pairs : ∀ (cs : List (Planar α)),
    multiGraftChildren cs [] = cs
  | [] => rfl
  | c :: cs => by
    show multiGraft c [] :: multiGraftChildren cs [] = c :: cs
    rw [multiGraft_nil c, multiGraftChildren_nil_pairs cs]
end

/-! ## §3: Singleton bridge to `insertAt`

A single-pair `multiGraft` is exactly `insertAt`. The proof splits into:

- §3.1 `multiGraftChildren cs [([], T₂)] = cs` — the empty path
  contributes only to root prepends, not to the children.
- §3.2 `multiGraftChildren cs [(j :: rest, T₂)]` agrees with `cs.set j`
  when `j < cs.length`, else is the identity.
- §3.3 Top-level `multiGraft_singleton` combines these. -/

private theorem multiGraftChildren_singleton_nilPath :
    ∀ (cs : List (Planar α)) (T₂ : Planar α),
    multiGraftChildren cs [([], T₂)] = cs
  | [], _ => rfl
  | c :: cs, _ => by
    show multiGraft c [] :: multiGraftChildren cs [] = c :: cs
    rw [multiGraft_nil c, multiGraftChildren_nil_pairs cs]

mutual
/-- Single-pair `multiGraft` is `insertAt`. Bridges the multi-graft
    primitive to the single-vertex insertion in `Insert.lean`. -/
theorem multiGraft_singleton : ∀ (T : Planar α) (p : Path) (T₂ : Planar α),
    multiGraft T [(p, T₂)] = insertAt p T₂ T
  | .node a cs, [], T₂ => by
    show Planar.node a ([T₂] ++ multiGraftChildren cs [([], T₂)]) =
         Planar.node a (T₂ :: cs)
    rw [multiGraftChildren_singleton_nilPath cs T₂]
    rfl
  | .node a cs, j :: rest, T₂ => by
    show Planar.node a ([] ++ multiGraftChildren cs [(j :: rest, T₂)]) =
         insertAt (j :: rest) T₂ (Planar.node a cs)
    rw [List.nil_append, multiGraftChildren_singleton_cons cs j rest T₂]
    by_cases hj : j < cs.length
    · rw [insertAt_cons_of_lt _ _ _ _ _ hj]
      simp [hj]
    · rw [insertAt_cons_of_not_lt _ _ _ _ _ hj]
      simp [hj]
private theorem multiGraftChildren_singleton_cons :
    ∀ (cs : List (Planar α)) (j : ℕ) (rest : Path) (T₂ : Planar α),
    multiGraftChildren cs [(j :: rest, T₂)] =
      if hj : j < cs.length then
        cs.set j (insertAt rest T₂ (cs[j]'hj))
      else cs
  | [], j, rest, T₂ => by
    show ([] : List (Planar α)) = _
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

end Planar

end RootedTree
