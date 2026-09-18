/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.RoseTree.Basic

/-!
# Path addressing for `RoseTree α`

A vertex of a rose tree is addressed by the list of child indices from the root, `[]` being the
root. `vertices T` enumerates the paths of `T` in root-first order through `verticesAux i cs`,
which lists the paths into a children list starting at child index `i`.

## Main results

* `verticesAux_append`, `verticesAux_eq_map_modifyHead`: how the enumeration of a children list
  splits and shifts.
* `length_vertices_eq_numNodes`: one path per vertex.

## References

* [foissy-typed-decorated-rooted-trees-2018]
* [chapoton-livernet-2001]
-/

namespace RoseTree

namespace Pathed

variable {α : Type*}

/-- A path from the root: the list of child indices. `[]` addresses the root. -/
abbrev Path : Type := List ℕ

/-! ## Vertex enumeration

`vertices T : List Path` lists the valid paths into `T` in DFS root-first
order: the empty path, then for each child `cs[i]` the i-prepended
recursion. Mutual with an aux running over the children list paired with
an offset index.

-/

mutual
/-- All valid paths into `T` in root-first order. -/
def vertices : RoseTree α → List Path
  | .node _ cs => [] :: verticesAux 0 cs
/-- Auxiliary: paths into a children list, with a starting index. The
    paths returned are already prefixed with the corresponding child
    index. -/
def verticesAux : ℕ → List (RoseTree α) → List Path
  | _, []      => []
  | i, c :: cs =>
      (vertices c).map (i :: ·) ++ verticesAux (i + 1) cs
end

@[simp] theorem vertices_node (a : α) (cs : List (RoseTree α)) :
    vertices (RoseTree.node a cs) = [] :: verticesAux 0 cs := rfl

@[simp] theorem verticesAux_nil (i : ℕ) :
    verticesAux i ([] : List (RoseTree α)) = [] := rfl

@[simp] theorem verticesAux_cons (i : ℕ) (c : RoseTree α) (cs : List (RoseTree α)) :
    verticesAux i (c :: cs) =
      (vertices c).map (i :: ·) ++ verticesAux (i + 1) cs := rfl

/-- `verticesAux` distributes over list `++`. The right summand's start
    index shifts by the left list's length. -/
theorem verticesAux_append (i : ℕ) (xs ys : List (RoseTree α)) :
    verticesAux i (xs ++ ys) =
      verticesAux i xs ++ verticesAux (i + xs.length) ys := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, verticesAux_cons, ih, List.append_assoc,
               List.length_cons]
    have : i + 1 + xs.length = i + (xs.length + 1) := by omega
    rw [this]

/-- Starting `verticesAux` at index `i` shifts every head index by `i`. -/
theorem verticesAux_eq_map_modifyHead (i : ℕ) (cs : List (RoseTree α)) :
    verticesAux i cs = (verticesAux 0 cs).map (List.modifyHead (· + i)) := by
  induction cs generalizing i with
  | nil => rfl
  | cons c cs ih =>
    rw [verticesAux_cons, verticesAux_cons, ih (i + 1), ih 1, List.map_append, List.map_map,
      List.map_map]
    congr 1
    · exact List.map_congr_left fun p _ => by simp
    · exact List.map_congr_left fun p _ => by
        rw [Function.comp_apply, List.modifyHead_modifyHead]
        exact congrArg (List.modifyHead · p) (funext fun x => by
          simp only [Function.comp_apply]
          omega)

/-- Every path enumerated by `verticesAux i cs` starts with an index of at least `i`. -/
theorem exists_cons_of_mem_verticesAux {i : ℕ} {cs : List (RoseTree α)} {p : Path}
    (hp : p ∈ verticesAux i cs) : ∃ k q, i ≤ k ∧ p = k :: q := by
  induction cs generalizing i with
  | nil => simp at hp
  | cons c cs ih =>
    rw [verticesAux_cons, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, -, rfl⟩ | hp
    · exact ⟨i, q, Nat.le_refl _, rfl⟩
    · obtain ⟨k, q, hk, rfl⟩ := ih hp
      exact ⟨k, q, by omega, rfl⟩

/-! ### Length theorem

The total number of enumerated paths equals the tree's node count. -/

mutual
theorem length_vertices_eq_numNodes : ∀ (T : RoseTree α),
    (vertices T).length = T.numNodes
  | .node _ cs => by
    rw [vertices_node, List.length_cons, length_verticesAux 0 cs, numNodes_node]
theorem length_verticesAux : ∀ (i : ℕ) (cs : List (RoseTree α)),
    (verticesAux i cs).length = (cs.map numNodes).sum
  | _, []      => by simp
  | i, c :: cs => by
    rw [verticesAux_cons, List.length_append, List.length_map,
        length_vertices_eq_numNodes c, length_verticesAux (i + 1) cs]
    simp
end

end Pathed

end RoseTree
