/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Data.Tree.Basic

set_option autoImplicit false

/-!
# Path-based vertex addressing for `Tree α`
[foissy-typed-decorated-rooted-trees-2018]
[chapoton-livernet-2001]

Path-based replacement for the indexed-inductive `Vertex T` / `VertexList cs`
machinery in `Vertex.lean`. A vertex is addressed by a `Path = List ℕ` of
child indices from the root. The non-dependent representation lets
`List.map_append`, `List.Perm`, and related mathlib API fire directly on
`vertices` outputs without the `have h := List.map_append; rw [h]`
workarounds that the dependent-typed version forced.

Lives under namespace `Tree.Pathed`; the `Pathed` sub-namespace keeps the
path-addressing API from colliding with the core `Tree` surface and will be
hoisted up once the old dependent `Vertex` machinery is retired.

## File scope

- §1: `Path`, `IsValidPath`, `Decidable` instance.
- §2: `vertices` enumeration + length theorem + validity sanity check.

Path-based code uses `Path` and `IsValidPath` directly. A subtype
wrapper `{ p : Path // IsValidPath p T }` can be inlined at use sites
that need it; no global `Vertex` def is needed.

## Status

`[UPSTREAM]` candidate. Sorry-free, no `noncomputable`.
-/

namespace RootedTree.Tree

namespace Pathed

variable {α : Type*}

/-! ## §1: `Path` and validity -/

/-- A path from the root: list of child indices. `[]` addresses the root. -/
abbrev Path : Type := List ℕ

/-- `IsValidPath p T` means `p` addresses an existing vertex in `T`.
    Recurses on the path: empty path is always valid; `i :: rest` requires
    `i` to be in bounds and `rest` to be valid in the i-th child. -/
def IsValidPath : Path → Tree α → Prop
  | [],        _           => True
  | i :: rest, .node _ cs  => ∃ h : i < cs.length, IsValidPath rest cs[i]

@[simp] theorem isValidPath_nil (T : Tree α) : IsValidPath ([] : Path) T := trivial

@[simp] theorem isValidPath_cons (i : ℕ) (rest : Path) (a : α) (cs : List (Tree α)) :
    IsValidPath (i :: rest) (Tree.node a cs) ↔
      ∃ h : i < cs.length, IsValidPath rest cs[i] := Iff.rfl

/-- Decidability of `IsValidPath`, by recursion on the path. -/
def decValidPath : ∀ (p : Path) (T : Tree α), Decidable (IsValidPath p T)
  | [],        _          => .isTrue trivial
  | i :: rest, .node _ cs =>
    if h : i < cs.length then
      match decValidPath rest cs[i] with
      | .isTrue ht  => .isTrue ⟨h, ht⟩
      | .isFalse hf => .isFalse (by rintro ⟨_, ht⟩; exact hf ht)
    else
      .isFalse (by rintro ⟨h', _⟩; exact h h')

instance (p : Path) (T : Tree α) : Decidable (IsValidPath p T) :=
  decValidPath p T

/-! ## §2: Vertex enumeration

`vertices T : List Path` lists the valid paths into `T` in DFS root-first
order: the empty path, then for each child `cs[i]` the i-prepended
recursion. Mutual with an aux running over the children list paired with
an offset index.

The mutual style is the same shape as `vertices` / `verticesList` in the
old `Vertex.lean` — exchange of the dependent inductive for a path list. -/

mutual
/-- All valid paths into `T` in root-first order. -/
def vertices : Tree α → List Path
  | .node _ cs => [] :: verticesAux 0 cs
/-- Auxiliary: paths into a children list, with a starting index. The
    paths returned are already prefixed with the corresponding child
    index. -/
def verticesAux : ℕ → List (Tree α) → List Path
  | _, []      => []
  | i, c :: cs =>
      (vertices c).map (i :: ·) ++ verticesAux (i + 1) cs
end

@[simp] theorem vertices_node (a : α) (cs : List (Tree α)) :
    vertices (Tree.node a cs) = [] :: verticesAux 0 cs := rfl

@[simp] theorem verticesAux_nil (i : ℕ) :
    verticesAux i ([] : List (Tree α)) = [] := rfl

@[simp] theorem verticesAux_cons (i : ℕ) (c : Tree α) (cs : List (Tree α)) :
    verticesAux i (c :: cs) =
      (vertices c).map (i :: ·) ++ verticesAux (i + 1) cs := rfl

/-- `verticesAux` distributes over list `++`. The right summand's start
    index shifts by the left list's length. -/
theorem verticesAux_append (i : ℕ) (xs ys : List (Tree α)) :
    verticesAux i (xs ++ ys) =
      verticesAux i xs ++ verticesAux (i + xs.length) ys := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, verticesAux_cons, ih, List.append_assoc,
               List.length_cons]
    have : i + 1 + xs.length = i + (xs.length + 1) := by omega
    rw [this]

/-! ### Length theorem

The total number of enumerated paths equals the tree's node count
(`numNodes`). Mirrors the dependent-typed substrate's `length_vertices`
result, now stated directly against `numNodes` — no `weightList` aux-twin
is needed, the child sum is `(cs.map numNodes).sum`. -/

mutual
theorem length_vertices_eq_numNodes : ∀ (T : Tree α),
    (vertices T).length = T.numNodes
  | .node _ cs => by
    rw [vertices_node, List.length_cons, length_verticesAux 0 cs, numNodes_node]
    omega
theorem length_verticesAux : ∀ (i : ℕ) (cs : List (Tree α)),
    (verticesAux i cs).length = (cs.map numNodes).sum
  | _, []      => by simp
  | i, c :: cs => by
    rw [verticesAux_cons, List.length_append, List.length_map,
        length_vertices_eq_numNodes c, length_verticesAux (i + 1) cs]
    simp
end

/-! ### Validity sanity check

Every path enumerated by `vertices T` is in fact valid in `T`. Proved via
a mutual recursion through an aux that decomposes paths in
`verticesAux i₀ cs` as `(i₀ + k) :: rest` with `rest ∈ vertices cs[k]`. -/

mutual
theorem forall_isValidPath : ∀ (T : Tree α) {p : Path},
    p ∈ vertices T → IsValidPath p T
  | .node _ cs, p, hp => by
    rw [vertices_node, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact trivial
    · obtain ⟨k, rest, heq, hk, hrest⟩ := forall_isValidPath_aux cs 0 hp
      have : p = k :: rest := by simpa [Nat.zero_add] using heq
      subst this
      exact ⟨hk, hrest⟩
theorem forall_isValidPath_aux : ∀ (cs : List (Tree α)) (i₀ : ℕ) {p : Path},
    p ∈ verticesAux i₀ cs →
    ∃ (k : ℕ) (rest : Path),
      p = (i₀ + k) :: rest ∧ ∃ h : k < cs.length, IsValidPath rest cs[k]
  | [],      _,  _, hp => by cases hp
  | c :: cs, i₀, p, hp => by
    rw [verticesAux_cons, List.mem_append] at hp
    rcases hp with hp | hp
    · rw [List.mem_map] at hp
      obtain ⟨q, hq_mem, rfl⟩ := hp
      refine ⟨0, q, ?_, by simp, ?_⟩
      · simp
      · simpa using forall_isValidPath c hq_mem
    · obtain ⟨k, rest, heq, hk, hrest⟩ := forall_isValidPath_aux cs (i₀ + 1) hp
      have hk' : k + 1 < (c :: cs).length := by simp [List.length_cons]; omega
      refine ⟨k + 1, rest, ?_, hk', ?_⟩
      · subst heq; simp; omega
      · show IsValidPath rest ((c :: cs)[k + 1]'hk')
        rw [List.getElem_cons_succ]
        exact hrest
end

end Pathed

end RootedTree.Tree
