/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Path
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Filter
import Mathlib.Tactic.Abel

set_option autoImplicit false

/-!
# Path-based single-vertex insertion and vertex decomposition for `Tree α`
[foissy-typed-decorated-rooted-trees-2018]
[chapoton-livernet-2001]

`insertAt p T₂ T` grafts `T₂` as a new first child at the vertex
addressed by path `p` in `T`. Out-of-bounds path: no-op.

The headline theorem `vertices_insertAt_decomp` partitions the path set
of `Pathed.insertAt e t₂ t₁` into three classes:

* **preserved**: paths of `t₁ \ {e}` transported through the insertion
  (a child-index shift when `e` is a proper prefix).
* **sourceSelf**: the source vertex `e` itself (still present in the
  post-graft tree, just with a new first child).
* **lifted**: paths of `t₂` embedded under `e` (each `q ∈ vertices t₂`
  ends up at path `e ++ 0 :: q` since `t₂` is grafted at child index 0).

This decomposition is the substrate behind the pre-Lie identity in
`Algebra.lean`: each `(insertAt v t₂) ◁ t₃` splits into three sums, each
of which has a clean cancellation against a symmetric counterpart.

The path-form is **flat, non-dependent**: `preserveOf e f`, `lift e q`,
etc. are pure path manipulations that don't carry `T` or `T₂` in their
types. `IsValidPath` obligations are discharged per-theorem with explicit
hypotheses.

## File scope

- §1: `insertAt` — single-vertex graft primitive.
- §2: `lift` — embedding `t₂`-paths into the post-graft tree.
- §3: `sourceSelf` — the source vertex's path post-graft.
- §4: `preserve?`, `preserveOf` — transporting a non-source vertex.
- §5: Commutativity `insertAt_commute_diff` and lifted-equals-nested
  `insertAt_lift_eq_nested`.
- §6: Multiset decomposition `vertices_insertAt_decomp`.
- §7: Preserved-class swap `bind_filterMap_preserve?_swap`.

Sibling files:
- `Path.lean` — Path / IsValidPath / vertices / verticesAux.
- `Graft.lean` — multi-pair `multiGraft` + multi-pair vertex decomposition.

## Status

`[UPSTREAM]` candidate. Sorry-free, no `noncomputable`.
-/

namespace RootedTree.Tree

namespace Pathed

variable {α : Type*}

/-! ## §1: `insertAt` -/

/-- Insert `T₂` as a new first child at the vertex addressed by path `p`
    in `T`. Returns `T` unchanged if `p` is out of bounds (no-op
    fallback for invalid paths). -/
def insertAt : Path → Tree α → Tree α → Tree α
  | [],        T₂, .node a cs => .node a (T₂ :: cs)
  | i :: rest, T₂, .node a cs =>
      if h : i < cs.length then
        .node a (cs.set i (insertAt rest T₂ (cs[i]'h)))
      else
        .node a cs

@[simp] theorem insertAt_nil (T₂ : Tree α) (a : α) (cs : List (Tree α)) :
    insertAt [] T₂ (Tree.node a cs) = Tree.node a (T₂ :: cs) := rfl

@[simp] theorem insertAt_cons_of_lt (i : ℕ) (rest : Path) (T₂ : Tree α)
    (a : α) (cs : List (Tree α)) (h : i < cs.length) :
    insertAt (i :: rest) T₂ (Tree.node a cs) =
      Tree.node a (cs.set i (insertAt rest T₂ (cs[i]'h))) := by
  simp [insertAt, h]

theorem insertAt_cons_of_not_lt (i : ℕ) (rest : Path) (T₂ : Tree α)
    (a : α) (cs : List (Tree α)) (h : ¬ i < cs.length) :
    insertAt (i :: rest) T₂ (Tree.node a cs) = Tree.node a cs := by
  simp [insertAt, h]

/-! ## §2: `lift` — embedding `T₂` into the post-graft tree

When `T₂` is grafted at path `e` in `T`, T₂'s root is at path `e ++ [0]`,
and a vertex of T₂ at internal path `q` ends up at `e ++ 0 :: q`. -/

/-- The position in `Pathed.insertAt e t₂ T` of the vertex `q ∈ T₂`. -/
def lift (e : Path) (q : Path) : Path := e ++ 0 :: q

@[simp] theorem lift_def (e q : Path) : lift e q = e ++ 0 :: q := rfl

@[simp] theorem lift_nil_left (q : Path) : lift [] q = 0 :: q := rfl

/-! ## §3: `sourceSelf` — the source vertex's path post-graft

The vertex at path `e` in `T` is still at path `e` in `Pathed.insertAt e t₂ T`
— it didn't move, it just gained a new first child. The path-form
analogue of `Vertex.sourceSelf` is the identity on `e`. -/

/-- The position of the source vertex `e` in the post-graft tree. Just `e`. -/
def sourceSelf (e : Path) : Path := e

@[simp] theorem sourceSelf_def (e : Path) : sourceSelf e = e := rfl

/-! ## §4: `preserve?`, `preserveOf` — transporting a non-source vertex

Given paths `e f` in `T` with `f ≠ e`, what's `f`'s path in
`Pathed.insertAt e t₂ T`? Four cases on the prefix relation of `e` and
`f`:

* `e = f`: diagonal, `none`.
* `f` is a strict ancestor of `e`: `f` unchanged.
* `e` is a strict ancestor of `f`: `f = e ++ (j :: rest)` shifts to
  `e ++ ((j+1) :: rest)` (new child `t₂` at index 0 pushes original
  children up).
* `e f` branch at some common ancestor: `f` unchanged.
-/

/-- Total Option-valued preservation: `none` on the diagonal, `some` of
    the shifted path elsewhere. Pure path arithmetic (no `T`, no `T₂`). -/
def preserve? : Path → Path → Option Path
  | [],          []           => none
  | [],          j :: rest    => some ((j + 1) :: rest)
  | _ :: _,      []           => some []
  | i :: rest_e, j :: rest_f  =>
      if i = j then
        (preserve? rest_e rest_f).map (i :: ·)
      else
        some (j :: rest_f)

@[simp] theorem preserve?_nil_nil : preserve? [] [] = none := rfl

@[simp] theorem preserve?_nil_cons (j : ℕ) (rest : Path) :
    preserve? [] (j :: rest) = some ((j + 1) :: rest) := rfl

@[simp] theorem preserve?_cons_nil (i : ℕ) (rest : Path) :
    preserve? (i :: rest) [] = some [] := rfl

theorem preserve?_cons_cons (i j : ℕ) (rest_e rest_f : Path) :
    preserve? (i :: rest_e) (j :: rest_f) =
      (if i = j then
         (preserve? rest_e rest_f).map (i :: ·)
       else
         some (j :: rest_f)) := by
  rfl

/-- Diagonal: `preserve? e e = none`. -/
@[simp] theorem preserve?_self : ∀ (e : Path), preserve? e e = none
  | []      => rfl
  | i :: rest => by
    rw [preserve?_cons_cons, if_pos rfl, preserve?_self rest]
    rfl

/-- Off-diagonal: when `f ≠ e`, `preserve? e f` is `some _`. The path is
    given by `preserveOf` below. -/
def preserveOf : Path → Path → Path
  | [],          []           => []  -- nonsense, won't be reached under f ≠ e
  | [],          j :: rest    => (j + 1) :: rest
  | _ :: _,      []           => []
  | i :: rest_e, j :: rest_f  =>
      if i = j then
        i :: preserveOf rest_e rest_f
      else
        j :: rest_f

@[simp] theorem preserveOf_nil_cons (j : ℕ) (rest : Path) :
    preserveOf [] (j :: rest) = (j + 1) :: rest := rfl

@[simp] theorem preserveOf_cons_nil (i : ℕ) (rest : Path) :
    preserveOf (i :: rest) [] = [] := rfl

theorem preserveOf_cons_cons (i j : ℕ) (rest_e rest_f : Path) :
    preserveOf (i :: rest_e) (j :: rest_f) =
      (if i = j then i :: preserveOf rest_e rest_f else j :: rest_f) := by
  rfl

/-- Off-diagonal: `preserve? e f = some (preserveOf e f)` when `f ≠ e`. -/
theorem preserve?_of_ne : ∀ (e f : Path) (_h : f ≠ e),
    preserve? e f = some (preserveOf e f)
  | [],            [],            h => absurd rfl h.symm
  | [],            _ :: _,        _ => rfl
  | _ :: _,        [],            _ => rfl
  | i :: rest_e,   j :: rest_f,   h => by
    rw [preserve?_cons_cons, preserveOf_cons_cons]
    by_cases hij : i = j
    · -- i = j, recurse on rest
      have hrest : rest_f ≠ rest_e := by
        intro heq; apply h; rw [hij, heq]
      rw [if_pos hij, if_pos hij, preserve?_of_ne rest_e rest_f hrest]
      rfl
    · rw [if_neg hij, if_neg hij]

/-! ## §5: Commutativity + lifted-equals-nested

Two algebraic identities about `Pathed.insertAt` that drive the pre-Lie
identity proof in `Algebra.lean`. -/

/-- **Commutativity at distinct paths**: inserting `t₂` at `e` then `t₃`
    at the `f`-image equals inserting `t₃` at `f` then `t₂` at the
    `e`-image. The (e, f) ↔ (f, e) re-keying lives in `preserveOf`.

    Proof structure: case-analyze the prefix relation of `e` and `f`,
    recurse on the shared prefix. Four primary cases:

    * Both empty: contradicts `h`.
    * `e = []`, `f = j :: rest_f`: insert at root, child shift.
    * `e = i :: rest_e`, `f = []`: symmetric.
    * Both non-empty: branch on `i = j` (recurse) vs `i ≠ j` (different
      child slots, commute via `List.set_comm`).

    Within each non-empty case, sub-case on `index < cs.length` (in
    bounds — meaningful insertion) vs out-of-bounds (both no-op). -/
theorem insertAt_commute_diff : ∀ (e f : Path) (_h : f ≠ e) (t₁ t₂ t₃ : Tree α),
    Pathed.insertAt (preserveOf e f) t₃ (Pathed.insertAt e t₂ t₁) =
      Pathed.insertAt (preserveOf f e) t₂ (Pathed.insertAt f t₃ t₁)
  | [], [], h, _, _, _ => absurd rfl h.symm
  | [], j :: rest_f, _, .node a cs, t₂, t₃ => by
    show Pathed.insertAt ((j + 1) :: rest_f) t₃ (Tree.node a (t₂ :: cs)) =
      Pathed.insertAt [] t₂ (Pathed.insertAt (j :: rest_f) t₃ (Tree.node a cs))
    by_cases hj : j < cs.length
    · have hj' : j + 1 < (t₂ :: cs).length := by simp; omega
      rw [Pathed.insertAt_cons_of_lt _ _ _ _ _ hj',
          Pathed.insertAt_cons_of_lt _ _ _ _ _ hj,
          Pathed.insertAt_nil]
      simp [List.getElem_cons_succ, List.set_cons_succ]
    · have hj' : ¬ (j + 1 < (t₂ :: cs).length) := by simp; omega
      rw [Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hj',
          Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hj,
          Pathed.insertAt_nil]
  | i :: rest_e, [], _, .node a cs, t₂, t₃ => by
    show Pathed.insertAt [] t₃ (Pathed.insertAt (i :: rest_e) t₂ (Tree.node a cs)) =
      Pathed.insertAt ((i + 1) :: rest_e) t₂ (Tree.node a (t₃ :: cs))
    by_cases hi : i < cs.length
    · have hi' : i + 1 < (t₃ :: cs).length := by simp; omega
      rw [Pathed.insertAt_cons_of_lt _ _ _ _ _ hi,
          Pathed.insertAt_nil,
          Pathed.insertAt_cons_of_lt _ _ _ _ _ hi']
      simp [List.getElem_cons_succ, List.set_cons_succ]
    · have hi' : ¬ (i + 1 < (t₃ :: cs).length) := by simp; omega
      rw [Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hi,
          Pathed.insertAt_nil,
          Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hi']
  | i :: rest_e, j :: rest_f, h, .node a cs, t₂, t₃ => by
    by_cases hij : i = j
    · -- i = j: recurse via IH on rest_e, rest_f.
      subst hij
      have hrest : rest_f ≠ rest_e := fun heq => h (by rw [heq])
      rw [show preserveOf (i :: rest_e) (i :: rest_f) = i :: preserveOf rest_e rest_f
            from by rw [preserveOf_cons_cons]; simp,
          show preserveOf (i :: rest_f) (i :: rest_e) = i :: preserveOf rest_f rest_e
            from by rw [preserveOf_cons_cons]; simp]
      by_cases hi : i < cs.length
      · have hlen_t2 : i < (cs.set i (Pathed.insertAt rest_e t₂ (cs[i]'hi))).length := by
          rw [List.length_set]; exact hi
        have hlen_t3 : i < (cs.set i (Pathed.insertAt rest_f t₃ (cs[i]'hi))).length := by
          rw [List.length_set]; exact hi
        rw [Pathed.insertAt_cons_of_lt _ _ _ _ _ hi,
            Pathed.insertAt_cons_of_lt _ _ _ _ _ hi,
            Pathed.insertAt_cons_of_lt _ _ _ _ _ hlen_t2,
            Pathed.insertAt_cons_of_lt _ _ _ _ _ hlen_t3,
            List.getElem_set_self, List.getElem_set_self,
            List.set_set, List.set_set,
            insertAt_commute_diff rest_e rest_f hrest (cs[i]'hi) t₂ t₃]
      · rw [Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hi,
            Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hi,
            Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hi,
            Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hi]
    · -- i ≠ j: paths branch at the root; sub-case on bounds.
      rw [show preserveOf (i :: rest_e) (j :: rest_f) = j :: rest_f
            from by rw [preserveOf_cons_cons, if_neg hij],
          show preserveOf (j :: rest_f) (i :: rest_e) = i :: rest_e
            from by rw [preserveOf_cons_cons, if_neg (Ne.symm hij)]]
      by_cases hi : i < cs.length
      · by_cases hj : j < cs.length
        · -- Both in bounds, i ≠ j: use set_comm + getElem_set_ne.
          have hlen_j_after_i : j < (cs.set i (Pathed.insertAt rest_e t₂ (cs[i]'hi))).length := by
            rw [List.length_set]; exact hj
          have hlen_i_after_j : i < (cs.set j (Pathed.insertAt rest_f t₃ (cs[j]'hj))).length := by
            rw [List.length_set]; exact hi
          rw [Pathed.insertAt_cons_of_lt _ _ _ _ _ hi,
              Pathed.insertAt_cons_of_lt _ _ _ _ _ hlen_j_after_i,
              Pathed.insertAt_cons_of_lt _ _ _ _ _ hj,
              Pathed.insertAt_cons_of_lt _ _ _ _ _ hlen_i_after_j,
              List.getElem_set_ne hij,
              List.getElem_set_ne (Ne.symm hij),
              List.set_comm _ _ hij]
        · -- i in bounds, j not: only the t₂-insertion fires.
          have hlen_j_after_i : ¬ (j < (cs.set i (Pathed.insertAt rest_e t₂ (cs[i]'hi))).length) := by
            rw [List.length_set]; exact hj
          rw [Pathed.insertAt_cons_of_lt _ _ _ _ _ hi,
              Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hlen_j_after_i,
              Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hj,
              Pathed.insertAt_cons_of_lt _ _ _ _ _ hi]
      · by_cases hj : j < cs.length
        · -- j in bounds, i not: only the t₃-insertion fires.
          have hlen_i_after_j : ¬ (i < (cs.set j (Pathed.insertAt rest_f t₃ (cs[j]'hj))).length) := by
            rw [List.length_set]; exact hi
          rw [Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hi,
              Pathed.insertAt_cons_of_lt _ _ _ _ _ hj,
              Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hlen_i_after_j]
        · -- Both out of bounds: all no-ops.
          rw [Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hi,
              Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hj,
              Pathed.insertAt_cons_of_not_lt _ _ _ _ _ hi]

/-- **Lifted-equals-nested**: inserting `t₃` at a lifted vertex of `t₂`
    (lifted into `Pathed.insertAt e t₂ t₁`) factors as `insertAt e (insertAt q t₃ t₂)`.

    Pure path arithmetic, no IsValidPath hypotheses needed — the no-op
    fallback of `Pathed.insertAt` handles invalid paths uniformly on
    both sides. -/
theorem insertAt_lift_eq_nested : ∀ (e : Path) (t₁ t₂ t₃ : Tree α) (q : Path),
    Pathed.insertAt (lift e q) t₃ (Pathed.insertAt e t₂ t₁) =
      Pathed.insertAt e (Pathed.insertAt q t₃ t₂) t₁
  | [], .node a cs, t₂, t₃, q => by
    show Pathed.insertAt (0 :: q) t₃ (Tree.node a (t₂ :: cs)) =
         Tree.node a (Pathed.insertAt q t₃ t₂ :: cs)
    simp
  | i :: rest_e, .node a cs, t₂, t₃, q => by
    have hlift : lift (i :: rest_e) q = i :: lift rest_e q := by
      show (i :: rest_e) ++ 0 :: q = i :: (rest_e ++ 0 :: q); rfl
    by_cases h : i < cs.length
    · rw [hlift,
          show Pathed.insertAt (i :: rest_e) t₂ (Tree.node a cs)
              = Tree.node a (cs.set i (Pathed.insertAt rest_e t₂ (cs[i]'h)))
            from Pathed.insertAt_cons_of_lt i rest_e t₂ a cs h]
      have hlen : i < (cs.set i (Pathed.insertAt rest_e t₂ (cs[i]'h))).length := by
        rw [List.length_set]; exact h
      rw [Pathed.insertAt_cons_of_lt i (lift rest_e q) t₃ a _ hlen,
          List.getElem_set_self, List.set_set,
          insertAt_lift_eq_nested rest_e (cs[i]'h) t₂ t₃ q,
          show Pathed.insertAt (i :: rest_e) (Pathed.insertAt q t₃ t₂)
                (Tree.node a cs)
              = Tree.node a (cs.set i (Pathed.insertAt rest_e
                  (Pathed.insertAt q t₃ t₂) (cs[i]'h)))
            from Pathed.insertAt_cons_of_lt i rest_e _ a cs h]
    · rw [hlift,
          Pathed.insertAt_cons_of_not_lt _ _ _ _ _ h,
          Pathed.insertAt_cons_of_not_lt _ _ _ _ _ h,
          Pathed.insertAt_cons_of_not_lt _ _ _ _ _ h]

/-! ## §6: Multiset decomposition of `vertices (insertAt e t₂)`

The 3-class decomposition: every path in `insertAt e t₂ t₁` is either
preserved (from `t₁ \ {e}`), the source `e` itself, or lifted (from
`t₂`). Stated as a Multiset equality with explicit RHS summands.

This is the substrate behind the pre-Lie identity proof in
`Algebra.lean` (§4): each `(insertAt v t₂) ◁ t₃` splits into three
sums, each of which has a clean cancellation against a symmetric
counterpart. -/

/-! ### Substrate: shift lemma for `filterMap (preserve? [])` -/

/-- Bridge lemma for the `e = []` case of `vertices_insertAt_decomp`:
    applying `preserve? []` via `filterMap` to `verticesAux i cs`
    shifts each first-index by +1, yielding `verticesAux (i+1) cs`.
    Pure path-arithmetic, proved by structural induction on `cs`. -/
private theorem filterMap_preserveNil_verticesAux (i : ℕ) (cs : List (Tree α)) :
    List.filterMap (preserve? ([] : Path)) (verticesAux i cs) = verticesAux (i + 1) cs := by
  induction cs generalizing i with
  | nil => rfl
  | cons c cs' ih =>
    rw [verticesAux_cons, List.filterMap_append, verticesAux_cons]
    congr 1
    · -- `(vertices c).map (i :: ·)` has elements `i :: rest`. Each becomes
      -- `(i+1) :: rest` under `preserve? []`. Collapses to `.map ((i+1) :: ·)`.
      rw [List.filterMap_map]
      show (vertices c).filterMap (fun rest => some ((i + 1) :: rest))
          = (vertices c).map ((i + 1) :: ·)
      exact congr_fun (List.filterMap_eq_map' (f := ((i + 1) :: ·))) _
    · exact ih (i + 1)

/-! ### Substrate: list-set decomposition for `verticesAux` -/

/-- Splits `verticesAux offset (cs.set i X)` into prefix-block, swapped i-block, and
    suffix-block. Pure path arithmetic via `List.set_eq_take_append_cons_drop` plus
    `verticesAux_append`. -/
private theorem verticesAux_set (i offset : ℕ) (X : Tree α) (cs : List (Tree α))
    (hi : i < cs.length) :
    verticesAux offset (cs.set i X) =
      verticesAux offset (cs.take i)
      ++ (vertices X).map ((offset + i) :: ·)
      ++ verticesAux (offset + i + 1) (cs.drop (i + 1)) := by
  have hlen : (cs.take i).length = i := by
    rw [List.length_take]; omega
  rw [List.set_eq_take_append_cons_drop, if_pos hi, verticesAux_append,
      verticesAux_cons, hlen, ← List.append_assoc]

/-! ### Substrate: `filterMap (preserve? (i :: rest))` away from `i` -/

/-- When `i` is outside the index range `[offset, offset + cs.length)` covered by
    `verticesAux offset cs`'s first indices, `filterMap (preserve? (i :: rest))` acts
    as identity. Every path is `(offset + k) :: q` with `offset + k ≠ i`, so
    `preserve? (i :: rest) ((offset + k) :: q) = some ((offset + k) :: q)`. -/
private theorem filterMap_preserve?_cons_disjoint :
    ∀ (i : ℕ) (rest : Path) (offset : ℕ) (cs : List (Tree α)),
      (i < offset ∨ offset + cs.length ≤ i) →
      List.filterMap (preserve? (i :: rest)) (verticesAux offset cs) = verticesAux offset cs
  | _, _, _, [], _ => rfl
  | i, rest, offset, c :: cs', h => by
    rw [verticesAux_cons, List.filterMap_append]
    have hoffset_ne : i ≠ offset := by
      rcases h with h | h
      · omega
      · simp only [List.length_cons] at h; omega
    have h' : i < offset + 1 ∨ offset + 1 + cs'.length ≤ i := by
      rcases h with h | h
      · left; omega
      · right; simp only [List.length_cons] at h; omega
    congr 1
    · rw [List.filterMap_map]
      show List.filterMap ((preserve? (i :: rest)) ∘ (offset :: ·)) (vertices c) =
        (vertices c).map (offset :: ·)
      have heq : (preserve? (i :: rest)) ∘ (offset :: ·) = some ∘ (offset :: ·) := by
        funext q
        show preserve? (i :: rest) (offset :: q) = some (offset :: q)
        rw [preserve?_cons_cons, if_neg hoffset_ne]
      rw [heq]
      exact congr_fun (List.filterMap_eq_map (f := (offset :: ·))) _
    · exact filterMap_preserve?_cons_disjoint i rest (offset + 1) cs' h'

/-- **The decomposition lemma** in path form. Assumes `e` is a valid
    path in `t₁`. The preserved class uses `filterMap preserve? e`
    (skipping `e` itself); sourceSelf is the singleton `{e}`; lifted is
    `map (lift e) (vertices t₂)`. -/
theorem vertices_insertAt_decomp : ∀ (e : Path) (t₁ t₂ : Tree α)
    (_he : IsValidPath e t₁),
    ((vertices (Pathed.insertAt e t₂ t₁) : List _) : Multiset Path) =
      ((vertices t₁ : Multiset Path).filterMap (preserve? e))
      + ({sourceSelf e} : Multiset Path)
      + ((vertices t₂ : Multiset Path).map (lift e))
  | [], .node a cs, t₂, _ => by
    -- LHS: vertices (node a (t₂ :: cs)) = [] :: verticesAux 0 (t₂ :: cs)
    --                                   = [] :: ((vertices t₂).map (0 :: ·) ++ verticesAux 1 cs)
    -- RHS: (vertices (node a cs)).filterMap (preserve? [])
    --        = (verticesAux 0 cs).filterMap (preserve? [])    -- [] gives none
    --        = verticesAux 1 cs                                -- bridge lemma
    --      + {[]} + (vertices t₂).map (0 :: ·)
    show ((vertices (Pathed.insertAt [] t₂ (Tree.node a cs)) : List _) :
            Multiset Path) =
        ((vertices (Tree.node a cs) : Multiset Path).filterMap (preserve? []))
          + ({[]} : Multiset Path)
          + ((vertices t₂ : Multiset Path).map (lift []))
    rw [Pathed.insertAt_nil, vertices_node, verticesAux_cons]
    -- LHS: ↑([] :: ((vertices t₂).map (0 :: ·) ++ verticesAux 1 cs))
    show (([] :: ((vertices t₂).map ((0 : ℕ) :: ·) ++ verticesAux (0 + 1) cs)
            : List Path) : Multiset Path) = _
    rw [show (0 : ℕ) + 1 = 1 from rfl]
    -- vertices (node a cs) = [] :: verticesAux 0 cs
    rw [show ((vertices (Tree.node a cs) : Multiset Path).filterMap (preserve? []))
          = (↑([] :: verticesAux 0 cs) : Multiset Path).filterMap (preserve? []) from rfl]
    -- Convert Multiset.filterMap to List.filterMap via Multiset.filterMap_coe
    rw [Multiset.filterMap_coe]
    -- Now LHS = ↑([] :: ...), RHS₁ = ↑(filterMap (preserve? []) ([] :: verticesAux 0 cs))
    rw [show List.filterMap (preserve? ([] : Path)) ([] :: verticesAux 0 cs)
          = verticesAux 1 cs from by
        rw [List.filterMap_cons_none (rfl : preserve? ([] : Path) [] = none),
            filterMap_preserveNil_verticesAux 0]]
    -- LHS: ↑([] :: ((vertices t₂).map (0 :: ·) ++ verticesAux 1 cs))
    -- RHS: ↑(verticesAux 1 cs) + {[]} + ↑((vertices t₂).map (lift []))
    -- Use Multiset.cons_coe + Multiset.coe_add to align the +s
    rw [show ((([] : Path) :: ((vertices t₂).map ((0 : ℕ) :: ·) ++ verticesAux 1 cs)
              : List Path) : Multiset Path)
          = ({[]} : Multiset Path)
              + ↑((vertices t₂).map ((0 : ℕ) :: ·))
              + ↑(verticesAux 1 cs) from by
        rw [show (([] : Path) :: ((vertices t₂).map ((0 : ℕ) :: ·)
                  ++ verticesAux 1 cs) : List Path)
              = [([] : Path)] ++ ((vertices t₂).map ((0 : ℕ) :: ·)
                  ++ verticesAux 1 cs) from rfl,
            ← Multiset.coe_add, ← Multiset.coe_add]
        rfl]
    rw [show (lift ([] : Path)) = ((0 : ℕ) :: ·) from rfl]
    -- Final: {[]} + ↑((vertices t₂).map (0 :: ·)) + ↑(verticesAux 1 cs)
    --      = ↑(verticesAux 1 cs) + {[]} + ↑((vertices t₂).map (0 :: ·))
    -- Pure Multiset commutativity; normalize coerced .map first.
    simp only [Multiset.map_coe]
    abel
  | i :: rest, .node a cs, t₂, hep => by
    obtain ⟨hi, hrest_valid⟩ := hep
    -- IH on (rest, cs[i], t₂).
    have ih : ((vertices (Pathed.insertAt rest t₂ (cs[i]'hi)) : List _) : Multiset Path) =
        ((vertices (cs[i]'hi) : Multiset Path).filterMap (preserve? rest))
        + ({rest} : Multiset Path)
        + ((vertices t₂ : Multiset Path).map (lift rest)) := by
      have := vertices_insertAt_decomp rest (cs[i]'hi) t₂ hrest_valid
      simpa using this
    -- Decompose `verticesAux 0 cs` via `verticesAux_set` with `X = cs[i]`
    -- (using `List.set_getElem_self : cs.set i cs[i] = cs`).
    have hcs : verticesAux 0 cs =
        verticesAux 0 (cs.take i) ++ (vertices (cs[i]'hi)).map ((i : ℕ) :: ·)
          ++ verticesAux (i + 1) (cs.drop (i + 1)) := by
      have h := verticesAux_set i 0 (cs[i]'hi) cs hi
      rw [List.set_getElem_self] at h
      simpa [Nat.zero_add] using h
    -- Disjoint filterMap identities.
    have hL_left : List.filterMap (preserve? (i :: rest)) (verticesAux 0 (cs.take i)) =
        verticesAux 0 (cs.take i) := by
      apply filterMap_preserve?_cons_disjoint
      right
      rw [List.length_take]; omega
    have hL_right : List.filterMap (preserve? (i :: rest))
          (verticesAux (i + 1) (cs.drop (i + 1))) =
        verticesAux (i + 1) (cs.drop (i + 1)) := by
      apply filterMap_preserve?_cons_disjoint
      left; omega
    -- Step 1: unfold both sides of the goal.
    show ((vertices (Pathed.insertAt (i :: rest) t₂ (Tree.node a cs)) : List _) :
            Multiset Path) =
        ((vertices (Tree.node a cs) : Multiset Path).filterMap (preserve? (i :: rest)))
          + ({sourceSelf (i :: rest)} : Multiset Path)
          + ((vertices t₂ : Multiset Path).map (lift (i :: rest)))
    rw [Pathed.insertAt_cons_of_lt _ _ _ _ _ hi]
    simp only [vertices_node]
    rw [verticesAux_set i 0 (Pathed.insertAt rest t₂ (cs[i]'hi)) cs hi, hcs]
    simp only [Nat.zero_add]
    -- Step 2: convert LHS-`[] :: (A ++ B ++ C)` to additive Multiset form, then expose
    -- `↑((vertices T').map (i :: ·))` as `(↑(vertices T')).map (i :: ·)`. Apply IH.
    rw [show ((([] : Path) :: (verticesAux 0 (cs.take i)
                ++ (vertices (Pathed.insertAt rest t₂ (cs[i]'hi))).map ((i : ℕ) :: ·)
                ++ verticesAux (i + 1) (cs.drop (i + 1)))) : List Path)
              = [([] : Path)] ++ verticesAux 0 (cs.take i)
                ++ (vertices (Pathed.insertAt rest t₂ (cs[i]'hi))).map ((i : ℕ) :: ·)
                ++ verticesAux (i + 1) (cs.drop (i + 1)) from rfl,
        show ((([] : Path) :: (verticesAux 0 (cs.take i)
                ++ (vertices (cs[i]'hi)).map ((i : ℕ) :: ·)
                ++ verticesAux (i + 1) (cs.drop (i + 1)))) : List Path)
              = [([] : Path)] ++ verticesAux 0 (cs.take i)
                ++ (vertices (cs[i]'hi)).map ((i : ℕ) :: ·)
                ++ verticesAux (i + 1) (cs.drop (i + 1)) from rfl,
        ← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add,
        ← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add,
        ← Multiset.map_coe ((i : ℕ) :: ·) (vertices (Pathed.insertAt rest t₂ (cs[i]'hi))),
        ← Multiset.map_coe ((i : ℕ) :: ·) (vertices (cs[i]'hi)),
        ih,
        Multiset.map_add, Multiset.map_add, Multiset.map_singleton,
        Multiset.map_filterMap, Multiset.map_map]
    -- Simplify `(preserve? rest q).map (i :: ·) = preserve? (i :: rest) (i :: q)`.
    rw [show (fun q : Path => (preserve? rest q).map ((i : ℕ) :: ·)) =
              (fun q : Path => preserve? (i :: rest) (i :: q)) from by
          funext q
          show (preserve? rest q).map ((i : ℕ) :: ·) = preserve? (i :: rest) (i :: q)
          rw [preserve?_cons_cons, if_pos rfl]]
    -- Simplify `(i :: ·) ∘ lift rest = lift (i :: rest)`.
    rw [show ((i : ℕ) :: ·) ∘ lift rest = lift (i :: rest) from by
          funext q
          show i :: lift rest q = lift (i :: rest) q
          rfl]
    -- Step 3: apply filterMap to RHS pieces.
    rw [Multiset.filterMap_add, Multiset.filterMap_add, Multiset.filterMap_add]
    -- ↑[[]] filterMap'd is ↑[[]] (preserve? (i :: rest) [] = some []).
    rw [show Multiset.filterMap (preserve? (i :: rest))
              ((↑([([] : Path)]) : Multiset Path)) =
            ((↑([([] : Path)]) : Multiset Path)) from by
          rw [Multiset.filterMap_coe]
          rfl]
    -- Disjoint pieces become identity.
    rw [show Multiset.filterMap (preserve? (i :: rest))
              ((↑(verticesAux 0 (cs.take i)) : Multiset Path)) =
            ((↑(verticesAux 0 (cs.take i)) : Multiset Path)) from by
          rw [Multiset.filterMap_coe, hL_left]]
    rw [show Multiset.filterMap (preserve? (i :: rest))
              ((↑(verticesAux (i + 1) (cs.drop (i + 1))) : Multiset Path)) =
            ((↑(verticesAux (i + 1) (cs.drop (i + 1))) : Multiset Path)) from by
          rw [Multiset.filterMap_coe, hL_right]]
    -- The i-block filterMap collapses to filterMap of `i :: q`.
    rw [Multiset.filterMap_map]
    -- Reduce sourceSelf (i :: rest) = i :: rest.
    show _ = _
    simp only [sourceSelf, Function.comp_def]
    abel

/-! ## §7: Preserved-class swap

The (e, f) ↔ (f, e) symmetry for preserved-class double sums. Used by
`assoc_symm_planar` to identify the preserved class of `(t₁ ◁ t₂) ◁ t₃`
with the preserved class of `(t₁ ◁ t₃) ◁ t₂`.

The pointwise bridge is `insertAt_commute_diff`: at distinct paths
`e ≠ f` of `t₁`, grafting `t₂` at `e` then `t₃` at the `f`-image equals
grafting `t₃` at `f` then `t₂` at the `e`-image. The diagonal `e = f` is
discarded by `preserve?_self = none` on both sides. -/

theorem bind_filterMap_preserve?_swap (t₁ t₂ t₃ : Tree α) :
    Multiset.bind (↑(vertices t₁) : Multiset Path) (fun e =>
        Multiset.filterMap (fun f =>
          (preserve? e f).map (fun pos => Pathed.insertAt pos t₃
            (Pathed.insertAt e t₂ t₁)))
          (↑(vertices t₁) : Multiset Path))
    = Multiset.bind (↑(vertices t₁) : Multiset Path) (fun e =>
        Multiset.filterMap (fun f =>
          (preserve? e f).map (fun pos => Pathed.insertAt pos t₂
            (Pathed.insertAt e t₃ t₁)))
          (↑(vertices t₁) : Multiset Path)) := by
  -- Pointwise: at each (e, f), the LHS Option agrees with the RHS Option
  -- under the (e, f) ↔ (f, e) swap.
  have hpw : ∀ e f : Path,
      (preserve? e f).map (fun pos => Pathed.insertAt pos t₃
                                        (Pathed.insertAt e t₂ t₁))
      = (preserve? f e).map (fun pos => Pathed.insertAt pos t₂
                                          (Pathed.insertAt f t₃ t₁)) := by
    intro e f
    by_cases h : f = e
    · subst h
      rw [preserve?_self]
      rfl
    · rw [preserve?_of_ne e f h, preserve?_of_ne f e (Ne.symm h)]
      simp only [Option.map_some]
      congr 1
      exact insertAt_commute_diff e f h t₁ t₂ t₃
  -- Convert filterMap to bind, apply hpw inside, then bind_bind for Fubini swap.
  simp_rw [Multiset.filterMap_eq_bind]
  have step1 : ∀ e f : Path,
      (((preserve? e f).map (fun pos => Pathed.insertAt pos t₃
                                          (Pathed.insertAt e t₂ t₁))).map
          (fun b : Tree α => ({b} : Multiset (Tree α)))).getD 0
      = (((preserve? f e).map (fun pos => Pathed.insertAt pos t₂
                                            (Pathed.insertAt f t₃ t₁))).map
          (fun b : Tree α => ({b} : Multiset (Tree α)))).getD 0 := by
    intros e f; rw [hpw e f]
  rw [show (fun e : Path =>
            (↑(vertices t₁) : Multiset Path).bind (fun f =>
              (((preserve? e f).map (fun pos => Pathed.insertAt pos t₃
                                                  (Pathed.insertAt e t₂ t₁))).map
                (fun b : Tree α => ({b} : Multiset (Tree α)))).getD 0)) =
          (fun e =>
            (↑(vertices t₁) : Multiset Path).bind (fun f =>
              (((preserve? f e).map (fun pos => Pathed.insertAt pos t₂
                                                  (Pathed.insertAt f t₃ t₁))).map
                (fun b : Tree α => ({b} : Multiset (Tree α)))).getD 0)) from
        funext fun e => Multiset.bind_congr (fun f _ => step1 e f)]
  rw [Multiset.bind_bind]

end Pathed

end RootedTree.Tree
