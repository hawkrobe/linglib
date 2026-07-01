/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insert
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Filter

set_option autoImplicit false

/-!
# Multi-path multi-tree grafting and vertex decomposition for `RoseTree α`
[foissy-typed-decorated-rooted-trees-2018]
[foissy-introduction-hopf-algebras-trees]

`multiGraft T pairs` grafts trees onto `T` at multiple paths
**simultaneously**, with paths interpreted in the *original* `T`
(Foissy 2021 convention). The pair list `List (Path × RoseTree α)` allows
multiple grafts at the same vertex (preserving pair-list order, which
matters at the root and at each common host vertex; commutativity at the
multiset boundary is upstream in `Insertion.lean`).

The headline theorem `vertices_multiGraft_decomp` partitions the path set
of `multiGraft T pairs` into three classes paralleling `vertices_insertAt_decomp`:

* **preserved**: vertices of `T \ pairSources` transported through the
  cumulative ancestor-source shifts.
* **sourceSelf**: vertices of `T ∩ pairSources` (sources of pair grafts),
  each at its transported original path. Distinct sources contribute
  multiplicity 1 each — sharing a source does not duplicate the host vertex.
* **lifted**: for each pair `k = (eₖ, Tₖ)` and each `q ∈ vertices Tₖ`, the
  path `transport pairs eₖ ++ posₖ :: q`, where `posₖ` is `k`'s position
  among pairs sharing source `eₖ` (in pair-list order, per Foissy 2021
  convention).

This decomposition is the vertex-multiset substrate for multi-graft
analysis. The deprecated A3.3 basis-level approach to Oudom-Guin
Prop 2.7.v has been superseded by the abstract pre-Lie route — see
`Linglib/Core/Algebra/PreLie/OudomGuinCirc.lean` and
`scratch/pivot_to_prelie_pbw.md`.

## Specialization to single-pair

`multiGraft T [(e, T₂)] = insertAt e T₂ T` (`multiGraft_singleton`), and
under that specialization the helpers reduce:

* `transport [(e, T₂)] = id` on paths disjoint from `e`'s descendants;
  `e ⊏ f → transport [(e, T₂)] f` shifts `f`'s child index past `e` by `+1`.
* `preserveMulti [(e, T₂)] = preserve? e`.
* `liftMulti [(e, T₂)] ⟨0, _⟩ q = lift e q`.

`vertices_multiGraft_decomp` therefore implies `vertices_insertAt_decomp`
as a corollary (§9).

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

- §1: Filter helpers (`rootPrependFilter`, `headChildFilter`, `tailChildFilter`).
- §2: `multiGraft` / `multiGraftChildren` mutual definitions + simp lemmas.
- §3: Nil identity (`multiGraft T [] = T`).
- §4: Singleton bridge (`multiGraft T [(p, T₂)] = insertAt p T₂ T`).
- §5: `descentToChild`, `rootPrependCount` — pair-list operations mirroring
  the `multiGraft` recursion.
- §6: `transport` — total path transformer applying cumulative ancestor shifts.
- §7: `pairSources`, `preserveMulti` — the preserve-or-drop function.
- §8: `posInGroup`, `liftMulti` — the lifted-vertex path embedding.
- §9: `vertices_multiGraft_decomp` — the headline theorem.
- §10: Single-pair specialization corollaries (depend on §9).

Sibling files:
- `Path.lean` — Path / IsValidPath / vertices / verticesAux.
- `Insert.lean` — single-pair `insertAt` + single-pair vertex decomposition.

## Status

`[UPSTREAM]` candidate. Sorry-free through §10.6, including the descent
case of `multiGraft_split_lifted_aux` (path-arithmetic substrate for
A3.3 cons-case Phase 4.2). The headline `vertices_multiGraft_decomp`
(§9) is closed via the §8.5–§8.9 substrate: descent helpers,
`liftMulti_at_root` / `liftMulti_at_child_descent`, `root_bind_eq`
(root-pair bridge), `bind_descent_eq_aux` (descent-pair bridge),
`bind_finRange_singleton_eq` (validity-based per-`k` decomp).
-/

namespace RoseTree

namespace Pathed

variable {α : Type*}

/-- A child subtree has strictly fewer nodes than its parent. The
    well-founded measure witnessing termination of the tree recursions
    below (`vertices_multiGraft_decomp`, `multiGraft_split_lifted_aux`,
    `multiGraft_cons_pair`), which descend into the `i`-th child. -/
private theorem numNodes_lt_of_getElem {a : α} {cs : List (RoseTree α)} {i : ℕ}
    (hi : i < cs.length) : (cs[i]'hi).numNodes < (RoseTree.node a cs).numNodes := by
  rw [numNodes_node]
  have hsum : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.sum := by
    intro l x hx
    induction l with
    | nil => simp at hx
    | cons c cs ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · simp
      · have := ih hx; simp only [List.sum_cons]; omega
  have := hsum (List.mem_map_of_mem (f := numNodes) (List.getElem_mem hi))
  omega

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

/-! ## §5: Pair-list operations mirroring `multiGraft` recursion

`multiGraft` descends pairs into children via `headChildFilter` (paths
starting with `0`) and `tailChildFilter` (paths starting with `k+1`).
The combined effect on the i-th child is captured by `descentToChild i`,
which keeps pairs whose path begins with `i` and strips that index.

Root prepends — pairs with empty path — are counted by `rootPrependCount`,
which determines the `+N` child-index shift seen by every original-T vertex
at the current level. -/

/-- Filter the pair list to those whose path begins with `i`, stripping
    the leading index. The resulting paths address vertices in the
    `i`-th child. -/
def descentToChild (i : ℕ) :
    List (Path × RoseTree α) → List (Path × RoseTree α)
  | []                          => []
  | ([], _) :: rest             => descentToChild i rest
  | (j :: rest_p, T) :: rest    =>
      if i = j then (rest_p, T) :: descentToChild i rest
      else descentToChild i rest

@[simp] theorem descentToChild_nil (i : ℕ) :
    descentToChild (α := α) i [] = [] := rfl

@[simp] theorem descentToChild_cons_nilPath (i : ℕ) (T : RoseTree α)
    (rest : List (Path × RoseTree α)) :
    descentToChild i (([], T) :: rest) = descentToChild i rest := rfl

theorem descentToChild_cons_consPath (i j : ℕ) (rest_p : Path)
    (T : RoseTree α) (rest : List (Path × RoseTree α)) :
    descentToChild i ((j :: rest_p, T) :: rest) =
      (if i = j then (rest_p, T) :: descentToChild i rest
       else descentToChild i rest) := rfl

@[simp] theorem descentToChild_cons_consPath_eq (i : ℕ) (rest_p : Path)
    (T : RoseTree α) (rest : List (Path × RoseTree α)) :
    descentToChild i ((i :: rest_p, T) :: rest) =
      (rest_p, T) :: descentToChild i rest := by
  rw [descentToChild_cons_consPath, if_pos rfl]

theorem descentToChild_cons_consPath_ne (i j : ℕ) (rest_p : Path)
    (T : RoseTree α) (rest : List (Path × RoseTree α)) (h : i ≠ j) :
    descentToChild i ((j :: rest_p, T) :: rest) =
      descentToChild i rest := by
  rw [descentToChild_cons_consPath, if_neg h]

/-- Number of pairs whose path is `[]` — the root-prepend count at the
    current level. Determines the `+N` shift of every original-T child index. -/
def rootPrependCount (pairs : List (Path × RoseTree α)) : ℕ :=
  (pairs.filter (fun pair => pair.fst = [])).length

@[simp] theorem rootPrependCount_nil :
    rootPrependCount (α := α) [] = 0 := rfl

@[simp] theorem rootPrependCount_cons_nilPath (T : RoseTree α)
    (rest : List (Path × RoseTree α)) :
    rootPrependCount (([], T) :: rest) = rootPrependCount rest + 1 := by
  unfold rootPrependCount
  simp

@[simp] theorem rootPrependCount_cons_consPath (j : ℕ) (rest_p : Path)
    (T : RoseTree α) (rest : List (Path × RoseTree α)) :
    rootPrependCount ((j :: rest_p, T) :: rest) = rootPrependCount rest := by
  unfold rootPrependCount
  simp

/-! ## §6: `transport` — total path transformer

`transport pairs f` computes the new path of an original-T vertex `f` in
`multiGraft T pairs`. Pure path arithmetic; works for any `f`, even those
not in `vertices T` (no validity hypothesis). -/

/-- Recursive path transformer: at each level, shift the child index by
    the root-prepend count, then descend with the projected pair list. -/
def transport : List (Path × RoseTree α) → Path → Path
  | _, []           => []
  | pairs, i :: rest =>
      (i + rootPrependCount pairs) ::
        transport (descentToChild i pairs) rest

@[simp] theorem transport_nil_path (pairs : List (Path × RoseTree α)) :
    transport pairs [] = [] := rfl

@[simp] theorem transport_cons_path (pairs : List (Path × RoseTree α))
    (i : ℕ) (rest : Path) :
    transport pairs (i :: rest) =
      (i + rootPrependCount pairs) ::
        transport (descentToChild i pairs) rest := rfl

@[simp] theorem transport_empty_pairs (f : Path) :
    transport (α := α) [] f = f := by
  induction f with
  | nil => rfl
  | cons i rest ih =>
    rw [transport_cons_path, rootPrependCount_nil, descentToChild_nil, ih,
        Nat.add_zero]

/-! ## §7: `pairSources`, `preserveMulti` — the preserve-or-drop function

`pairSources` is the underlying list of pair source paths. `preserveMulti`
returns `none` on any pair source (excluding it from the preserved class)
and `some (transport pairs f)` otherwise. -/

/-- The list of pair source paths (in pair-list order; may contain
    duplicates if multiple pairs share a source). -/
def pairSources (pairs : List (Path × RoseTree α)) : List Path :=
  pairs.map Prod.fst

@[simp] theorem pairSources_nil : pairSources (α := α) [] = [] := rfl

@[simp] theorem pairSources_cons (p : Path) (T : RoseTree α)
    (rest : List (Path × RoseTree α)) :
    pairSources ((p, T) :: rest) = p :: pairSources rest := rfl

/-- The preserve-or-drop function for the multi-pair case.
    - `none` if `f` is any pair source (excluded from the preserved class).
    - `some (transport pairs f)` otherwise (transport applies the
      cumulative ancestor-source shifts).

    Mirrors `preserve?` for the single-pair case. -/
def preserveMulti (pairs : List (Path × RoseTree α)) (f : Path) : Option Path :=
  if f ∈ pairSources pairs then none else some (transport pairs f)

@[simp] theorem preserveMulti_empty (f : Path) :
    preserveMulti (α := α) [] f = some f := by
  unfold preserveMulti
  simp

/-! ## §7.5: A3.3 substrate — `preserved + sourceSelf = vertices.map transport`

The preserved-class `filterMap (preserveMulti pairs)` and the sourceSelf-class
`filter (∈ pairSources) .map (transport pairs)` partition `vertices T` by
membership in `pairSources pairs`. Combined, they cover all of `vertices T`,
each mapped under `transport pairs`. -/

/-- `filterMap (preserveMulti pairs)` decomposes as `filter (∉ pairSources)`
    composed with `map (transport pairs)`. Direct from the `if-none-else-some`
    shape of `preserveMulti`. -/
theorem filterMap_preserveMulti_eq_filter_map_transport
    (pairs : List (Path × RoseTree α)) (vs : Multiset Path) :
    vs.filterMap (preserveMulti pairs) =
      (vs.filter (· ∉ pairSources pairs)).map (transport pairs) := by
  refine Multiset.induction_on vs (by simp) (fun a s ih => ?_)
  by_cases h : a ∈ pairSources pairs
  · have h_none : preserveMulti pairs a = none := by
      unfold preserveMulti; simp [h]
    rw [Multiset.filterMap_cons_none _ _ h_none, ih]
    have h_filter : Multiset.filter (fun x => x ∉ pairSources pairs) (a ::ₘ s) =
        Multiset.filter (fun x => x ∉ pairSources pairs) s :=
      Multiset.filter_cons_of_neg _ (fun hp => hp h)
    rw [h_filter]
  · have h_some : preserveMulti pairs a = some (transport pairs a) := by
      unfold preserveMulti; simp [h]
    rw [Multiset.filterMap_cons_some _ _ _ h_some, ih]
    have h_filter : Multiset.filter (fun x => x ∉ pairSources pairs) (a ::ₘ s) =
        a ::ₘ Multiset.filter (fun x => x ∉ pairSources pairs) s :=
      Multiset.filter_cons_of_pos _ h
    rw [h_filter, Multiset.map_cons]

/-- The preserved + sourceSelf classes of `vertices (multiGraft T pairs)`
    together equal `vertices T` mapped under `transport pairs`. -/
theorem preserved_add_sourceSelf_eq_vertices_map_transport
    (pairs : List (Path × RoseTree α)) (vs : Multiset Path) :
    vs.filterMap (preserveMulti pairs) +
      (vs.filter (· ∈ pairSources pairs)).map (transport pairs) =
    vs.map (transport pairs) := by
  rw [filterMap_preserveMulti_eq_filter_map_transport, ← Multiset.map_add]
  congr 1
  rw [add_comm]
  exact Multiset.filter_add_not _ _

/-! ## §8: `posInGroup`, `liftMulti` — lifted-vertex paths

For pair `k = (eₖ, Tₖ)`, vertices `q ∈ vertices Tₖ` lift to
`transport pairs eₖ ++ posₖ :: q`, where `posₖ` is `k`'s 0-indexed
position among pairs targeting `eₖ` (in pair-list order). When all pairs
have distinct sources, every `posₖ = 0`. -/

/-- Position of pair `k` among pairs sharing the same source path
    (counting only earlier pairs in pair-list order). -/
def posInGroup (pairs : List (Path × RoseTree α)) (k : Fin pairs.length) : ℕ :=
  ((pairs.take k.val).filter (fun pair => pair.fst = pairs[k].fst)).length

/-- The path of vertex `q ∈ vertices (pairs[k].snd)` in `multiGraft T pairs`. -/
def liftMulti (pairs : List (Path × RoseTree α)) (k : Fin pairs.length)
    (q : Path) : Path :=
  transport pairs pairs[k].fst ++ (posInGroup pairs k :: q)

/-! ## §8.5: Substrate lemmas for the decomposition

Five identities needed by the main proof:

1. `length_filterMap_rootPrependFilter`: the rootPrepends list has length
   equal to `rootPrependCount pairs`.
2. `descentToChild_zero`: `descentToChild 0 pairs = pairs.filterMap headChildFilter`.
3. `descentToChild_succ`: `descentToChild (i+1) pairs = descentToChild i (pairs.filterMap tailChildFilter)`.
4. `descent_pairSources_iff`: `rest ∈ pairSources (descentToChild i pairs) ↔ (i :: rest) ∈ pairSources pairs`.
5. `preserveMulti_cons`: `preserveMulti pairs (i :: rest) =
     (preserveMulti (descentToChild i pairs) rest).map ((i + rootPrependCount pairs) :: ·)`.

These bridge the multiGraft recursion (on filterMap headChildFilter / tailChildFilter)
to the path-arithmetic operations (descentToChild, rootPrependCount, transport). -/

/-- Length of the root-prepends list equals `rootPrependCount`. -/
@[simp] theorem length_filterMap_rootPrependFilter : ∀ (pairs : List (Path × RoseTree α)),
    (pairs.filterMap rootPrependFilter).length = rootPrependCount pairs
  | [] => rfl
  | ([], T) :: rest => by
    have h : List.filterMap rootPrependFilter ((([], T) :: rest) : List (Path × RoseTree α))
             = T :: rest.filterMap rootPrependFilter := rfl
    rw [h, List.length_cons, length_filterMap_rootPrependFilter rest,
        rootPrependCount_cons_nilPath]
  | (i :: rest_p, T) :: rest => by
    have h : List.filterMap rootPrependFilter (((i :: rest_p, T) :: rest) : List (Path × RoseTree α))
             = rest.filterMap rootPrependFilter := rfl
    rw [h, length_filterMap_rootPrependFilter rest,
        rootPrependCount_cons_consPath]

/-- `descentToChild 0 pairs` agrees with `pairs.filterMap headChildFilter`. -/
theorem descentToChild_zero : ∀ (pairs : List (Path × RoseTree α)),
    descentToChild 0 pairs = pairs.filterMap headChildFilter
  | [] => rfl
  | ([], T) :: rest => by
    rw [descentToChild_cons_nilPath, descentToChild_zero rest]
    simp [headChildFilter_of_nil]
  | (0 :: rest_p, T) :: rest => by
    rw [descentToChild_cons_consPath_eq 0 rest_p T rest, descentToChild_zero rest]
    simp [headChildFilter_of_zero_cons]
  | ((k + 1) :: rest_p, T) :: rest => by
    rw [descentToChild_cons_consPath_ne 0 (k + 1) rest_p T rest (by omega),
        descentToChild_zero rest]
    simp [headChildFilter_of_succ_cons]

/-- `descentToChild (i+1) pairs` agrees with descending into the `i`-th child of
    `pairs.filterMap tailChildFilter`. The shift `(k+1) :: rest ↦ k :: rest`
    on tail-child paths exactly cancels the `+1` in the descent index. -/
theorem descentToChild_succ (i : ℕ) : ∀ (pairs : List (Path × RoseTree α)),
    descentToChild (i + 1) pairs = descentToChild i (pairs.filterMap tailChildFilter)
  | [] => rfl
  | ([], T) :: rest => by
    rw [descentToChild_cons_nilPath, descentToChild_succ i rest]
    simp [tailChildFilter_of_nil]
  | (0 :: rest_p, T) :: rest => by
    rw [descentToChild_cons_consPath_ne (i + 1) 0 rest_p T rest (by omega),
        descentToChild_succ i rest]
    simp [tailChildFilter_of_zero_cons]
  | ((k + 1) :: rest_p, T) :: rest => by
    by_cases h : i = k
    · subst h
      rw [descentToChild_cons_consPath_eq (i + 1) rest_p T rest,
          show ((((i + 1) :: rest_p, T) :: rest : List (Path × RoseTree α)).filterMap
                tailChildFilter) = (i :: rest_p, T) :: rest.filterMap tailChildFilter
            from by simp [tailChildFilter_of_succ_cons],
          descentToChild_cons_consPath_eq i rest_p T (rest.filterMap tailChildFilter),
          descentToChild_succ i rest]
    · have h' : ¬ (i + 1 = k + 1) := fun heq => h (by omega)
      rw [descentToChild_cons_consPath_ne (i + 1) (k + 1) rest_p T rest h',
          show ((((k + 1) :: rest_p, T) :: rest : List (Path × RoseTree α)).filterMap
                tailChildFilter) = (k :: rest_p, T) :: rest.filterMap tailChildFilter
            from by simp [tailChildFilter_of_succ_cons],
          descentToChild_cons_consPath_ne i k rest_p T (rest.filterMap tailChildFilter) h,
          descentToChild_succ i rest]

/-- A path `rest` is a source of the descended pair list iff `i :: rest` is a
    source of the original pair list. -/
theorem descent_pairSources_iff (i : ℕ) (rest : Path) :
    ∀ (pairs : List (Path × RoseTree α)),
    rest ∈ pairSources (descentToChild i pairs) ↔ (i :: rest) ∈ pairSources pairs
  | [] => by simp
  | ([], T) :: pairs' => by
    rw [descentToChild_cons_nilPath, pairSources_cons, List.mem_cons,
        descent_pairSources_iff i rest pairs']
    exact ⟨Or.inr, fun h => h.resolve_left (List.cons_ne_nil i rest)⟩
  | (j :: rest_p, T) :: pairs' => by
    by_cases h : i = j
    · subst h
      rw [descentToChild_cons_consPath_eq i rest_p T pairs', pairSources_cons,
          pairSources_cons, List.mem_cons, List.mem_cons,
          descent_pairSources_iff i rest pairs',
          show ((i :: rest) = (i :: rest_p) ↔ rest = rest_p) from
            ⟨fun heq => (List.cons.injEq _ _ _ _).mp heq |>.right,
             fun heq => congr_arg (i :: ·) heq⟩]
    · rw [descentToChild_cons_consPath_ne i j rest_p T pairs' h,
          pairSources_cons, List.mem_cons,
          descent_pairSources_iff i rest pairs']
      exact ⟨Or.inr, fun hor => hor.resolve_left
        (fun heq => h ((List.cons.injEq _ _ _ _).mp heq).left)⟩

/-- The decomposition of `preserveMulti` over a `cons` path: descending into
    child `i` strips the leading `i` and shifts the next index by the
    `rootPrependCount`. -/
theorem preserveMulti_cons (pairs : List (Path × RoseTree α)) (i : ℕ) (rest : Path) :
    preserveMulti pairs (i :: rest) =
      (preserveMulti (descentToChild i pairs) rest).map
        ((i + rootPrependCount pairs) :: ·) := by
  unfold preserveMulti
  by_cases h : (i :: rest) ∈ pairSources pairs
  · rw [if_pos h, if_pos ((descent_pairSources_iff i rest pairs).mpr h)]
    rfl
  · rw [if_neg h, if_neg (fun hmem => h ((descent_pairSources_iff i rest pairs).mp hmem))]
    rw [transport_cons_path]
    rfl

/-- Membership in `descentToChild i pairs` — a pair `(rest, T)` appears iff
    the original `(i :: rest, T)` appears in `pairs`. The .snd is preserved
    under descent; the .fst loses its leading `i`. -/
theorem mem_descentToChild_iff (i : ℕ) (rest : Path) (T : RoseTree α) :
    ∀ (pairs : List (Path × RoseTree α)),
    (rest, T) ∈ descentToChild i pairs ↔ (i :: rest, T) ∈ pairs
  | [] => by simp
  | ([], T') :: pairs' => by
    rw [descentToChild_cons_nilPath, mem_descentToChild_iff i rest T pairs',
        List.mem_cons]
    refine ⟨Or.inr, ?_⟩
    rintro (heq | h)
    · injection heq with hpath _
      exact absurd hpath (List.cons_ne_nil i rest)
    · exact h
  | (j :: rest_p, T') :: pairs' => by
    by_cases h : i = j
    · subst h
      rw [descentToChild_cons_consPath_eq i rest_p T' pairs',
          List.mem_cons, List.mem_cons,
          mem_descentToChild_iff i rest T pairs']
      refine ⟨?_, ?_⟩
      · rintro (heq | h_mem)
        · refine Or.inl ?_
          injection heq with hfs hsn
          rw [hfs, hsn]
        · exact Or.inr h_mem
      · rintro (heq | h_mem)
        · refine Or.inl ?_
          injection heq with hfs hsn
          injection hfs with _ hrest_eq
          rw [hrest_eq, hsn]
        · exact Or.inr h_mem
    · rw [descentToChild_cons_consPath_ne i j rest_p T' pairs' h,
          List.mem_cons,
          mem_descentToChild_iff i rest T pairs']
      refine ⟨Or.inr, ?_⟩
      rintro (heq | h_mem)
      · injection heq with hfs _
        injection hfs with hji _
        exact (h hji).elim
      · exact h_mem

/-- Per-child validity: if every pair source is valid in `node a cs`, then
    every descended pair (under child `i`) has its source valid in `cs[i]`.
    Used by the main `vertices_multiGraft_decomp` proof to derive the IH
    hypothesis on each child. -/
theorem descentToChild_valid_of_node (a : α) (cs : List (RoseTree α))
    (pairs : List (Path × RoseTree α))
    (h_valid : ∀ pair ∈ pairs, IsValidPath pair.fst (RoseTree.node a cs))
    (i : Fin cs.length) :
    ∀ pair ∈ descentToChild i.val pairs, IsValidPath pair.fst cs[i.val] := by
  intro pair hmem
  obtain ⟨rest, T_pair⟩ := pair
  have horig : (i.val :: rest, T_pair) ∈ pairs :=
    (mem_descentToChild_iff i.val rest T_pair pairs).mp hmem
  have h_orig_valid := h_valid (i.val :: rest, T_pair) horig
  obtain ⟨_, h_rest⟩ := (isValidPath_cons i.val rest a cs).mp h_orig_valid
  exact h_rest

/-! ## §8.6: Children-block companion lemma

The main theorem's structural decomposition needs a companion lemma giving
the per-child unfolding of `verticesAux N (multiGraftChildren cs pairs)`.
This is mutually recursive with the main theorem (the companion calls main
on each `cs[i]`, which is structurally smaller than `node a cs`). -/

/-- Children-block structural unfolding: the verticesAux of multiGraftChildren
    decomposes as a sum over child indices, each prepended with `(offset + i)`.
    Pure structural unfolding — does not yet apply the main theorem's 3-class
    decomposition; the main theorem applies that after unfolding. -/
private theorem verticesAux_multiGraftChildren_unfold :
    ∀ (cs : List (RoseTree α)) (pairs : List (Path × RoseTree α)) (offset : ℕ),
    ((verticesAux offset (multiGraftChildren cs pairs) : List Path) : Multiset Path) =
      (Multiset.ofList (List.finRange cs.length)).bind fun i =>
        ((vertices (multiGraft cs[i.val] (descentToChild i.val pairs)) : List Path) :
          Multiset Path).map ((offset + i.val) :: ·)
  | [], _, _ => by
    rw [multiGraftChildren_nil_cs, verticesAux_nil]
    show ((↑([] : List Path)) : Multiset Path) = _
    simp [List.finRange_zero]
  | c :: cs', pairs, offset => by
    -- Step 1: unfold LHS, distribute Multiset coercion over append.
    rw [multiGraftChildren_cons_cs, verticesAux_cons]
    rw [show (((vertices (multiGraft c (pairs.filterMap headChildFilter))).map
                ((offset : ℕ) :: ·) ++
              verticesAux (offset + 1) (multiGraftChildren cs'
                (pairs.filterMap tailChildFilter)) : List Path) : Multiset Path) =
            (((vertices (multiGraft c (pairs.filterMap headChildFilter))).map
                ((offset : ℕ) :: ·) : List Path) : Multiset Path) +
            ((verticesAux (offset + 1) (multiGraftChildren cs'
                (pairs.filterMap tailChildFilter)) : List Path) : Multiset Path)
        from by rw [← Multiset.coe_add]]
    -- Step 2: apply IH on cs'.
    rw [verticesAux_multiGraftChildren_unfold cs' (pairs.filterMap tailChildFilter) (offset + 1)]
    -- Step 3: bridge via descentToChild_zero (head) + descentToChild_succ (tail).
    rw [show pairs.filterMap headChildFilter = descentToChild 0 pairs from
          (descentToChild_zero pairs).symm]
    -- Inside IH bind: rewrite the `descentToChild j.val (pairs.filterMap tailChildFilter)`
    -- to `descentToChild (j.val + 1) pairs`, and also normalize the offset arithmetic.
    rw [show (Multiset.ofList (List.finRange cs'.length)).bind (fun j =>
              ((vertices (multiGraft cs'[j.val]
                  (descentToChild j.val (pairs.filterMap tailChildFilter))) : List Path) :
                Multiset Path).map ((offset + 1 + j.val) :: ·)) =
            (Multiset.ofList (List.finRange cs'.length)).bind (fun j =>
              ((vertices (multiGraft cs'[j.val] (descentToChild (j.val + 1) pairs)) :
                List Path) : Multiset Path).map ((offset + (j.val + 1)) :: ·))
        from by
          refine Multiset.bind_congr fun j _ => ?_
          rw [← descentToChild_succ j.val pairs,
              show offset + 1 + j.val = offset + (j.val + 1) from by omega]]
    -- Step 4: expand RHS bind via List.finRange_succ.
    -- RHS bind is over `Fin (c :: cs').length`. By definitional equality
    -- `(c :: cs').length = cs'.length + 1`, this is `Fin (cs'.length + 1)`.
    -- `List.finRange_succ` rewrites `List.finRange (n+1) = 0 :: (finRange n).map Fin.succ`.
    show _ = (Multiset.ofList (List.finRange (cs'.length + 1))).bind fun i =>
              ((vertices (multiGraft (c :: cs')[i.val] (descentToChild i.val pairs)) :
                List Path) : Multiset Path).map ((offset + i.val) :: ·)
    rw [List.finRange_succ]
    rw [show ((Multiset.ofList ((0 : Fin (cs'.length + 1)) ::
              (List.finRange cs'.length).map Fin.succ) : Multiset (Fin (cs'.length + 1))) =
            (0 : Fin (cs'.length + 1)) ::ₘ
              Multiset.ofList ((List.finRange cs'.length).map Fin.succ))
        from rfl,
        Multiset.cons_bind]
    -- Reduce the head term.
    rw [show ((c :: cs') : List (RoseTree α))[(0 : Fin (cs'.length + 1)).val] = c from rfl,
        show offset + (0 : Fin (cs'.length + 1)).val = offset from by
          show offset + 0 = offset; omega]
    -- Tail bind: convert via Multiset.bind_map.
    rw [show Multiset.ofList ((List.finRange cs'.length).map Fin.succ) =
            (Multiset.ofList (List.finRange cs'.length)).map Fin.succ from rfl]
    rw [Multiset.bind_map]
    -- Now both sides have shape `head_term + bind (Fin cs'.length) (...)` and should match.
    refine congr_arg _ ?_
    refine Multiset.bind_congr fun j _ => ?_
    rfl

/-! ## §8.7: Helpers for the 3-class decomposition proof

Three helpers needed by the headline proof:

1. `verticesAux_unfold`: the no-graft companion of
   `verticesAux_multiGraftChildren_unfold` — `verticesAux offset cs` as a
   bind over child indices. Specializes the multi-graft version with
   `pairs = []`.
2. `preserveMulti_cons_post_map`: pointwise bridge identifying
   `(preserveMulti (descentToChild i pairs) f).map ((i + N) :: ·)`
   with `preserveMulti pairs (i :: f)`. Uses `preserveMulti_cons`.
3. `transport_descent_via_cons`: pointwise bridge identifying
   `transport (descentToChild i pairs) f` (after prepending) with
   `transport pairs (i :: f)`. Uses `transport_cons_path`.
-/

/-- No-graft companion of `verticesAux_multiGraftChildren_unfold`: the
    paths in `verticesAux offset cs` decompose as a bind over child
    indices, each prepended with `(offset + i)`. Proof is by structural
    induction on `cs` (no mutual recursion needed). -/
private theorem verticesAux_unfold :
    ∀ (cs : List (RoseTree α)) (offset : ℕ),
    ((verticesAux offset cs : List Path) : Multiset Path) =
      (Multiset.ofList (List.finRange cs.length)).bind fun i =>
        ((vertices cs[i.val] : List Path) : Multiset Path).map ((offset + i.val) :: ·)
  | [], _ => by
    rw [verticesAux_nil]
    show ((↑([] : List Path)) : Multiset Path) = _
    simp [List.finRange_zero]
  | c :: cs', offset => by
    rw [verticesAux_cons]
    rw [show (((vertices c).map ((offset : ℕ) :: ·) ++
              verticesAux (offset + 1) cs' : List Path) : Multiset Path) =
            (((vertices c).map ((offset : ℕ) :: ·) : List Path) : Multiset Path) +
            ((verticesAux (offset + 1) cs' : List Path) : Multiset Path)
        from by rw [← Multiset.coe_add]]
    rw [verticesAux_unfold cs' (offset + 1)]
    -- RHS: bind over Fin (c :: cs').length = Fin (cs'.length + 1).
    show _ = (Multiset.ofList (List.finRange (cs'.length + 1))).bind fun i =>
              ((vertices ((c :: cs') : List (RoseTree α))[i.val] : List Path) :
                Multiset Path).map ((offset + i.val) :: ·)
    rw [List.finRange_succ]
    rw [show ((Multiset.ofList ((0 : Fin (cs'.length + 1)) ::
              (List.finRange cs'.length).map Fin.succ) : Multiset (Fin (cs'.length + 1))) =
            (0 : Fin (cs'.length + 1)) ::ₘ
              Multiset.ofList ((List.finRange cs'.length).map Fin.succ))
        from rfl,
        Multiset.cons_bind]
    rw [show ((c :: cs') : List (RoseTree α))[(0 : Fin (cs'.length + 1)).val] = c from rfl,
        show offset + (0 : Fin (cs'.length + 1)).val = offset from by
          show offset + 0 = offset; omega]
    rw [show Multiset.ofList ((List.finRange cs'.length).map Fin.succ) =
            (Multiset.ofList (List.finRange cs'.length)).map Fin.succ from rfl]
    rw [Multiset.bind_map]
    refine congr_arg _ ?_
    refine Multiset.bind_congr fun j _ => ?_
    rw [show offset + 1 + j.val = offset + (j.val + 1) from by omega]
    rfl

/-- Pointwise bridge: `(preserveMulti (descentToChild i pairs) f).map ((N + i) :: ·) =
    preserveMulti pairs (i :: f)`, where `N = rootPrependCount pairs`. Direct
    consequence of `preserveMulti_cons` after commuting addition. -/
private theorem preserveMulti_cons_post_map (pairs : List (Path × RoseTree α))
    (i : ℕ) (f : Path) :
    (preserveMulti (descentToChild i pairs) f).map
      ((rootPrependCount pairs + i) :: ·) = preserveMulti pairs (i :: f) := by
  rw [preserveMulti_cons, show rootPrependCount pairs + i = i + rootPrependCount pairs
      from by omega]

/-- Pointwise bridge: `(N + i) :: transport (descentToChild i pairs) f =
    transport pairs (i :: f)`, where `N = rootPrependCount pairs`. Direct
    consequence of `transport_cons_path` after commuting addition. -/
private theorem transport_cons_descent (pairs : List (Path × RoseTree α))
    (i : ℕ) (f : Path) :
    (rootPrependCount pairs + i) :: transport (descentToChild i pairs) f =
      transport pairs (i :: f) := by
  rw [transport_cons_path, show rootPrependCount pairs + i = i + rootPrependCount pairs
      from by omega]

/-! ## §8.8: Bijection helpers for the lifted bridge (step 8)

The (i, k') ↔ k bijection between descent-indexed pairs and original pairs.
Built around `descentCount` (a counting form of `descentToChild i pairs`'s length)
and `descentIdxOf` (the descent-corresponding index function).

Properties needed by step 8:
- `descentToChild_length_eq`: `(descentToChild i pairs).length = descentCount i pairs`.
- `descentToChild_take`: walking-the-prefix gives a prefix-of-the-walk.
- `descentToChild_getElem`: characterizes `(descentToChild i pairs)[k']`.
- `descentIdxOf_lt`: validity of `descentIdxOf` as a `Fin`-index.
- `posInGroup_descent_invariance`: posInGroup is preserved under descent.

The bijection is implicit; step 8 uses these properties to re-organize the
LHS bind to match RHS via `Multiset.bind_congr` after `transport_cons_descent`. -/

/-- Number of pairs in `pairs` whose first index is `i`. Equals
    `(descentToChild i pairs).length`. -/
private def descentCount (i : ℕ) (pairs : List (Path × RoseTree α)) : ℕ :=
  (pairs.filter (fun pair => pair.fst.head? = some i)).length

@[simp] private theorem descentCount_nil (i : ℕ) :
    descentCount (α := α) i [] = 0 := rfl

@[simp] private theorem descentCount_cons_nilPath (i : ℕ) (T : RoseTree α)
    (rest : List (Path × RoseTree α)) :
    descentCount i (([], T) :: rest) = descentCount i rest := by
  unfold descentCount
  simp [List.filter_cons]

@[simp] private theorem descentCount_cons_consPath_eq (i : ℕ) (rest_p : Path)
    (T : RoseTree α) (rest : List (Path × RoseTree α)) :
    descentCount i ((i :: rest_p, T) :: rest) = descentCount i rest + 1 := by
  unfold descentCount
  simp [List.filter_cons]

private theorem descentCount_cons_consPath_ne (i j : ℕ) (rest_p : Path)
    (T : RoseTree α) (rest : List (Path × RoseTree α)) (h : i ≠ j) :
    descentCount i ((j :: rest_p, T) :: rest) = descentCount i rest := by
  unfold descentCount
  rw [List.filter_cons]
  simp [Ne.symm h]

/-- `(descentToChild i pairs).length = descentCount i pairs`. The descent
    operation matches the count of pairs with the right head. -/
private theorem descentToChild_length_eq (i : ℕ) :
    ∀ (pairs : List (Path × RoseTree α)),
    (descentToChild i pairs).length = descentCount i pairs
  | [] => rfl
  | ([], _) :: rest => by
    rw [descentToChild_cons_nilPath, descentToChild_length_eq i rest,
        descentCount_cons_nilPath]
  | (j :: rest_p, T) :: rest => by
    by_cases h : i = j
    · subst h
      rw [descentToChild_cons_consPath_eq i rest_p T rest, List.length_cons,
          descentToChild_length_eq i rest, descentCount_cons_consPath_eq]
    · rw [descentToChild_cons_consPath_ne i j rest_p T rest h,
          descentToChild_length_eq i rest, descentCount_cons_consPath_ne i j _ T rest h]

/-- `descentToChild` distributes over `++`. -/
private theorem descentToChild_append (i : ℕ) :
    ∀ (xs ys : List (Path × RoseTree α)),
    descentToChild i (xs ++ ys) = descentToChild i xs ++ descentToChild i ys
  | [], ys => by simp [descentToChild]
  | ([], T) :: xs', ys => by
    rw [List.cons_append, descentToChild_cons_nilPath, descentToChild_cons_nilPath,
        descentToChild_append i xs' ys]
  | (j :: rest_p, T) :: xs', ys => by
    by_cases h : i = j
    · subst h
      rw [List.cons_append, descentToChild_cons_consPath_eq, descentToChild_cons_consPath_eq,
          descentToChild_append i xs' ys, List.cons_append]
    · rw [List.cons_append, descentToChild_cons_consPath_ne i j rest_p T (xs' ++ ys) h,
          descentToChild_cons_consPath_ne i j rest_p T xs' h,
          descentToChild_append i xs' ys]

/-- `descentCount` distributes over `++`. -/
private theorem descentCount_append (i : ℕ) :
    ∀ (xs ys : List (Path × RoseTree α)),
    descentCount i (xs ++ ys) = descentCount i xs + descentCount i ys
  | [], _ => by simp
  | x :: xs', ys => by
    unfold descentCount
    rw [List.cons_append, List.filter_cons, List.filter_cons]
    by_cases h : x.fst.head? = some i
    · simp [h, descentCount_append i xs' ys, descentCount, Nat.add_right_comm]
    · simp [h, descentCount_append i xs' ys, descentCount]

/-- The descent-corresponding index. Given `pairs[k].fst.head? = some i`,
    `descentIdxOf i pairs k` is the position of `k` among the descent-i pairs
    (0-indexed). -/
private def descentIdxOf (i : ℕ) (pairs : List (Path × RoseTree α))
    (k : Fin pairs.length) : ℕ :=
  descentCount i (pairs.take k.val)

/-- `descentIdxOf` is bounded by `descentCount` of the full list, when
    `pairs[k].fst.head? = some i`. -/
private theorem descentIdxOf_lt (i : ℕ) (pairs : List (Path × RoseTree α))
    (k : Fin pairs.length) (h : pairs[k.val].fst.head? = some i) :
    descentIdxOf i pairs k < descentCount i pairs := by
  unfold descentIdxOf descentCount
  -- pairs decomposes around k.
  have hsplit : pairs = pairs.take k.val ++ pairs[k.val] :: pairs.drop (k.val + 1) := by
    rw [List.cons_getElem_drop_succ]
    exact (List.take_append_drop k.val pairs).symm
  conv_rhs => rw [hsplit]
  rw [List.filter_append, List.length_append, List.filter_cons]
  rw [show decide (pairs[k.val].fst.head? = some i) = true from by simp [h]]
  simp [List.length_cons]

/-- `descentToChild` of the prefix is the prefix of `descentToChild`.
    Together with `descentToChild_length_eq` this characterizes
    `descentToChild i pairs` index-by-index. -/
private theorem descentToChild_take (i : ℕ) (pairs : List (Path × RoseTree α)) (m : ℕ) :
    descentToChild i (pairs.take m) =
      (descentToChild i pairs).take (descentCount i (pairs.take m)) := by
  -- Decompose pairs as pairs.take m ++ pairs.drop m, apply descentToChild_append.
  rw [← descentToChild_length_eq]
  conv_rhs => rw [show descentToChild i pairs =
                    descentToChild i (pairs.take m ++ pairs.drop m) from by
                      rw [List.take_append_drop],
                  descentToChild_append, List.take_left]

/-- The element of `descentToChild i pairs` at index `descentIdxOf i pairs k`
    (when `pairs[k].fst = i :: rest`) is `(rest, pairs[k].snd)`. -/
private theorem descentToChild_getElem_at_descentIdxOf (i : ℕ)
    (pairs : List (Path × RoseTree α)) (k : Fin pairs.length) (rest : Path)
    (h : pairs[k.val].fst = i :: rest) :
    (descentToChild i pairs)[descentIdxOf i pairs k]'(by
        rw [descentToChild_length_eq]
        exact descentIdxOf_lt i pairs k (by rw [h]; rfl)) =
      (rest, pairs[k.val].snd) := by
  -- Strategy: rewrite the LHS list (descentToChild i pairs) by splitting pairs around k.
  -- Use that getElem on `xs ++ ys` at index `xs.length + j` is `ys[j]`.
  -- Avoid rewriting pairs itself (dependent types); instead transform descentToChild i pairs.
  have hdec : descentToChild i pairs =
      descentToChild i (pairs.take k.val) ++
      descentToChild i (pairs[k.val] :: pairs.drop (k.val + 1)) := by
    rw [← descentToChild_append i (pairs.take k.val)
        (pairs[k.val] :: pairs.drop (k.val + 1))]
    congr 1
    rw [List.cons_getElem_drop_succ]
    exact (List.take_append_drop k.val pairs).symm
  have hidx : descentIdxOf i pairs k = (descentToChild i (pairs.take k.val)).length := by
    unfold descentIdxOf
    rw [descentToChild_length_eq]
  -- Apply hdec to the LHS list, fixing the index proof via List.getElem_of_eq.
  -- Strategy: rebuild the goal so that the index is literally `0` after both
  -- list rewriting and arithmetic, then close by rfl. We do this in a single
  -- `show` to avoid the dependent-rewrite trap of `rw [show idx = 0 ...]`.
  have hpkdec : (pairs[k.val] :: pairs.drop (k.val + 1)) =
      ((i :: rest, pairs[k.val].snd) :: pairs.drop (k.val + 1)) := by
    rw [show pairs[k.val] = (i :: rest, pairs[k.val].snd) from by
          rw [Prod.mk.injEq]; exact ⟨h, rfl⟩]
  have hdec' : descentToChild i pairs =
      descentToChild i (pairs.take k.val) ++
        ((rest, pairs[k.val].snd) :: descentToChild i (pairs.drop (k.val + 1))) := by
    rw [hdec]
    congr 1
    rw [hpkdec]
    exact descentToChild_cons_consPath_eq i rest pairs[k.val].snd (pairs.drop (k.val + 1))
  -- Reduce both index and list together. The index `descentIdxOf i pairs k` equals
  -- `(descentToChild i (pairs.take k.val)).length`, and the corresponding element
  -- in the appended cons-list is the head, namely `(rest, pairs[k.val].snd)`.
  rw [List.getElem_of_eq hdec' _]
  rw [List.getElem_append_right (by omega : (descentToChild i (pairs.take k.val)).length ≤ descentIdxOf i pairs k)]
  -- The remaining index `descentIdxOf i pairs k - (descentToChild i (pairs.take k.val)).length`
  -- is `0`, picking the head of the cons-list. Use `List.getElem_cons_zero` after
  -- rewriting the index via `List.getElem_of_eq` on the index proof, by proving
  -- the new shape is a cons.
  have hidx0 : descentIdxOf i pairs k - (descentToChild i (pairs.take k.val)).length = 0 := by
    rw [hidx]; omega
  -- Use a non-dependent `congr_arg` on the entire getElem expression. The cleanest
  -- way is to reduce by hand on the head: getElem on a cons at a specific index.
  -- Simply transport via the index equality using `Eq.mpr`.
  refine Eq.trans ?_ rfl
  -- Convert the goal to using index `0` instead of the difference.
  -- The list `(rest, pairs[k.val].snd) :: descentToChild i (pairs.drop (k.val+1))`
  -- at index 0 is `(rest, pairs[k.val].snd)`.
  conv_lhs => rw [show
      ((rest, pairs[k.val].snd) :: descentToChild i (pairs.drop (k.val + 1)))[
        descentIdxOf i pairs k - (descentToChild i (pairs.take k.val)).length]'(by
          rw [hidx0]; simp) =
      ((rest, pairs[k.val].snd) :: descentToChild i (pairs.drop (k.val + 1)))[0]'(by simp)
        from by congr 1 <;> rw [hidx0]]
  rfl

/-- Position invariance: for `pairs[k].fst = i :: rest`, the descent-corresponding
    index `descentIdxOf i pairs k` has the same `posInGroup` in `descentToChild i pairs`
    as `k` does in `pairs`. -/
private theorem posInGroup_descent_invariance (i : ℕ) (pairs : List (Path × RoseTree α))
    (k : Fin pairs.length) (rest : Path) (h : pairs[k.val].fst = i :: rest) :
    posInGroup (descentToChild i pairs)
        ⟨descentIdxOf i pairs k, by
          rw [descentToChild_length_eq]
          exact descentIdxOf_lt i pairs k (by rw [h]; rfl)⟩ =
      posInGroup pairs k := by
  unfold posInGroup
  -- LHS: ((descentToChild i pairs).take (descentIdxOf i pairs k)).filter (·.fst = (descentToChild i pairs)[descentIdxOf].fst).length
  -- = (descentToChild i (pairs.take k)).filter (·.fst = rest).length    [via descentToChild_take + getElem]
  -- RHS: (pairs.take k).filter (·.fst = i :: rest).length
  -- Both `posInGroup` calls use `Fin` indexing (`pairs[⟨..⟩]`); convert to
  -- `Nat` indexing via `Fin.getElem_fin`, then rewrite the getElem-fst via
  -- the substrate getElem characterization. Use `simp only` to dodge the
  -- `decide`-instance dependency that breaks bare `rw`.
  simp only [Fin.getElem_fin,
             descentToChild_getElem_at_descentIdxOf i pairs k rest h, h]
  rw [show ((descentToChild i pairs).take (descentIdxOf i pairs k)) =
          descentToChild i (pairs.take k.val) from by
        rw [descentToChild_take]
        congr]
  -- Now: (descentToChild i (pairs.take k)).filter (·.fst = rest).length
  --    = (pairs.take k).filter (·.fst = i :: rest).length
  show ((descentToChild i (pairs.take k.val)).filter (fun pair => decide (pair.fst = rest))).length =
      ((pairs.take k.val).filter (fun pair => decide (pair.fst = i :: rest))).length
  -- Prove by induction on pairs.take k.
  induction pairs.take k.val with
  | nil => simp
  | cons p ps ih =>
    rcases p with ⟨pfst, psnd⟩
    cases pfst with
    | nil =>
      rw [descentToChild_cons_nilPath, List.filter_cons]
      simp [ih]
    | cons j rest_p =>
      by_cases hij : i = j
      · subst hij
        rw [descentToChild_cons_consPath_eq i rest_p psnd ps,
            List.filter_cons, List.filter_cons]
        by_cases hr : rest_p = rest
        · subst hr
          simp [ih]
        · simp [hr, ih]
      · rw [descentToChild_cons_consPath_ne i j rest_p psnd ps hij,
            List.filter_cons]
        have : ¬ ((j :: rest_p : Path) = (i :: rest)) := by
          intro heq
          injection heq with heq1 _
          exact hij heq1.symm
        simp [this, ih]

/-- `descentIdxOf` past a head pair: the descent count grows by one iff
    the head pair's source matches `i`, otherwise it's preserved.
    Subsumes the per-shape versions (nil-head / matching cons / non-matching
    cons) via the `if`-discriminator. -/
private theorem descentIdxOf_cons_succ (i : ℕ) (p : Path × RoseTree α)
    (rest : List (Path × RoseTree α)) (k : Fin rest.length) :
    descentIdxOf i (p :: rest) (Fin.succ k) =
      descentIdxOf i rest k + (if p.fst.head? = some i then 1 else 0) := by
  unfold descentIdxOf
  show descentCount i ((p :: rest).take ((Fin.succ k).val)) =
       descentCount i (rest.take k.val) + _
  rw [show (Fin.succ k).val = k.val + 1 from rfl,
      show (p :: rest).take (k.val + 1) = p :: rest.take k.val from rfl]
  unfold descentCount
  rw [List.filter_cons]
  by_cases h : p.fst.head? = some i
  · simp [h]
  · simp [h]

/-- `descentIdxOf` at index zero on any non-empty pair list is zero — no
    pairs precede the head. -/
private theorem descentIdxOf_at_zero (i : ℕ) (pairs : List (Path × RoseTree α))
    (h0 : 0 < pairs.length) :
    descentIdxOf i pairs ⟨0, h0⟩ = 0 := by
  unfold descentIdxOf
  show descentCount i (pairs.take 0) = 0
  rw [List.take_zero]
  rfl

/-! ## §8.9: Step-8 lifted bridge — bijection on bind indices

Step 8 of `vertices_multiGraft_decomp` is a multiset equation between two
re-indexings of the same family of "lifted" vertex contributions:

  LHS = ↑(verticesAux 0 rootPrepends)
        + bind_{i : Fin n} (head-shift ∘ bind_{k' : descentToChild i pairs} liftMulti)
  RHS = bind_{k : Fin pairs.length} liftMulti pairs k ∘ ↑vertices pairs[k].snd

Strategy: split RHS into root-pair and child-pair contributions via
`Multiset.filter_add_not + add_bind`, then identify each half with the
corresponding LHS part:

* **Root half.** For `k` with `pairs[k].fst = []`,
  `liftMulti pairs k q = posInGroup pairs k :: q`. By induction on `pairs`,
  the root-pair bind equals `↑(verticesAux 0 rootPrepends)`.
* **Child half.** For `k` with `pairs[k].fst = i :: rest`,
  `liftMulti pairs k q = (N + i) :: liftMulti (descent i pairs) ⟨descentIdxOf i pairs k, _⟩ q`
  (via `posInGroup_descent_invariance` + `descentToChild_getElem_at_descentIdxOf`).
  By induction on `pairs`, the head-`i` slice equals
  `map ((N+i)::·) (bind_{k'} ...)`. Summing over `i ∈ Fin cs.length`
  recovers LHS Part 2 under the validity hypothesis. -/

/-- `liftMulti` at a root-pair (`pairs[k].fst = []`): the lifted path is
    just `posInGroup pairs k :: q`. Direct from `transport_empty_path` +
    the definition of `liftMulti`. -/
private theorem liftMulti_at_root (pairs : List (Path × RoseTree α))
    (k : Fin pairs.length) (h : pairs[k.val].fst = [])
    (q : Path) :
    liftMulti pairs k q = posInGroup pairs k :: q := by
  show transport pairs pairs[k.val].fst ++ (posInGroup pairs k :: q) =
       posInGroup pairs k :: q
  rw [h, transport_nil_path, List.nil_append]

/-- `liftMulti` at a child-pair (`pairs[k].fst = i :: rest`): the lifted
    path factors as `(N + i) :: (lifted via descent)`, where the descent
    index is `descentIdxOf i pairs k`. Combines `transport_cons_path`
    (head shift) with `posInGroup_descent_invariance` + the descent
    `getElem` characterization. -/
private theorem liftMulti_at_child_descent (pairs : List (Path × RoseTree α))
    (k : Fin pairs.length) (i : ℕ) (rest : Path) (h : pairs[k.val].fst = i :: rest)
    (q : Path) :
    liftMulti pairs k q =
      (rootPrependCount pairs + i) ::
        liftMulti (descentToChild i pairs)
          ⟨descentIdxOf i pairs k, by
            rw [descentToChild_length_eq]
            exact descentIdxOf_lt i pairs k (by rw [h]; rfl)⟩ q := by
  have hdesc_lt : descentIdxOf i pairs k < (descentToChild i pairs).length := by
    rw [descentToChild_length_eq]
    exact descentIdxOf_lt i pairs k (by rw [h]; rfl)
  have hpos :
      posInGroup (descentToChild i pairs) ⟨descentIdxOf i pairs k, hdesc_lt⟩ =
        posInGroup pairs k :=
    posInGroup_descent_invariance i pairs k rest h
  unfold liftMulti
  simp only [Fin.getElem_fin,
             descentToChild_getElem_at_descentIdxOf i pairs k rest h, h, hpos,
             transport_cons_path, List.cons_append]
  congr 1
  omega

/-- `posInGroup` recursive characterization at index `0`: the head pair has
    no earlier same-source pairs, so its position in its group is always `0`. -/
private theorem posInGroup_cons_zero (p : Path) (T : RoseTree α)
    (rest : List (Path × RoseTree α)) :
    posInGroup ((p, T) :: rest)
      ⟨0, Nat.succ_pos _⟩ = 0 := by
  unfold posInGroup
  simp

/-- `posInGroup` at a successor index, when the head pair has source `[]`
    and the indexed pair also has source `[]`: the count grows by one. -/
private theorem posInGroup_cons_succ_root (T : RoseTree α)
    (pairs' : List (Path × RoseTree α)) (k : Fin pairs'.length)
    (h : pairs'[k.val].fst = []) :
    posInGroup (([], T) :: pairs') k.succ = posInGroup pairs' k + 1 := by
  unfold posInGroup
  show (((([], T) :: pairs').take (k.succ.val)).filter
          (fun pair => pair.fst = (([], T) :: pairs')[k.succ.val].fst)).length =
       ((pairs'.take k.val).filter (fun pair => pair.fst = pairs'[k.val].fst)).length + 1
  show (((([], T) :: pairs').take (k.val + 1)).filter
          (fun pair => pair.fst = (([], T) :: pairs')[k.val + 1].fst)).length =
       ((pairs'.take k.val).filter (fun pair => pair.fst = pairs'[k.val].fst)).length + 1
  rw [show (([], T) :: pairs').take (k.val + 1) =
          (([], T) : Path × RoseTree α) :: pairs'.take k.val from rfl,
      show (([], T) :: pairs')[k.val + 1] = pairs'[k.val] from rfl,
      h, List.filter_cons]
  simp

/-- `posInGroup` at a successor index, when the head pair has source `[]`
    but the indexed pair has non-`[]` source: the count is unchanged. -/
private theorem posInGroup_cons_succ_root_of_ne (T : RoseTree α)
    (pairs' : List (Path × RoseTree α)) (k : Fin pairs'.length)
    (h : pairs'[k.val].fst ≠ []) :
    posInGroup (([], T) :: pairs') k.succ = posInGroup pairs' k := by
  unfold posInGroup
  show (((([], T) :: pairs').take (k.succ.val)).filter
          (fun pair => pair.fst = (([], T) :: pairs')[k.succ.val].fst)).length =
       ((pairs'.take k.val).filter (fun pair => pair.fst = pairs'[k.val].fst)).length
  show (((([], T) :: pairs').take (k.val + 1)).filter
          (fun pair => pair.fst = (([], T) :: pairs')[k.val + 1].fst)).length =
       ((pairs'.take k.val).filter (fun pair => pair.fst = pairs'[k.val].fst)).length
  rw [show (([], T) :: pairs').take (k.val + 1) =
          (([], T) : Path × RoseTree α) :: pairs'.take k.val from rfl,
      show (([], T) :: pairs')[k.val + 1] = pairs'[k.val] from rfl,
      List.filter_cons]
  simp [Ne.symm h]

/-- `posInGroup` at a successor index, when the head pair has non-`[]`
    source: the count is unchanged regardless of the indexed pair's source. -/
private theorem posInGroup_cons_succ_child (i : ℕ) (rest_p : Path) (T : RoseTree α)
    (pairs' : List (Path × RoseTree α)) (k : Fin pairs'.length) :
    posInGroup ((i :: rest_p, T) :: pairs') k.succ =
    posInGroup pairs' k +
      (if (i :: rest_p : Path) = pairs'[k.val].fst then 1 else 0) := by
  unfold posInGroup
  show ((((i :: rest_p, T) :: pairs').take (k.succ.val)).filter
          (fun pair => pair.fst = ((i :: rest_p, T) :: pairs')[k.succ.val].fst)).length =
       ((pairs'.take k.val).filter (fun pair => pair.fst = pairs'[k.val].fst)).length +
         (if (i :: rest_p : Path) = pairs'[k.val].fst then 1 else 0)
  show ((((i :: rest_p, T) :: pairs').take (k.val + 1)).filter
          (fun pair => pair.fst = ((i :: rest_p, T) :: pairs')[k.val + 1].fst)).length =
       ((pairs'.take k.val).filter (fun pair => pair.fst = pairs'[k.val].fst)).length +
         (if (i :: rest_p : Path) = pairs'[k.val].fst then 1 else 0)
  rw [show ((i :: rest_p, T) :: pairs').take (k.val + 1) =
          ((i :: rest_p, T) : Path × RoseTree α) :: pairs'.take k.val from rfl,
      show ((i :: rest_p, T) :: pairs')[k.val + 1] = pairs'[k.val] from rfl,
      List.filter_cons]
  by_cases h : (i :: rest_p : Path) = pairs'[k.val].fst
  · simp [h]
  · simp [h]

/-- `verticesAux` shifts uniformly: `verticesAux (offset+1) cs` equals
    `verticesAux offset cs` with each path's head index incremented by 1.
    Stated as a Multiset equality via `verticesAux_unfold`. -/
private theorem verticesAux_succ (cs : List (RoseTree α)) (offset : ℕ) :
    (↑(verticesAux (offset + 1) cs) : Multiset Path) =
      (↑(verticesAux offset cs) : Multiset Path).map
        (fun p => match p with | [] => [] | h :: q => (h + 1) :: q) := by
  rw [verticesAux_unfold cs (offset + 1), verticesAux_unfold cs offset, Multiset.map_bind]
  refine Multiset.bind_congr fun i _ => ?_
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun q _ => ?_
  show (offset + 1 + i.val) :: q =
       (match ((offset + i.val) :: q : Path) with | [] => [] | h :: q => (h + 1) :: q)
  show (offset + 1 + i.val) :: q = (offset + i.val + 1) :: q
  congr 1; omega

/-! ### Root-pair bridge

The conditional bind over `Fin pairs.length`-indices, contributing
`(vertices pairs[k].snd).map ((offset + posInGroup pairs k) :: ·)` for
root pairs (and `0` otherwise), equals `↑(verticesAux offset rootPrepends)`.
Strengthened with `offset` to support induction on `pairs`. -/
private theorem root_bind_eq : ∀ (pairs : List (Path × RoseTree α)) (offset : ℕ),
    ((↑(List.finRange pairs.length) : Multiset (Fin pairs.length)).bind fun k =>
        if pairs[k.val].fst = [] then
          ((vertices pairs[k.val].snd : List Path) : Multiset Path).map
            ((offset + posInGroup pairs k) :: ·)
        else 0) =
      (↑(verticesAux offset (pairs.filterMap rootPrependFilter)) : Multiset Path)
  | [], offset => by
    show ((↑(List.finRange 0) : Multiset (Fin 0)).bind _) =
         (↑(verticesAux offset ([] : List (RoseTree α))) : Multiset Path)
    rw [List.finRange_zero, verticesAux_nil]
    show ((0 : Multiset (Fin 0)).bind _) = (↑([] : List Path) : Multiset Path)
    rw [Multiset.zero_bind]; rfl
  | (p, T) :: pairs', offset => by
    -- Decompose Fin (pairs'.length + 1) via List.finRange_succ.
    have hfin : (↑(List.finRange ((p, T) :: pairs').length) :
                 Multiset (Fin ((p, T) :: pairs').length)) =
                (0 : Fin ((p, T) :: pairs').length) ::ₘ
                  ((↑(List.finRange pairs'.length) : Multiset (Fin pairs'.length)).map
                    Fin.succ) := by
      show (↑(List.finRange (pairs'.length + 1)) : Multiset (Fin (pairs'.length + 1))) = _
      rw [List.finRange_succ, ← Multiset.cons_coe, ← Multiset.map_coe]
    rw [hfin, Multiset.cons_bind, Multiset.bind_map]
    -- Head term g ⟨0, _⟩.
    rw [show (((p, T) :: pairs')[(0 : Fin ((p, T) :: pairs').length).val] = (p, T)) from rfl]
    -- Tail bind in terms of pairs' indices.
    -- The tail iterates k' : Fin pairs'.length with index Fin.succ k'.
    rw [show (fun (k' : Fin pairs'.length) =>
              (fun (k : Fin ((p, T) :: pairs').length) =>
                if ((p, T) :: pairs')[k.val].fst = [] then
                  ((vertices ((p, T) :: pairs')[k.val].snd : List Path) :
                    Multiset Path).map
                    ((offset + posInGroup ((p, T) :: pairs') k) :: ·)
                else 0) (Fin.succ k')) =
            (fun (k' : Fin pairs'.length) =>
              if pairs'[k'.val].fst = [] then
                ((vertices pairs'[k'.val].snd : List Path) : Multiset Path).map
                  ((offset + posInGroup ((p, T) :: pairs') (Fin.succ k')) :: ·)
              else 0)
        from by
          funext k'
          show (if ((p, T) :: pairs')[(Fin.succ k').val].fst = [] then _ else 0) = _
          rw [show ((p, T) :: pairs')[(Fin.succ k').val] = pairs'[k'.val] from rfl]]
    -- Case-split on p.
    by_cases hp : p = []
    · -- Sub-case A: head is a root pair.
      subst hp
      -- Head contributes (vertices T).map (offset :: ·).
      rw [show (if (([], T) : Path × RoseTree α).fst = [] then
                  ((vertices T : List Path) : Multiset Path).map
                    ((offset + posInGroup (([], T) :: pairs') 0) :: ·)
                else 0) =
              ((vertices T : List Path) : Multiset Path).map (offset :: ·) from by
        rw [if_pos rfl,
            show posInGroup (([], T) :: pairs') (0 : Fin _) = 0
              from posInGroup_cons_zero ([] : Path) T pairs']
        simp only [Nat.add_zero]]
      -- For tail: posInGroup new ⟨k'+1, _⟩ for root k' = posInGroup pairs' ⟨k', _⟩ + 1.
      rw [show (fun (k' : Fin pairs'.length) =>
                if pairs'[k'.val].fst = [] then
                  ((vertices pairs'[k'.val].snd : List Path) : Multiset Path).map
                    ((offset + posInGroup (([], T) :: pairs') (Fin.succ k')) :: ·)
                else 0) =
              (fun (k' : Fin pairs'.length) =>
                if pairs'[k'.val].fst = [] then
                  ((vertices pairs'[k'.val].snd : List Path) : Multiset Path).map
                    (((offset + 1) + posInGroup pairs' k') :: ·)
                else 0)
          from by
            funext k'
            split_ifs with hk'
            · refine Multiset.map_congr rfl fun q _ => ?_
              rw [posInGroup_cons_succ_root T pairs' k' hk']
              show (offset + (posInGroup pairs' k' + 1)) :: q =
                   (offset + 1 + posInGroup pairs' k') :: q
              have : offset + (posInGroup pairs' k' + 1) =
                     offset + 1 + posInGroup pairs' k' := by omega
              rw [this]
            · rfl]
      -- Apply IH on pairs' with offset+1.
      rw [root_bind_eq pairs' (offset + 1)]
      -- Combine: (vertices T).map (offset::·) + ↑(verticesAux (offset+1) (rootPrepends_old))
      --        = ↑(verticesAux offset (T :: rootPrepends_old))
      show ((vertices T : List Path) : Multiset Path).map (offset :: ·) +
           (↑(verticesAux (offset + 1) (pairs'.filterMap rootPrependFilter))
              : Multiset Path) =
           (↑(verticesAux offset
              ((([], T) :: pairs' : List (Path × RoseTree α)).filterMap rootPrependFilter))
              : Multiset Path)
      rw [show (([], T) :: pairs' : List (Path × RoseTree α)).filterMap rootPrependFilter
              = T :: pairs'.filterMap rootPrependFilter from rfl,
          verticesAux_cons]
      rw [← Multiset.coe_add, ← Multiset.map_coe]
    · -- Sub-case B: head is a child pair. Head contributes 0.
      have hp_fst_ne : (p, T).fst ≠ [] := hp
      rw [show (if ((p, T) : Path × RoseTree α).fst = [] then _
                else (0 : Multiset Path)) = 0 from if_neg hp_fst_ne, Multiset.zero_add]
      -- For tail: posInGroup new ⟨k'+1, _⟩ for root k' = posInGroup pairs' ⟨k', _⟩
      -- (since p ≠ [] doesn't match []).
      -- p has the form (i :: rest_p), so we need posInGroup_cons_succ_child applied.
      obtain ⟨i, rest_p, hp_eq⟩ : ∃ i rest_p, p = i :: rest_p := by
        cases p with
        | nil => exact absurd rfl hp
        | cons i rest_p => exact ⟨i, rest_p, rfl⟩
      subst hp_eq
      rw [show (fun (k' : Fin pairs'.length) =>
                if pairs'[k'.val].fst = [] then
                  ((vertices pairs'[k'.val].snd : List Path) : Multiset Path).map
                    ((offset + posInGroup ((i :: rest_p, T) :: pairs') (Fin.succ k')) :: ·)
                else 0) =
              (fun (k' : Fin pairs'.length) =>
                if pairs'[k'.val].fst = [] then
                  ((vertices pairs'[k'.val].snd : List Path) : Multiset Path).map
                    ((offset + posInGroup pairs' k') :: ·)
                else 0)
          from by
            funext k'
            split_ifs with hk'
            · refine Multiset.map_congr rfl fun q _ => ?_
              rw [posInGroup_cons_succ_child i rest_p T pairs' k']
              -- (i :: rest_p) ≠ [] = pairs'[k'].fst, so the if returns 0.
              have hne : (i :: rest_p : Path) ≠ pairs'[k'.val].fst := by
                rw [hk']; exact List.cons_ne_nil _ _
              rw [if_neg hne]
              show (offset + (posInGroup pairs' k' + 0)) :: q =
                   (offset + posInGroup pairs' k') :: q
              have : offset + (posInGroup pairs' k' + 0) =
                     offset + posInGroup pairs' k' := by omega
              rw [this]
            · rfl]
      -- Apply IH on pairs'.
      rw [root_bind_eq pairs' offset]
      -- rootPrepends ((i :: rest_p, T) :: pairs') = rootPrepends pairs' (since (i :: rest_p, T)
      -- is not a root pair).
      show (↑(verticesAux offset (pairs'.filterMap rootPrependFilter)) : Multiset Path) =
           (↑(verticesAux offset
              (((i :: rest_p, T) :: pairs' : List (Path × RoseTree α)).filterMap
                rootPrependFilter)) : Multiset Path)
      rw [show ((i :: rest_p, T) :: pairs' : List (Path × RoseTree α)).filterMap
              rootPrependFilter = pairs'.filterMap rootPrependFilter from rfl]

/-! ### Descent-pair bridge

The conditional bind over `Fin pairs.length`-indices, contributing
`F ⟨descentIdxOf i pairs k, _⟩` exactly when `pairs[k].fst.head? = some i`,
equals the bind over `Fin (descentToChild i pairs).length` of the same
`F`. Parameterized by an external `n` (instead of
`(descentToChild i pairs).length`) to dodge the dependent-rewrite trap when
recursing on `pairs`: in sub-case B (`i = j` head), the recursive call
needs to produce an `F'` of type `Fin n' → Multiset β` for `n' = n - 1`,
which is impossible if `F`'s type is tied to a `pairs`-dependent
expression. Threading `n` as an independent parameter and `h_len` as the
identification lets the recursion in B re-bind `F'` cleanly. The sole
caller passes `(descentToChild i.val pairs).length` and `rfl`. -/
private theorem bind_descent_eq_aux (i : ℕ) :
    ∀ (pairs : List (Path × RoseTree α)) (n : ℕ)
      (_h_len : (descentToChild i pairs).length = n)
      {β : Type*} (F : Fin n → Multiset β),
    ((↑(List.finRange pairs.length) : Multiset (Fin pairs.length)).bind fun k =>
      if h : pairs[k.val].fst.head? = some i then
        F ⟨descentIdxOf i pairs k, by
              rw [← _h_len, descentToChild_length_eq]
              exact descentIdxOf_lt i pairs k h⟩
      else (0 : Multiset β)) =
    (↑(List.finRange n) : Multiset (Fin n)).bind F
  | [], n, h_len, _, F => by
    have hn : n = 0 := by rw [← h_len]; rfl
    subst hn
    show ((↑(List.finRange 0) : Multiset (Fin 0)).bind _) =
         ((↑(List.finRange 0) : Multiset (Fin 0)).bind F)
    rw [List.finRange_zero]
    show ((0 : Multiset (Fin 0)).bind _) = ((0 : Multiset (Fin 0)).bind F)
    rw [Multiset.zero_bind, Multiset.zero_bind]
  | (p, T) :: pairs', n, h_len, β, F => by
    -- Decompose Fin (pairs'.length + 1) via List.finRange_succ.
    have hfin : (↑(List.finRange ((p, T) :: pairs').length) :
                 Multiset (Fin ((p, T) :: pairs').length)) =
                (0 : Fin ((p, T) :: pairs').length) ::ₘ
                  ((↑(List.finRange pairs'.length) : Multiset (Fin pairs'.length)).map
                    Fin.succ) := by
      show (↑(List.finRange (pairs'.length + 1)) : Multiset (Fin (pairs'.length + 1))) = _
      rw [List.finRange_succ, ← Multiset.cons_coe, ← Multiset.map_coe]
    rw [hfin, Multiset.cons_bind, Multiset.bind_map]
    cases p with
    | nil =>
      -- Sub-case A: head pair is `([], T)`. Head term is 0 (head? = none ≠ some i);
      -- tail descentIdxOf preserved → IH on pairs' with same n.
      have h_n_pairs' : (descentToChild i pairs').length = n := h_len
      have h_head_neg : ¬ ((([], T) :: pairs')[(0 : Fin (([], T) :: pairs').length).val].fst.head?
                            = some i) := by
        show ¬ (([] : Path).head? = some i)
        intro h; cases h
      rw [dif_neg h_head_neg, Multiset.zero_add]
      have step : (fun (k' : Fin pairs'.length) =>
          if h : (([], T) :: pairs')[(Fin.succ k').val].fst.head? = some i then
            F ⟨descentIdxOf i (([], T) :: pairs') (Fin.succ k'),
                by rw [← h_len, descentToChild_length_eq]
                   exact descentIdxOf_lt i _ _ h⟩
          else (0 : Multiset β)) =
        (fun (k' : Fin pairs'.length) =>
          if h : pairs'[k'.val].fst.head? = some i then
            F ⟨descentIdxOf i pairs' k',
                by rw [← h_n_pairs', descentToChild_length_eq]
                   exact descentIdxOf_lt i _ _ h⟩
          else 0) := by
        funext k'
        have h_eq_idx : (([], T) :: pairs')[(Fin.succ k').val] = pairs'[k'.val] := rfl
        have h_eq_descent :
            descentIdxOf i (([], T) :: pairs') (Fin.succ k') = descentIdxOf i pairs' k' := by
          rw [descentIdxOf_cons_succ i ([], T) pairs' k']
          show descentIdxOf i pairs' k' +
                 (if (([] : Path).head?) = some i then 1 else 0) = _
          rw [if_neg (fun h => by cases h), Nat.add_zero]
        by_cases hh : pairs'[k'.val].fst.head? = some i
        · have hh' : (([], T) :: pairs')[(Fin.succ k').val].fst.head? = some i := by
            rw [h_eq_idx]; exact hh
          rw [dif_pos hh, dif_pos hh']
          exact congr_arg F (Fin.eq_of_val_eq h_eq_descent)
        · have hh' : ¬ ((([], T) :: pairs')[(Fin.succ k').val].fst.head? = some i) := by
            rw [h_eq_idx]; exact hh
          rw [dif_neg hh, dif_neg hh']
      rw [step]
      exact bind_descent_eq_aux i pairs' n h_n_pairs' F
    | cons j rest_p =>
      by_cases hij : i = j
      · -- Sub-case B: i = j. Head k=0 contributes F ⟨0, _⟩; tail descentIdxOf grows by 1
        -- → IH on pairs' with n - 1, F'.
        subst hij
        have h_n_pairs' : (descentToChild i pairs').length + 1 = n := by
          rw [← h_len, descentToChild_cons_consPath_eq i rest_p T pairs', List.length_cons]
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨_, h_n_pairs'.symm⟩
        have h_n_pairs'_eq : (descentToChild i pairs').length = n' := by omega
        let F' : Fin n' → Multiset β := fun k' =>
          F ⟨k'.val + 1, by show k'.val + 1 < n' + 1; omega⟩
        -- Head term k=0: dite condition is some i = some i (true).
        have h_head_pos : ((i :: rest_p, T) :: pairs')[(0 : Fin _).val].fst.head? = some i :=
          rfl
        rw [dif_pos h_head_pos]
        -- Rewrite the tail to use F' via descentIdxOf_cons_succ_consPath_eq.
        have step : (fun (k' : Fin pairs'.length) =>
            if h : ((i :: rest_p, T) :: pairs')[(Fin.succ k').val].fst.head? = some i then
              F ⟨descentIdxOf i ((i :: rest_p, T) :: pairs') (Fin.succ k'),
                  by rw [← h_len, descentToChild_length_eq]
                     exact descentIdxOf_lt i _ _ h⟩
            else (0 : Multiset β)) =
          (fun (k' : Fin pairs'.length) =>
            if h : pairs'[k'.val].fst.head? = some i then
              F' ⟨descentIdxOf i pairs' k',
                  by rw [← h_n_pairs'_eq, descentToChild_length_eq]
                     exact descentIdxOf_lt i _ _ h⟩
            else 0) := by
          funext k'
          have h_eq_idx :
              ((i :: rest_p, T) :: pairs')[(Fin.succ k').val] = pairs'[k'.val] := rfl
          have h_eq_descent :
              descentIdxOf i ((i :: rest_p, T) :: pairs') (Fin.succ k') =
                descentIdxOf i pairs' k' + 1 := by
            rw [descentIdxOf_cons_succ i (i :: rest_p, T) pairs' k']
            show descentIdxOf i pairs' k' +
                   (if some i = some i then 1 else 0) = _
            rw [if_pos rfl]
          by_cases hh : pairs'[k'.val].fst.head? = some i
          · have hh' : ((i :: rest_p, T) :: pairs')[(Fin.succ k').val].fst.head? = some i := by
              rw [h_eq_idx]; exact hh
            rw [dif_pos hh, dif_pos hh']
            show F ⟨descentIdxOf i ((i :: rest_p, T) :: pairs') (Fin.succ k'), _⟩ =
                 F ⟨descentIdxOf i pairs' k' + 1, _⟩
            congr 1
            exact Fin.eq_of_val_eq h_eq_descent
          · have hh' :
                ¬ (((i :: rest_p, T) :: pairs')[(Fin.succ k').val].fst.head? = some i) := by
              rw [h_eq_idx]; exact hh
            rw [dif_neg hh, dif_neg hh']
        rw [step]
        -- LHS now: F ⟨descentIdxOf ... ⟨0, _⟩, _⟩ + bind ... (using F').
        -- Apply IH to bring tail to bind_{k' : Fin n'} F'.
        rw [bind_descent_eq_aux i pairs' n' h_n_pairs'_eq F']
        -- RHS: decompose Fin (n' + 1) via List.finRange_succ; head = F ⟨0, _⟩.
        have hrhs : (↑(List.finRange (n' + 1)) : Multiset (Fin (n' + 1))) =
                    (0 : Fin (n' + 1)) ::ₘ
                      ((↑(List.finRange n') : Multiset (Fin n')).map Fin.succ) := by
          rw [List.finRange_succ, ← Multiset.cons_coe, ← Multiset.map_coe]
        rw [hrhs, Multiset.cons_bind, Multiset.bind_map]
        -- Closes by rfl (Lean 4 defeq with proof irrelevance):
        --  - Head: `descentIdxOf i ((i :: rest_p, T) :: pairs') ⟨0, _⟩` reduces to
        --    `descentCount i [] = 0` by computation, matching `(0 : Fin (n' + 1)).val`.
        --  - Tail: `F' k'` is defined as `F ⟨k'.val + 1, _⟩`, which is `F (Fin.succ k')`
        --    up to Fin's propositional `isLt` field (proof irrelevance).
        --  See `descentIdxOf_at_zero` for the head equation in lemma form.
        rfl
      · -- Sub-case C: i ≠ j. Head k=0 contributes 0 (head? = some j ≠ some i);
        -- tail descentIdxOf preserved → IH on pairs' with same n.
        have h_n_pairs' : (descentToChild i pairs').length = n := by
          rw [← h_len, descentToChild_cons_consPath_ne i j rest_p T pairs' hij]
        have h_head_neg :
            ¬ (((j :: rest_p, T) :: pairs')[(0 : Fin _).val].fst.head? = some i) := by
          show ¬ ((j :: rest_p : Path).head? = some i)
          show ¬ (some j = some i)
          intro heq; injection heq with heq'; exact hij heq'.symm
        rw [dif_neg h_head_neg, Multiset.zero_add]
        have step : (fun (k' : Fin pairs'.length) =>
            if h : ((j :: rest_p, T) :: pairs')[(Fin.succ k').val].fst.head? = some i then
              F ⟨descentIdxOf i ((j :: rest_p, T) :: pairs') (Fin.succ k'),
                  by rw [← h_len, descentToChild_length_eq]
                     exact descentIdxOf_lt i _ _ h⟩
            else (0 : Multiset β)) =
          (fun (k' : Fin pairs'.length) =>
            if h : pairs'[k'.val].fst.head? = some i then
              F ⟨descentIdxOf i pairs' k',
                  by rw [← h_n_pairs', descentToChild_length_eq]
                     exact descentIdxOf_lt i _ _ h⟩
            else 0) := by
          funext k'
          have h_eq_idx :
              ((j :: rest_p, T) :: pairs')[(Fin.succ k').val] = pairs'[k'.val] := rfl
          have h_eq_descent :
              descentIdxOf i ((j :: rest_p, T) :: pairs') (Fin.succ k') =
                descentIdxOf i pairs' k' := by
            rw [descentIdxOf_cons_succ i (j :: rest_p, T) pairs' k']
            show descentIdxOf i pairs' k' +
                   (if some j = some i then 1 else 0) = _
            rw [if_neg (fun h => hij (Option.some.inj h).symm), Nat.add_zero]
          by_cases hh : pairs'[k'.val].fst.head? = some i
          · have hh' : ((j :: rest_p, T) :: pairs')[(Fin.succ k').val].fst.head? = some i := by
              rw [h_eq_idx]; exact hh
            rw [dif_pos hh, dif_pos hh']
            congr 1
            exact Fin.eq_of_val_eq h_eq_descent
          · have hh' :
                ¬ (((j :: rest_p, T) :: pairs')[(Fin.succ k').val].fst.head? = some i) := by
              rw [h_eq_idx]; exact hh
            rw [dif_neg hh, dif_neg hh']
        rw [step]
        exact bind_descent_eq_aux i pairs' n h_n_pairs' F

/-! ### Indicator-singleton bind helper

Bind over `Fin n` of a value-conditional indicator (matching one specific
`j < n`) collapses to the value. Used in step 8's per-`k` validity
decomposition: when a child pair has head `j < cs.length`, exactly one
`i ∈ Fin cs.length` matches.

`[UPSTREAM]` candidate: this is the `Multiset.bind` analogue of mathlib's
`Finset.sum_ite_eq` (`Algebra/BigOperators/Group/Finset/Piecewise.lean`).
The cleaner factoring goes through two missing mathlib lemmas: a generic
`Multiset.bind_ite` (`s.bind (fun a => if p a then f a else 0)
= (s.filter p).bind f`) plus
`(List.finRange n).filter (· = ⟨j, h⟩) = [⟨j, h⟩]`. Both are real gaps. -/
private theorem bind_finRange_singleton_eq {β : Type*} :
    ∀ (n : ℕ) (g : Multiset β) (j : ℕ) (_h : j < n),
    ((↑(List.finRange n) : Multiset (Fin n)).bind fun i =>
      if j = i.val then g else (0 : Multiset β)) = g := by
  intro n
  induction n with
  | zero => intros _ _ h; omega
  | succ n' ih =>
    intro g j hj
    rw [show (↑(List.finRange (n' + 1)) : Multiset (Fin (n' + 1))) =
            (0 : Fin (n' + 1)) ::ₘ
              ((↑(List.finRange n') : Multiset (Fin n')).map Fin.succ)
        from by rw [List.finRange_succ, ← Multiset.cons_coe, ← Multiset.map_coe]]
    rw [Multiset.cons_bind, Multiset.bind_map]
    cases j with
    | zero =>
      have h_head_pos : (0 : ℕ) = (0 : Fin (n' + 1)).val := by
        simp only [Fin.val_zero]
      rw [if_pos h_head_pos]
      have step : (fun (k' : Fin n') =>
          if (0 : ℕ) = (Fin.succ k').val then g else (0 : Multiset β)) =
          (fun (_ : Fin n') => (0 : Multiset β)) := by
        funext k'
        show (if 0 = k'.val + 1 then g else 0) = 0
        rw [if_neg (by omega)]
      rw [step, Multiset.bind_zero, Multiset.add_zero]
    | succ j' =>
      have h_zero_neg : ¬ (j' + 1 = (0 : Fin (n' + 1)).val) := by
        simp only [Fin.val_zero]; omega
      rw [if_neg h_zero_neg, Multiset.zero_add]
      have step : (fun (k' : Fin n') =>
          if j' + 1 = (Fin.succ k').val then g else (0 : Multiset β)) =
          (fun (k' : Fin n') =>
          if j' = k'.val then g else (0 : Multiset β)) := by
        funext k'
        show (if j' + 1 = k'.val + 1 then g else 0) = (if j' = k'.val then g else 0)
        by_cases hk : j' = k'.val
        · rw [if_pos (by omega : j' + 1 = k'.val + 1), if_pos hk]
        · rw [if_neg (by omega : ¬ (j' + 1 = k'.val + 1)), if_neg hk]
      rw [step]
      have hj' : j' < n' := by
        have := hj
        omega
      exact ih g j' hj'


/-! ## §8.10: `stripLiftMulti` — operational inverse of `liftMulti`

The map `liftMulti pairs k` injects vertices `q ∈ vertices pairs[k].snd`
into the lifted-class image at `transport pairs pairs[k].fst ++
(posInGroup pairs k :: q)`. `stripLiftMulti` is an Option-valued
operational inverse: it returns `some q` exactly when the input path
matches that shape.

The aux walker `stripLiftMultiAux e posIG outer p` traces `e` step by
step, checking at each level that the input path's head matches the
expected `rootPrependCount`-offsetted descent index. Recursion is
structural on `e`.

Original consumer was the deprecated `composePairs` partition theorem
(deleted 2026-06-12 with the A3.3 route); kept as generic vertex
bookkeeping substrate. -/

/-- Auxiliary walker: structural recursion on the prefix path. -/
def stripLiftMultiAux : Path → ℕ → List (Path × RoseTree α) → Path → Option Path
  | [], _, _, [] => none
  | [], posIG, _, h :: q => if h = posIG then some q else none
  | _ :: _, _, _, [] => none
  | i :: rest, posIG, outer, h :: q =>
      if h = i + rootPrependCount outer then
        stripLiftMultiAux rest posIG (descentToChild i outer) q
      else none

/-- Operational inverse of `liftMulti`: `stripLiftMulti pairs k p = some q`
    iff `p = liftMulti pairs k q`. Computable. -/
def stripLiftMulti (pairs : List (Path × RoseTree α)) (k : Fin pairs.length)
    (p : Path) : Option Path :=
  stripLiftMultiAux pairs[k.val].fst (posInGroup pairs k) pairs p

/-- **Characterization of `stripLiftMultiAux`**: it returns `some q` exactly
    when the input path equals `transport outer e ++ (posIG :: q)`.
    Proof by structural induction on `e`. -/
theorem stripLiftMultiAux_eq_some_iff
    (e : Path) (posIG : ℕ) (outer : List (Path × RoseTree α)) (p q : Path) :
    stripLiftMultiAux e posIG outer p = some q ↔
      p = transport outer e ++ (posIG :: q) := by
  induction e generalizing outer p with
  | nil =>
    rw [transport_nil_path, List.nil_append]
    cases p with
    | nil => simp [stripLiftMultiAux]
    | cons h q' =>
      show (if h = posIG then some q' else none) = some q ↔
           (h :: q' : Path) = posIG :: q
      by_cases hh : h = posIG
      · rw [if_pos hh, hh]; simp
      · rw [if_neg hh]; simp [hh]
  | cons i rest ih =>
    rw [transport_cons_path]
    cases p with
    | nil => simp [stripLiftMultiAux]
    | cons h q' =>
      show (if h = i + rootPrependCount outer then
              stripLiftMultiAux rest posIG (descentToChild i outer) q'
            else none) = some q ↔
        (h :: q' : Path) = (i + rootPrependCount outer) ::
          (transport (descentToChild i outer) rest ++ (posIG :: q))
      by_cases hh : h = i + rootPrependCount outer
      · rw [if_pos hh, ih (descentToChild i outer) q']
        constructor
        · intro hq'; rw [hq', hh]
        · intro hcons; injection hcons
      · rw [if_neg hh]
        constructor
        · intro hf; exact absurd hf (by simp)
        · intro hcons; injection hcons with hhd _; exact (hh hhd).elim

/-- **Iff-characterization**: `stripLiftMulti pairs k p = some q` exactly
    when `p` is the lifted image of `q` under `liftMulti pairs k`. -/
theorem stripLiftMulti_eq_some_iff (pairs : List (Path × RoseTree α))
    (k : Fin pairs.length) (p q : Path) :
    stripLiftMulti pairs k p = some q ↔ p = liftMulti pairs k q := by
  unfold stripLiftMulti liftMulti
  exact stripLiftMultiAux_eq_some_iff pairs[k.val].fst (posInGroup pairs k) pairs p q

/-- **Correctness**: stripping a lifted vertex recovers the original. -/
theorem stripLiftMulti_liftMulti (pairs : List (Path × RoseTree α))
    (k : Fin pairs.length) (q : Path) :
    stripLiftMulti pairs k (liftMulti pairs k q) = some q := by
  rw [stripLiftMulti_eq_some_iff]

/-! ## §8.11: `untransport` — operational inverse of `transport`

`transport pairs v` computes the path of `v ∈ vertices T` in `multiGraft T pairs`.
`untransport pairs p` returns `some v` if `p = transport pairs v` for some `v`,
else `none`. Used in §11.5 `rootInner` to recover T-coordinate paths from
preserved/sourceSelf inner vertices. -/

/-- Recursive Option-valued inverse of `transport`: strips the
    `rootPrependCount`-offset at each level, recursing into descended pairs. -/
def untransport : List (Path × RoseTree α) → Path → Option Path
  | _, [] => some []
  | outer, h :: q =>
      if h ≥ rootPrependCount outer then
        (untransport (descentToChild (h - rootPrependCount outer) outer) q).map
          ((h - rootPrependCount outer) :: ·)
      else none

@[simp] theorem untransport_nil (outer : List (Path × RoseTree α)) :
    untransport outer [] = some [] := rfl

/-- **Iff-characterization**: `untransport outer p = some v` iff
    `p = transport outer v`. Proof by structural induction on `p`. -/
theorem untransport_eq_some_iff
    (outer : List (Path × RoseTree α)) (p v : Path) :
    untransport outer p = some v ↔ p = transport outer v := by
  induction p generalizing outer v with
  | nil =>
    cases v with
    | nil => simp
    | cons i rest =>
      rw [transport_cons_path]
      show some ([] : Path) = some (i :: rest) ↔ ([] : Path) = _ :: _
      simp
  | cons h q ih =>
    show (if h ≥ rootPrependCount outer then
            (untransport (descentToChild (h - rootPrependCount outer) outer) q).map
              ((h - rootPrependCount outer) :: ·)
          else none) = some v ↔ (h :: q : Path) = transport outer v
    by_cases h_ge : h ≥ rootPrependCount outer
    · rw [if_pos h_ge, Option.map_eq_some_iff]
      constructor
      · rintro ⟨a, hut, ha⟩
        subst ha
        rw [transport_cons_path]
        rw [← (ih _ _).mp hut]
        congr 1; omega
      · intro hcons
        cases v with
        | nil => rw [transport_nil_path] at hcons; simp at hcons
        | cons i rest =>
          rw [transport_cons_path] at hcons
          injection hcons with hhd htail
          refine ⟨rest, ?_, ?_⟩
          · have h_i : i = h - rootPrependCount outer := by omega
            rw [(ih _ _).mpr]
            rw [← h_i]; exact htail
          · have h_i : h - rootPrependCount outer = i := by omega
            rw [h_i]
    · rw [if_neg h_ge]
      cases v with
      | nil => rw [transport_nil_path]; simp
      | cons i rest =>
        rw [transport_cons_path]
        constructor
        · intro hf; exact absurd hf (by simp)
        · intro hcons
          injection hcons with hhd _
          have : h = i + rootPrependCount outer := hhd
          omega

/-- **Correctness**: untransporting a transported vertex recovers the original. -/
theorem untransport_transport (outer : List (Path × RoseTree α)) (v : Path) :
    untransport outer (transport outer v) = some v := by
  rw [untransport_eq_some_iff]

/-! ## §9: The decomposition theorem

The 3-class decomposition statement. Proof is the headline of A3.0
phase 2.

The substrate identities (§8.5–§8.8) are sorry-free. The singleton
corollaries (§10) follow as direct consequences. -/

/-- **Multi-pair decomposition lemma**. Under the validity hypothesis
    that every pair's source is a valid path in `T`, the vertex multiset
    of `multiGraft T pairs` partitions into:

    1. **preserved**: `(vertices T).filterMap (preserveMulti pairs)` —
       non-source T-vertices, each transported.
    2. **sourceSelf**: source vertices of `T` (those whose path is in
       `pairSources pairs`), each transported.
    3. **lifted**: for each pair `k` and each `q ∈ vertices (pairs[k].snd)`,
       the path `liftMulti pairs k q`.

    Specializes to `vertices_insertAt_decomp` for single-pair lists
    (corollary in §10). -/
theorem vertices_multiGraft_decomp :
    ∀ (T : RoseTree α) (pairs : List (Path × RoseTree α))
      (_h_valid : ∀ pair ∈ pairs, IsValidPath pair.fst T),
    ((vertices (multiGraft T pairs) : List Path) : Multiset Path) =
      ((vertices T : Multiset Path).filterMap (preserveMulti pairs))
      + (((vertices T : Multiset Path).filter (· ∈ pairSources pairs)).map
          (transport pairs))
      + ((Multiset.ofList (List.finRange pairs.length)).bind
          (fun k => (vertices (pairs[k].snd) : Multiset Path).map
            (liftMulti pairs k)))
  | .node a cs, pairs, h_valid => by
    set N := rootPrependCount pairs with hN_def
    -- Step 1: unfold LHS structurally.
    rw [multiGraft_node, vertices_node, verticesAux_append,
        length_filterMap_rootPrependFilter]
    rw [show (([] : Path) ::
              ((verticesAux 0 (pairs.filterMap rootPrependFilter)) ++
               (verticesAux (0 + N) (multiGraftChildren cs pairs))) : List Path) =
            ([([] : Path)] ++ verticesAux 0 (pairs.filterMap rootPrependFilter) ++
              verticesAux (0 + N) (multiGraftChildren cs pairs)) from rfl,
        ← Multiset.coe_add, ← Multiset.coe_add]
    -- Step 2: apply companion to the children block.
    rw [show (0 + N : ℕ) = N from by omega,
        verticesAux_multiGraftChildren_unfold cs pairs N]
    -- Step 3: derive per-child validity via substrate lemma, then apply IH inside bind.
    have h_valid_child : ∀ (i : Fin cs.length),
        ∀ pair ∈ descentToChild i.val pairs, IsValidPath pair.fst cs[i.val] :=
      descentToChild_valid_of_node a cs pairs h_valid
    -- Apply IH per-child via Multiset.bind_congr. Each i ∈ Fin cs.length yields
    -- the 3-class decomposition for cs[i.val] with descended pairs.
    have ih_per_child : ∀ (i : Fin cs.length),
        ((vertices (multiGraft cs[i.val] (descentToChild i.val pairs)) : List Path) :
          Multiset Path) =
        ((vertices cs[i.val] : Multiset Path).filterMap
            (preserveMulti (descentToChild i.val pairs)))
        + (((vertices cs[i.val] : Multiset Path).filter
              (· ∈ pairSources (descentToChild i.val pairs))).map
            (transport (descentToChild i.val pairs)))
        + ((Multiset.ofList (List.finRange (descentToChild i.val pairs).length)).bind
            (fun k' => (vertices ((descentToChild i.val pairs)[k'.val].snd) :
              Multiset Path).map (liftMulti (descentToChild i.val pairs) k'))) :=
      fun i => vertices_multiGraft_decomp cs[i.val]
                 (descentToChild i.val pairs) (h_valid_child i)
    -- Step 4: apply ih_per_child inside the bind, distributing .map over the 3-class sum.
    simp_rw [ih_per_child, Multiset.map_add]
    -- Step 5: distribute bind over the 3-class sum into 3 separate binds.
    rw [Multiset.bind_add, Multiset.bind_add]
    -- Unfold N to enable rewrites with helpers that mention rootPrependCount pairs.
    simp only [hN_def]
    -- Step 6: bridge per-child preserved bind to (verticesAux 0 cs).filterMap (preserveMulti pairs).
    -- Push .map inside filterMap, apply preserveMulti_cons_post_map, fold via filterMap_map +
    -- filterMap_bind + verticesAux_unfold.
    have step6 : ((↑(List.finRange cs.length) : Multiset (Fin cs.length)).bind fun i =>
            Multiset.map (fun x => (rootPrependCount pairs + i.val) :: x)
              (Multiset.filterMap (preserveMulti (descentToChild i.val pairs))
                (↑(vertices cs[i.val]) : Multiset Path))) =
        Multiset.filterMap (preserveMulti pairs)
          (↑(verticesAux 0 cs) : Multiset Path) := by
      -- Push .map inside filterMap via Multiset.map_filterMap.
      simp_rw [Multiset.map_filterMap, preserveMulti_cons_post_map]
      -- Now: bind_i (filterMap (fun f => preserveMulti pairs (i :: f)) ↑(vertices cs[i.val])).
      -- Convert filterMap (fun f => g (h f)) to filterMap g ∘ map h via Multiset.filterMap_map.
      rw [show (fun (i : Fin cs.length) =>
              Multiset.filterMap (fun f => preserveMulti pairs (i.val :: f))
                (↑(vertices cs[i.val]) : Multiset Path)) =
            (fun (i : Fin cs.length) =>
              Multiset.filterMap (preserveMulti pairs)
                (Multiset.map (i.val :: ·) (↑(vertices cs[i.val]) : Multiset Path)))
          from by funext i; rw [Multiset.filterMap_map]; rfl]
      -- Pull filterMap out of bind via Multiset.filterMap_bind.
      rw [← Multiset.filterMap_bind]
      -- Inner bind = ↑(verticesAux 0 cs) by verticesAux_unfold.
      congr 1
      rw [verticesAux_unfold cs 0]
      refine Multiset.bind_congr fun i _ => ?_
      rw [show (0 + i.val : ℕ) = i.val from by omega]
    rw [step6]
    -- Step 7: bridge per-child sourceSelf bind to (filter (· ∈ pairSources pairs) ↑(verticesAux 0 cs)).map (transport pairs).
    -- Compose .map's via Multiset.map_map, apply transport_cons_descent pointwise,
    -- rewrite filter via descent_pairSources_iff, then fold via map_bind + filter_bind +
    -- verticesAux_unfold.
    have step7 : ((↑(List.finRange cs.length) : Multiset (Fin cs.length)).bind fun i =>
            Multiset.map (fun x => (rootPrependCount pairs + i.val) :: x)
              (Multiset.map (transport (descentToChild i.val pairs))
                (Multiset.filter (fun x => x ∈ pairSources (descentToChild i.val pairs))
                  (↑(vertices cs[i.val]) : Multiset Path)))) =
        Multiset.map (transport pairs)
          (Multiset.filter (fun x => x ∈ pairSources pairs)
            (↑(verticesAux 0 cs) : Multiset Path)) := by
      -- Compose the two outer .map's via Multiset.map_map.
      simp_rw [Multiset.map_map]
      -- Pointwise: (fun x => (N + ↑i) :: ·) ∘ transport (desc ↑i pairs) = transport pairs ∘ (↑i :: ·).
      rw [show (fun (i : Fin cs.length) =>
              Multiset.map ((fun x : Path => (rootPrependCount pairs + i.val) :: x) ∘
                              transport (descentToChild i.val pairs))
                (Multiset.filter (fun x => x ∈ pairSources (descentToChild i.val pairs))
                  (↑(vertices cs[i.val]) : Multiset Path))) =
            (fun (i : Fin cs.length) =>
              Multiset.map (transport pairs ∘ (i.val :: ·))
                (Multiset.filter (fun x => x ∈ pairSources (descentToChild i.val pairs))
                  (↑(vertices cs[i.val]) : Multiset Path)))
          from by
            funext i
            congr 1
            funext y
            exact transport_cons_descent pairs i.val y]
      -- Filter rewrite via descent_pairSources_iff.
      rw [show (fun (i : Fin cs.length) =>
              Multiset.map (transport pairs ∘ (i.val :: ·))
                (Multiset.filter (fun x => x ∈ pairSources (descentToChild i.val pairs))
                  (↑(vertices cs[i.val]) : Multiset Path))) =
            (fun (i : Fin cs.length) =>
              Multiset.map (transport pairs ∘ (i.val :: ·))
                (Multiset.filter (fun x => (i.val :: x) ∈ pairSources pairs)
                  (↑(vertices cs[i.val]) : Multiset Path)))
          from by
            funext i
            congr 1
            refine Multiset.filter_congr fun x _ => ?_
            exact descent_pairSources_iff i.val x pairs]
      -- Pull .map of (i.val :: ·) out of filter via Multiset.filter_map (reversed).
      rw [show (fun (i : Fin cs.length) =>
              Multiset.map (transport pairs ∘ (i.val :: ·))
                (Multiset.filter (fun x => (i.val :: x) ∈ pairSources pairs)
                  (↑(vertices cs[i.val]) : Multiset Path))) =
            (fun (i : Fin cs.length) =>
              Multiset.map (transport pairs)
                (Multiset.filter (fun x => x ∈ pairSources pairs)
                  (Multiset.map (i.val :: ·) (↑(vertices cs[i.val]) : Multiset Path))))
          from by
            funext i
            rw [← Multiset.map_map, Multiset.filter_map]
            rfl]
      -- Pull `map (transport pairs)` out of bind via Multiset.map_bind (reversed).
      rw [← Multiset.map_bind]
      congr 1
      -- Pull `filter (· ∈ pairSources pairs)` out of bind via Multiset.filter_bind (reversed).
      rw [← Multiset.filter_bind]
      congr 1
      -- Inner bind = ↑(verticesAux 0 cs) by verticesAux_unfold.
      rw [verticesAux_unfold cs 0]
      refine Multiset.bind_congr fun i _ => ?_
      rw [show (0 + i.val : ℕ) = i.val from by omega]
    rw [step7]
    -- Step 9 (combine [] vertex first): the preserved + sourceSelf classes evaluated at
    -- vertices T = [] :: verticesAux 0 cs decompose as the verticesAux versions plus
    -- ↑[[]]. The [] vertex contributes either to preserved (if [] ∉ sources) or to
    -- sourceSelf (if [] ∈ sources), but never both.
    have hcoe_singleton : (↑([[]] : List Path) : Multiset Path) =
        ({([] : Path)} : Multiset Path) := rfl
    have step9 : Multiset.filterMap (preserveMulti pairs)
                    (↑(vertices (RoseTree.node a cs)) : Multiset Path)
                  + Multiset.map (transport pairs)
                      (Multiset.filter (fun x => x ∈ pairSources pairs)
                        (↑(vertices (RoseTree.node a cs)) : Multiset Path)) =
        (↑([[]] : List Path) : Multiset Path)
        + Multiset.filterMap (preserveMulti pairs)
            (↑(verticesAux 0 cs) : Multiset Path)
        + Multiset.map (transport pairs)
            (Multiset.filter (fun x => x ∈ pairSources pairs)
              (↑(verticesAux 0 cs) : Multiset Path)) := by
      rw [vertices_node]
      rw [show (↑(([] : Path) :: verticesAux 0 cs) : Multiset Path) =
              (([] : Path) ::ₘ (↑(verticesAux 0 cs) : Multiset Path))
          from by rw [← Multiset.cons_coe]]
      rw [Multiset.filterMap_cons, Multiset.filter_cons, hcoe_singleton]
      by_cases h : ([] : Path) ∈ pairSources pairs
      · -- preserveMulti pairs [] = none → preserved gets 0
        -- [] ∈ sources → sourceSelf cons gets [], mapped via transport pairs [] = []
        have hpm : preserveMulti pairs ([] : Path) = none := by
          unfold preserveMulti; simp [h]
        rw [hpm, if_pos h]
        simp only [Option.map_none, Option.getD_none, Multiset.zero_add,
                   Multiset.map_add, Multiset.map_singleton,
                   show transport pairs ([] : Path) = [] from rfl]
        abel
      · -- preserveMulti pairs [] = some [] → preserved cons gets []
        -- [] ∉ sources → sourceSelf unaffected
        have hpm : preserveMulti pairs ([] : Path) = some [] := by
          unfold preserveMulti
          rw [if_neg h]
          rfl
        rw [hpm, if_neg h]
        simp only [Option.map_some, Option.getD_some]
        abel
    -- Now use step9 to align preserved + sourceSelf parts of LHS and RHS.
    -- After step9 substitution, both sides differ only in the lifted parts.
    rw [step9]
    -- Step 8: lifted bridge — the (i, k') ↔ k bijection.
    -- Both sides enumerate `Σ k ∈ Fin pairs.length, q ∈ vertices pairs[k].snd`,
    -- organized differently. Bijection: each k corresponds to one of:
    --   (a) `pairs[k].fst = []`: rootPrepends m-th, where m = posInGroup pairs k.
    --   (b) `pairs[k].fst = i :: rest` (i < cs.length by validity): descent
    --       (i, k') in i-bucket, where k' = descentIdxOf i pairs k.
    -- See §8.7 (`posInGroup_descent_invariance`,
    -- `descentToChild_getElem_at_descentIdxOf`) for the substrate.
    have step8 : (↑(verticesAux 0 (List.filterMap rootPrependFilter pairs))
                    : Multiset Path)
                + ((↑(List.finRange cs.length) : Multiset (Fin cs.length)).bind fun i =>
                    Multiset.map (fun x => (rootPrependCount pairs + i.val) :: x)
                      ((↑(List.finRange (descentToChild i.val pairs).length)
                          : Multiset (Fin (descentToChild i.val pairs).length)).bind fun k' =>
                        Multiset.map (liftMulti (descentToChild i.val pairs) k')
                          (↑(vertices (descentToChild i.val pairs)[k'.val].snd) :
                            Multiset Path))) =
        ((↑(List.finRange pairs.length) : Multiset (Fin pairs.length)).bind fun k =>
          Multiset.map (liftMulti pairs k) (↑(vertices pairs[k].snd) : Multiset Path)) := by
      -- Step A: each per-i LHS contribution is a bind over k filtered by
      -- `pairs[k.val].fst.head? = some i.val`. This uses Multiset.map_bind to
      -- pull `(N + i.val) :: ·` inside, then bind_descent_eq_aux to translate
      -- the inner k'-bind to a conditional k-bind, then liftMulti_at_child_descent
      -- + descentToChild_getElem_at_descentIdxOf to simplify the pos branch.
      have h_per_i : ∀ (i : Fin cs.length),
          Multiset.map (fun x => (rootPrependCount pairs + i.val) :: x)
            ((↑(List.finRange (descentToChild i.val pairs).length) :
              Multiset (Fin (descentToChild i.val pairs).length)).bind fun k' =>
              Multiset.map (liftMulti (descentToChild i.val pairs) k')
                (↑(vertices (descentToChild i.val pairs)[k'.val].snd) : Multiset Path)) =
          ((↑(List.finRange pairs.length) : Multiset (Fin pairs.length)).bind fun k =>
            if pairs[k.val].fst.head? = some i.val then
              Multiset.map (liftMulti pairs k) (↑(vertices pairs[k.val].snd) : Multiset Path)
            else 0) := by
        intro i
        -- A.1. Push (N + i.val) :: · inside via Multiset.map_bind, compose maps.
        simp_rw [Multiset.map_bind, Multiset.map_map]
        -- A.3. Apply bind_descent_eq_aux (reverse).
        rw [(bind_descent_eq_aux i.val pairs (descentToChild i.val pairs).length rfl
              (fun k' => Multiset.map (((rootPrependCount pairs + i.val) :: ·) ∘
                            (liftMulti (descentToChild i.val pairs) k'))
                  (↑(vertices (descentToChild i.val pairs)[k'.val].snd) : Multiset Path))).symm]
        -- A.4. Per-k: simplify pos branch.
        refine Multiset.bind_congr fun k _ => ?_
        by_cases h : pairs[k.val].fst.head? = some i.val
        · rw [dif_pos h, if_pos h]
          -- Extract pairs[k.val].fst = i.val :: rest.
          obtain ⟨rest, h_eq⟩ : ∃ rest, pairs[k.val].fst = i.val :: rest := by
            generalize hp : pairs[k.val].fst = p at h ⊢
            cases p with
            | nil =>
              simp only [List.head?_nil] at h
              cases h
            | cons j rest =>
              simp only [List.head?_cons, Option.some.injEq] at h
              subst h
              exact ⟨rest, rfl⟩
          -- Pos branch:
          -- Multiset.map (((N + i.val) :: ·) ∘ liftMulti (desc i.val pairs)
          --                ⟨descentIdxOf i.val pairs k, _⟩)
          --   ↑(vertices (desc i.val pairs)[descentIdxOf i.val pairs k]'_).snd
          -- = Multiset.map (liftMulti pairs k) ↑(vertices pairs[k.val].snd)
          have h_getElem :=
            descentToChild_getElem_at_descentIdxOf i.val pairs k rest h_eq
          -- The vertex source matches:
          --   (desc i.val pairs)[descentIdxOf i.val pairs k]'_.snd = pairs[k.val].snd
          have h_snd : ((descentToChild i.val pairs)[descentIdxOf i.val pairs k]'(by
              rw [descentToChild_length_eq]
              exact descentIdxOf_lt _ _ _ h)).snd = pairs[k.val].snd := by
            rw [h_getElem]
          -- The mapping function matches pointwise:
          have h_fun : ∀ q, (((rootPrependCount pairs + i.val) :: ·) ∘
                              liftMulti (descentToChild i.val pairs)
                                ⟨descentIdxOf i.val pairs k, by
                                  rw [descentToChild_length_eq]
                                  exact descentIdxOf_lt _ _ _ h⟩) q
                            = liftMulti pairs k q := by
            intro q
            exact (liftMulti_at_child_descent pairs k i.val rest h_eq q).symm
          -- Combine via Multiset.map_congr.
          refine Multiset.map_congr ?_ (fun q _ => h_fun q)
          rw [h_snd]
        · rw [dif_neg h, if_neg h]
      -- Apply Step A.
      simp_rw [h_per_i]
      -- Step B: swap binds via Multiset.bind_bind.
      rw [Multiset.bind_bind]
      -- Step C: convert ↑(verticesAux 0 rootPrepends) via root_bind_eq + liftMulti_at_root.
      rw [show (↑(verticesAux 0 (List.filterMap rootPrependFilter pairs)) : Multiset Path) =
            ((↑(List.finRange pairs.length) : Multiset (Fin pairs.length)).bind fun k =>
              if pairs[k.val].fst = [] then
                Multiset.map (liftMulti pairs k) (↑(vertices pairs[k.val].snd) : Multiset Path)
              else 0)
          from by
            rw [← root_bind_eq pairs 0]
            refine Multiset.bind_congr fun k _ => ?_
            by_cases h : pairs[k.val].fst = []
            · rw [if_pos h, if_pos h]
              refine Multiset.map_congr rfl fun q _ => ?_
              rw [Nat.zero_add]
              exact (liftMulti_at_root pairs k h q).symm
            · rw [if_neg h, if_neg h]]
      -- Step D: combine via Multiset.bind_add^-1.
      rw [← Multiset.bind_add]
      -- Step E: per-k decomposition.
      refine Multiset.bind_congr fun k _ => ?_
      by_cases h_root : pairs[k.val].fst = []
      · -- Root k: first term = fk(k); inner bind = 0.
        rw [if_pos h_root]
        have h_zero : ((↑(List.finRange cs.length) : Multiset (Fin cs.length)).bind fun i =>
            if pairs[k.val].fst.head? = some i.val then
              Multiset.map (liftMulti pairs k) (↑(vertices pairs[k.val].snd) : Multiset Path)
            else 0) = 0 := by
          have step : (fun (i : Fin cs.length) =>
              if pairs[k.val].fst.head? = some i.val then
                Multiset.map (liftMulti pairs k) (↑(vertices pairs[k.val].snd) : Multiset Path)
              else (0 : Multiset Path)) = (fun _ => 0) := by
            funext i
            rw [h_root]
            rw [if_neg (fun h => by cases h)]
          rw [step, Multiset.bind_zero]
        rw [h_zero, Multiset.add_zero]
        -- Bridge `pairs[k.val]` (Nat-indexed; from h_per_i / bind_descent_eq_aux body)
        -- to `pairs[k]` (Fin-indexed; from the original step 8 statement).
        simp only [Fin.getElem_fin]
      · -- Child k: first term = 0; inner bind picks out unique i.
        rw [if_neg h_root, Multiset.zero_add]
        obtain ⟨j, rest, h_eq⟩ : ∃ j rest, pairs[k.val].fst = j :: rest := by
          cases h_path : pairs[k.val].fst with
          | nil => exact absurd h_path h_root
          | cons j rest => exact ⟨j, rest, rfl⟩
        have h_j_lt : j < cs.length := by
          have h_valid_pair := h_valid pairs[k.val] (List.getElem_mem _)
          rw [h_eq, isValidPath_cons] at h_valid_pair
          exact h_valid_pair.fst
        -- Rewrite predicate: pairs[k].fst.head? = some i.val ↔ j = i.val.
        have step : (fun (i : Fin cs.length) =>
            if pairs[k.val].fst.head? = some i.val then
              Multiset.map (liftMulti pairs k) (↑(vertices pairs[k.val].snd) : Multiset Path)
            else (0 : Multiset Path)) =
          (fun (i : Fin cs.length) =>
            if j = i.val then
              Multiset.map (liftMulti pairs k) (↑(vertices pairs[k.val].snd) : Multiset Path)
            else 0) := by
          funext i
          rw [h_eq]
          show (if some j = some i.val then _ else _) = (if j = i.val then _ else _)
          by_cases hi : j = i.val
          · rw [if_pos (by rw [hi]), if_pos hi]
          · rw [if_neg (by intro heq; injection heq with heq'; exact hi heq'), if_neg hi]
        rw [step]
        exact bind_finRange_singleton_eq cs.length
          (Multiset.map (liftMulti pairs k) (↑(vertices pairs[k.val].snd) : Multiset Path))
          j h_j_lt
    -- Substitute liftedClass via step 8 (reverse), then close by abel.
    rw [← step8]
    abel
termination_by T _ _ => T.numNodes
decreasing_by exact numNodes_lt_of_getElem i.isLt

/-! ## §9.5: Corollary — `transport pairs v_T ∈ vertices (multiGraft T pairs)`

Direct consequence of `vertices_multiGraft_decomp` + the §7.5 identity that
the preserved + sourceSelf classes equal `vertices T` mapped under
`transport pairs`. Consumed by A3.3 substrate `multiGraft_compose_cons_pair_at_choice`
to discharge the `v_c ∈ vertices T'` hypothesis when `v_c` is a transported
T-vertex. -/

/-- For any vertex `v_T ∈ vertices T`, the transported path `transport pairs v_T`
    is a vertex of `multiGraft T pairs`. -/
theorem transport_mem_vertices_multiGraft
    (T : RoseTree α) (pairs : List (Path × RoseTree α))
    (h_valid : ∀ pair ∈ pairs, IsValidPath pair.fst T)
    (v_T : Path) (h_v_T : v_T ∈ vertices T) :
    transport pairs v_T ∈ vertices (multiGraft T pairs) := by
  have h_mem_map :
      transport pairs v_T ∈ ((vertices T : Multiset Path).map (transport pairs)) :=
    Multiset.mem_map.mpr ⟨v_T, h_v_T, rfl⟩
  rw [← preserved_add_sourceSelf_eq_vertices_map_transport pairs
        ((vertices T : List Path) : Multiset Path)] at h_mem_map
  rw [← Multiset.mem_coe, vertices_multiGraft_decomp T pairs h_valid]
  exact Multiset.mem_add.mpr (Or.inl h_mem_map)

/-! ## §10: Single-pair specialization corollaries

When `pairs = [(e, T₂)]`, the multi-pair decomposition reduces to
`vertices_insertAt_decomp`. Validates the API shape against the existing
substrate. -/

/-- Singleton transport on the source itself: `transport [(e, T₂)] e = e`.
    The source path is at every level shifted by `0` (the only pair
    contributes to descent, never to root-prepends, except at the end
    where it's an empty descent). -/
theorem transport_singleton_self : ∀ (e : Path) (T₂ : RoseTree α),
    transport [(e, T₂)] e = e
  | [], _ => rfl
  | i :: rest, T₂ => by
    show (i + rootPrependCount [(i :: rest, T₂)]) ::
         transport (descentToChild i [(i :: rest, T₂)]) rest = i :: rest
    rw [rootPrependCount_cons_consPath, rootPrependCount_nil, Nat.add_zero,
        descentToChild_cons_consPath_eq i rest T₂ [],
        descentToChild_nil,
        transport_singleton_self rest T₂]

/-- Single-pair `transport` agrees with `preserveOf` for `f ≠ e`. The
    diagonal is captured by `preserveMulti = preserve?` (see
    `preserveMulti_singleton`). -/
theorem transport_singleton_of_ne : ∀ (e : Path) (T₂ : RoseTree α) (f : Path)
    (_hne : f ≠ e), transport [(e, T₂)] f = preserveOf e f
  | [],            _,   [],            h => absurd rfl h.symm
  | [],            T₂,  j :: rest_f,   _ => by
    show (j + rootPrependCount [(([] : Path), T₂)]) ::
         transport (descentToChild j [(([] : Path), T₂)]) rest_f =
         preserveOf [] (j :: rest_f)
    rw [rootPrependCount_cons_nilPath, rootPrependCount_nil,
        descentToChild_cons_nilPath, descentToChild_nil,
        transport_empty_pairs, preserveOf_nil_cons]
  | _ :: _,        _,   [],            _ => rfl
  | i :: rest_e,   T₂,  j :: rest_f,   h => by
    by_cases hij : i = j
    · -- `subst hij` substitutes the newer var, here `j := i`.
      subst hij
      have hrest_ne : rest_f ≠ rest_e := fun heq => h (by rw [heq])
      show (i + rootPrependCount [(i :: rest_e, T₂)]) ::
           transport (descentToChild i [(i :: rest_e, T₂)]) rest_f =
           preserveOf (i :: rest_e) (i :: rest_f)
      rw [rootPrependCount_cons_consPath, rootPrependCount_nil, Nat.add_zero,
          descentToChild_cons_consPath_eq i rest_e T₂ [],
          descentToChild_nil,
          transport_singleton_of_ne rest_e T₂ rest_f hrest_ne,
          preserveOf_cons_cons, if_pos rfl]
    · show (j + rootPrependCount [(i :: rest_e, T₂)]) ::
           transport (descentToChild j [(i :: rest_e, T₂)]) rest_f =
           preserveOf (i :: rest_e) (j :: rest_f)
      rw [rootPrependCount_cons_consPath, rootPrependCount_nil, Nat.add_zero,
          descentToChild_cons_consPath_ne j i rest_e T₂ [] (Ne.symm hij),
          descentToChild_nil,
          transport_empty_pairs,
          preserveOf_cons_cons, if_neg hij]

/-- `preserveMulti [(e, T₂)] = preserve? e`. Combines
    `transport_singleton_of_ne` (off-diagonal) with `preserve?_self`
    (diagonal). -/
theorem preserveMulti_singleton (e : Path) (T₂ : RoseTree α) (f : Path) :
    preserveMulti [(e, T₂)] f = preserve? e f := by
  show (if f ∈ pairSources [(e, T₂)] then none else some (transport [(e, T₂)] f))
       = preserve? e f
  rw [show pairSources [(e, T₂)] = [e] from rfl]
  by_cases h : f = e
  · subst h
    rw [if_pos (List.mem_singleton.mpr rfl), preserve?_self]
  · rw [if_neg (fun hmem => h (List.mem_singleton.mp hmem)),
        preserve?_of_ne e f h, transport_singleton_of_ne e T₂ f h]

/-- `liftMulti [(e, T₂)] ⟨0, _⟩ q = lift e q`. The single pair's
    `posInGroup` is `0` (no earlier same-source pairs) and its
    `transport`ed source is `e` itself (`transport_singleton_self`). -/
theorem liftMulti_singleton (e : Path) (T₂ : RoseTree α) (q : Path) :
    liftMulti [(e, T₂)] ⟨0, by simp⟩ q = lift e q := by
  show transport [(e, T₂)] (([(e, T₂)] : List _)[0]'(by simp)).fst ++
       (posInGroup [(e, T₂)] ⟨0, by simp⟩ :: q) = e ++ 0 :: q
  rw [show (([(e, T₂)] : List (Path × RoseTree α))[0]'(by simp)).fst = e from rfl,
      transport_singleton_self e T₂,
      show posInGroup [(e, T₂)] ⟨0, by simp⟩ = 0 from by
        unfold posInGroup; simp]

/-! ## §10.5: Forest-aux companion to `vertices_multiGraft_decomp`

The forest-aux companion gives the per-child 3-class decomposition of
`verticesAux N (multiGraftChildren cs pairs)`. Composes
`verticesAux_multiGraftChildren_unfold` (per-child unfolding via
`descentToChild`) with `vertices_multiGraft_decomp` (per-tree 3-class
decomposition).

This is Phase 3.1 substrate for the A3.3 cons-case proof
(`scratch/a33_cons_plan.md`). Consumers (Phase 4) further distribute the
`.map ((offset + i.val) :: ·)` over the 3-class sum at the use site. -/

/-- Forest-aux companion to `vertices_multiGraft_decomp`. The vertices of
    `verticesAux offset (multiGraftChildren cs pairs)` decompose, per-child
    `i`, into the same 3-class sum as for a single tree (preserved /
    sourceSelf / lifted), with the per-child paths prepended by
    `(offset + i.val)`. The validity hypothesis is supplied per-child via
    `descentToChild`. -/
theorem verticesAux_multiGraftChildren_decomp
    (cs : List (RoseTree α)) (pairs : List (Path × RoseTree α))
    (h_valid_per_child : ∀ (i : Fin cs.length),
        ∀ pair ∈ descentToChild i.val pairs, IsValidPath pair.fst cs[i.val])
    (offset : ℕ) :
    ((verticesAux offset (multiGraftChildren cs pairs) : List Path) :
        Multiset Path) =
      (Multiset.ofList (List.finRange cs.length)).bind fun i =>
        (((vertices cs[i.val] : Multiset Path).filterMap
              (preserveMulti (descentToChild i.val pairs)))
          + (((vertices cs[i.val] : Multiset Path).filter
                (· ∈ pairSources (descentToChild i.val pairs))).map
              (transport (descentToChild i.val pairs)))
          + ((Multiset.ofList (List.finRange (descentToChild i.val pairs).length)).bind
              (fun k => (vertices ((descentToChild i.val pairs)[k.val].snd) :
                Multiset Path).map (liftMulti (descentToChild i.val pairs) k)))
        ).map ((offset + i.val) :: ·) := by
  rw [verticesAux_multiGraftChildren_unfold]
  refine Multiset.bind_congr fun i _ => ?_
  congr 1
  exact vertices_multiGraft_decomp cs[i.val]
          (descentToChild i.val pairs) (h_valid_per_child i)

/-- Helper: `verticesAux` of a `(List.finRange n).map f` forest unfolds as a
    bind over `Fin n` directly, with the per-i body being `vertices (f i)`
    prepended by `(offset + i.val)`. Proof by induction on `n`, with the
    `n+1` case unfolding `List.finRange_succ` and shifting the offset. -/
private theorem verticesAux_finRange_map {n : ℕ}
    (f : Fin n → RoseTree α) (offset : ℕ) :
    ((verticesAux offset ((List.finRange n).map f) : List Path) :
        Multiset Path) =
      (Multiset.ofList (List.finRange n)).bind fun i =>
        ((vertices (f i) : List Path) : Multiset Path).map ((offset + i.val) :: ·) := by
  induction n generalizing offset with
  | zero =>
    rw [show (List.finRange 0).map f = ([] : List (RoseTree α)) from rfl,
        verticesAux_nil]
    show ((↑([] : List Path)) : Multiset Path) = _
    rw [show (List.finRange 0 : List (Fin 0)) = [] from rfl]
    rfl
  | succ n ih =>
    rw [List.finRange_succ, List.map_cons, verticesAux_cons,
        show ((((vertices (f 0)).map ((offset : ℕ) :: ·)) ++
                verticesAux (offset + 1)
                  (((List.finRange n).map Fin.succ).map f) :
                List Path) : Multiset Path) =
            (((vertices (f 0)).map ((offset : ℕ) :: ·) : List Path) : Multiset Path) +
            ((verticesAux (offset + 1)
                (((List.finRange n).map Fin.succ).map f) : List Path) : Multiset Path)
            from by rw [← Multiset.coe_add]]
    rw [List.map_map]
    rw [ih (f ∘ Fin.succ) (offset + 1)]
    -- RHS bind: List.finRange (n + 1) = (0 : Fin (n+1)) :: (List.finRange n).map Fin.succ
    rw [show ((Multiset.ofList ((0 : Fin (n + 1)) ::
              (List.finRange n).map Fin.succ) : Multiset (Fin (n + 1))) =
            (0 : Fin (n + 1)) ::ₘ
              Multiset.ofList ((List.finRange n).map Fin.succ))
        from rfl,
        Multiset.cons_bind]
    rw [show offset + (0 : Fin (n + 1)).val = offset from by
          show offset + 0 = offset; omega]
    rw [show Multiset.ofList ((List.finRange n).map Fin.succ) =
            (Multiset.ofList (List.finRange n)).map Fin.succ from rfl]
    rw [Multiset.bind_map]
    refine congr_arg _ ?_
    refine Multiset.bind_congr fun j _ => ?_
    rw [show offset + 1 + j.val = offset + (j.val + 1) from by omega]
    rfl

/-- Forest-level partition of vertices for an arbitrary list of `multiGraft`
    results. Generalizes `verticesAux_multiGraftChildren_decomp`: instead of a
    single pair list with descent into children, each tree `cs[i]` is grafted
    against its own pair list `per_tree_pairs i`. The grafted forest is
    constructed via `(List.finRange cs.length).map fun i => multiGraft cs[i] _`,
    and its `verticesAux offset` decomposes per-tree into the 3-class
    partition (preserved / sourceSelf / lifted), with each class prepended by
    `(offset + i.val)`.

    This is the substrate Phase 4 of the A3.3 cons-case proof
    (`scratch/a33_cons_plan.md`) consumes when decomposing
    `vertices(T_ins :: F_ins)` into the 4-class V-partition by `QuadIdx`. -/
theorem vertices_forest_eq_partition
    (cs : List (RoseTree α))
    (per_tree_pairs : Fin cs.length → List (Path × RoseTree α))
    (h_valid : ∀ (i : Fin cs.length),
        ∀ pair ∈ per_tree_pairs i, IsValidPath pair.fst cs[i.val])
    (offset : ℕ) :
    ((verticesAux offset
        ((List.finRange cs.length).map fun i =>
          multiGraft cs[i.val] (per_tree_pairs i)) : List Path) :
        Multiset Path) =
      (Multiset.ofList (List.finRange cs.length)).bind fun i =>
        (((vertices cs[i.val] : Multiset Path).filterMap
              (preserveMulti (per_tree_pairs i)))
          + (((vertices cs[i.val] : Multiset Path).filter
                (· ∈ pairSources (per_tree_pairs i))).map
              (transport (per_tree_pairs i)))
          + ((Multiset.ofList (List.finRange (per_tree_pairs i).length)).bind
              (fun k => (vertices ((per_tree_pairs i)[k.val].snd) :
                Multiset Path).map (liftMulti (per_tree_pairs i) k)))
        ).map ((offset + i.val) :: ·) := by
  rw [verticesAux_finRange_map (fun i => multiGraft cs[i.val] (per_tree_pairs i))]
  refine Multiset.bind_congr fun i _ => ?_
  congr 1
  exact vertices_multiGraft_decomp cs[i.val] (per_tree_pairs i) (h_valid i)

/-! ## §10.6: `multiGraft_split_lifted_aux` — single-graft commutation

Grafting `c` at a lifted-vertex position `liftMulti pairs k q` in `multiGraft T pairs`
equals multi-grafting `T` with `pairs.set k.val (pairs[k.val].fst,
insertAt q c pairs[k.val].snd)`. The single-graft baby version of the full
`multiGraft_compose` (Route B, ~600+ LOC).

Substrate for Phase 4.2 of the A3.3 cons-case proof
(`scratch/a33_cons_plan.md`): "graft C-element at a T_graft-bucket vertex of T_ins"
equals "first insert C-element into the corresponding pre_T_B subtree, then graft
the modified pre_T_B-list into T". Per-c application; multiple T_graft-routed
C-elements iterate via the `q`-relative-to-modified-subtree update. -/

/-! ### §10.6.1 Helper: `posInGroup` of a root pair is `< rootPrependCount` -/

/-- When pair `k` has empty source path, its `posInGroup` is the count of earlier
    pairs in `pairs` with empty path, which is `< rootPrependCount pairs`. Direct
    consequence of `posInGroup`'s definition (filter-by-source) on a pair with
    `pairs[k].fst = []`. -/
private theorem posInGroup_lt_rootPrependCount
    (pairs : List (Path × RoseTree α)) (k : Fin pairs.length)
    (h_fst : pairs[k.val].fst = []) :
    posInGroup pairs k < rootPrependCount pairs := by
  unfold posInGroup rootPrependCount
  -- (pairs.take k.val).filter (·.fst = []) ++ ((pairs.drop k.val).filter (·.fst = []))
  -- = pairs.filter (·.fst = []) (filter distributes over append; take ++ drop = pairs).
  -- pairs[k] ∈ (pairs.drop k.val).filter, contributing ≥ 1 to drop's length.
  -- The goal uses `pairs[k]` (Fin instance); rewrite to use `[]` via h_fst.
  rw [show pairs[k].fst = ([] : Path) from h_fst]
  have h_split : ((pairs.take k.val).filter (fun pair => pair.fst = [])).length +
                  ((pairs.drop k.val).filter (fun pair => pair.fst = [])).length =
                  (pairs.filter (fun pair => pair.fst = [])).length := by
    rw [← List.length_append, ← List.filter_append, List.take_append_drop]
  have h_drop_pos : 0 < ((pairs.drop k.val).filter (fun pair => pair.fst = [])).length := by
    have h_mem : pairs[k.val] ∈ ((pairs.drop k.val).filter (fun pair => pair.fst = [])) := by
      rw [List.mem_filter]
      refine ⟨?_, ?_⟩
      · -- pairs[k] ∈ pairs.drop k.val: it's the 0-th element of drop k.val.
        have h_lt : 0 < (pairs.drop k.val).length := by
          rw [List.length_drop]; omega
        have h_eq : (pairs.drop k.val)[0]'h_lt = pairs[k.val] := by
          rw [List.getElem_drop]; rfl
        rw [← h_eq]
        exact List.getElem_mem _
      · rw [h_fst]; rfl
    exact List.length_pos_of_mem h_mem
  omega

/-! ### §10.6.2 Helpers for the root case

The next two helpers (`rootPrepends_at_posInGroup_eq_snd` and
`filterMap_rootPrepend_set_root`) both reduce to structural induction on
`pairs` with case analysis on `p.fst` and `k_val`. The arithmetic is
straightforward but the proofs require care with dependent-type rewrites
(the goal has `arr[posInGroup ...]'h` where the proof `h` depends on
`posInGroup`). -/

/-- When `pairs[k].fst = []`, the `posInGroup`-th rootPrepend equals `pairs[k].snd`.

    Stated via `List.get?` (Option-valued) to avoid dependent-typing complications
    of the `arr[i]'h` form. Consumers convert via `List.get?_eq_some` /
    `List.getElem_eq_iff`. -/
private theorem rootPrepends_at_posInGroup_eq_snd
    (pairs : List (Path × RoseTree α)) (k : Fin pairs.length)
    (h_fst : pairs[k.val].fst = []) :
    (pairs.filterMap rootPrependFilter)[posInGroup pairs k]? = some pairs[k.val].snd := by
  induction pairs with
  | nil => exact absurd k.isLt (by simp)
  | cons p rest ih =>
    obtain ⟨k_val, hk_lt⟩ := k
    obtain ⟨p_fst, p_snd⟩ := p
    cases k_val with
    | zero =>
      have h_p_fst : p_fst = [] := h_fst
      subst h_p_fst
      have h_pos : posInGroup ((([], p_snd) :: rest) : List (Path × RoseTree α))
                     ⟨0, hk_lt⟩ = 0 :=
        posInGroup_cons_zero ([] : Path) p_snd rest
      rw [h_pos]
      rfl
    | succ k_pred =>
      have hk_lt' : k_pred < rest.length := by
        simp [List.length_cons] at hk_lt; omega
      have h_idx_eq : (((p_fst, p_snd) :: rest) : List (Path × RoseTree α))[k_pred + 1] =
          rest[k_pred] := List.getElem_cons_succ ..
      have h_rest_fst : rest[k_pred].fst = [] := by rw [← h_idx_eq]; exact h_fst
      have ih_applied := ih ⟨k_pred, hk_lt'⟩ h_rest_fst
      cases h_p_fst : p_fst with
      | nil =>
        subst h_p_fst
        have h_fin_eq : (⟨k_pred + 1, hk_lt⟩ : Fin (([], p_snd) :: rest).length) =
            Fin.succ ⟨k_pred, hk_lt'⟩ := rfl
        have h_snd_eq : (((([], p_snd) :: rest) : List (Path × RoseTree α))[k_pred + 1].snd) =
            rest[k_pred].snd := by rw [h_idx_eq]
        rw [h_snd_eq, h_fin_eq, posInGroup_cons_succ_root p_snd rest ⟨k_pred, hk_lt'⟩ h_rest_fst]
        show (p_snd :: rest.filterMap rootPrependFilter)[posInGroup rest ⟨k_pred, hk_lt'⟩ + 1]? = some rest[k_pred].snd
        rw [List.getElem?_cons_succ]
        exact ih_applied
      | cons p_h p_rest =>
        subst h_p_fst
        have h_fin_eq : (⟨k_pred + 1, hk_lt⟩ : Fin ((p_h :: p_rest, p_snd) :: rest).length) =
            Fin.succ ⟨k_pred, hk_lt'⟩ := rfl
        have h_snd_eq : (((p_h :: p_rest, p_snd) :: rest : List (Path × RoseTree α))[k_pred + 1].snd) =
            rest[k_pred].snd := by rw [h_idx_eq]
        rw [h_snd_eq, h_fin_eq]
        have h_pos := posInGroup_cons_succ_child p_h p_rest p_snd rest ⟨k_pred, hk_lt'⟩
        rw [h_rest_fst, if_neg (by exact List.cons_ne_nil _ _), Nat.add_zero] at h_pos
        rw [h_pos]
        exact ih_applied

/-- When `pairs[k].fst = []` and the new pair also has empty `fst`, replacing
    `pairs[k]` by `(([], newSnd))` in `pairs` produces a `filterMap rootPrependFilter`
    that's `pairs.filterMap rootPrependFilter` with the `posInGroup`-th entry
    replaced by `newSnd`. Structural induction on `pairs` parallel to
    `rootPrepends_at_posInGroup_eq_snd`. -/
private theorem filterMap_rootPrepend_set_root
    (pairs : List (Path × RoseTree α)) (k : Fin pairs.length)
    (h_fst : pairs[k.val].fst = []) (newSnd : RoseTree α) :
    (pairs.set k.val (([] : Path), newSnd)).filterMap rootPrependFilter =
    (pairs.filterMap rootPrependFilter).set (posInGroup pairs k) newSnd := by
  induction pairs with
  | nil => exact absurd k.isLt (by simp)
  | cons p rest ih =>
    obtain ⟨k_val, hk_lt⟩ := k
    obtain ⟨p_fst, p_snd⟩ := p
    cases k_val with
    | zero =>
      have h_p_fst : p_fst = [] := h_fst
      subst h_p_fst
      -- Set 0: (([], p_snd) :: rest).set 0 ([], newSnd) = ([], newSnd) :: rest
      -- filterMap of LHS: newSnd :: rest.filterMap _
      -- posInGroup _ 0 = 0; (filterMap rest).set 0 newSnd = newSnd :: tail of filterMap.
      -- filterMap of original: p_snd :: rest.filterMap _; .set 0 newSnd: newSnd :: rest.filterMap _.
      have h_pos : posInGroup ((([], p_snd) :: rest) : List (Path × RoseTree α))
                     ⟨0, hk_lt⟩ = 0 := posInGroup_cons_zero ([] : Path) p_snd rest
      rw [h_pos]
      show (((([], newSnd) :: rest) : List (Path × RoseTree α)).filterMap rootPrependFilter) =
           (((([], p_snd) :: rest) : List (Path × RoseTree α)).filterMap rootPrependFilter).set 0 newSnd
      rfl
    | succ k_pred =>
      have hk_lt' : k_pred < rest.length := by
        simp [List.length_cons] at hk_lt; omega
      have h_idx_eq : (((p_fst, p_snd) :: rest) : List (Path × RoseTree α))[k_pred + 1] =
          rest[k_pred] := List.getElem_cons_succ ..
      have h_rest_fst : rest[k_pred].fst = [] := by rw [← h_idx_eq]; exact h_fst
      have ih_applied := ih ⟨k_pred, hk_lt'⟩ h_rest_fst
      cases h_p_fst : p_fst with
      | nil =>
        subst h_p_fst
        -- ([], p_snd) :: rest. Set at k_pred+1 affects rest at k_pred.
        -- LHS filterMap: p_snd :: (rest.set k_pred ([], newSnd)).filterMap _
        -- = p_snd :: ((rest.filterMap _).set (posInGroup rest k_pred) newSnd) (by IH)
        -- RHS: (([], p_snd) :: rest).filterMap _ = p_snd :: rest.filterMap _.
        -- .set at posInGroup _ ⟨k_pred+1, _⟩ = posInGroup rest ⟨k_pred, _⟩ + 1 (from posInGroup_cons_succ_root).
        -- Set at j+1: (h :: t).set (j+1) v = h :: t.set j v.
        have h_fin_eq : (⟨k_pred + 1, hk_lt⟩ : Fin (([], p_snd) :: rest).length) =
            Fin.succ ⟨k_pred, hk_lt'⟩ := rfl
        rw [h_fin_eq, posInGroup_cons_succ_root p_snd rest ⟨k_pred, hk_lt'⟩ h_rest_fst]
        -- Goal: (((([], p_snd) :: rest).set (k_pred + 1) ([], newSnd)).filterMap _ =
        --       (([], p_snd) :: rest).filterMap _).set (posInGroup rest _ + 1) newSnd
        show ((([], p_snd) :: rest.set k_pred (([] : Path), newSnd) :
              List (Path × RoseTree α)).filterMap rootPrependFilter) =
             ((p_snd :: rest.filterMap rootPrependFilter).set
               (posInGroup rest ⟨k_pred, hk_lt'⟩ + 1) newSnd)
        rw [show ((([], p_snd) :: rest.set k_pred (([] : Path), newSnd) :
              List (Path × RoseTree α)).filterMap rootPrependFilter) =
              p_snd :: (rest.set k_pred (([] : Path), newSnd)).filterMap rootPrependFilter
              from rfl]
        rw [List.set_cons_succ]
        rw [ih_applied]
      | cons p_h p_rest =>
        subst h_p_fst
        -- (p_h :: p_rest, p_snd) :: rest. Set at k_pred+1 affects rest at k_pred.
        -- LHS filterMap drops the head (since p.fst ≠ []): (rest.set k_pred _).filterMap _
        -- RHS: filterMap of (p_h :: p_rest, p_snd) :: rest is rest.filterMap _.
        -- posInGroup unchanged via posInGroup_cons_succ_child with non-match.
        have h_fin_eq : (⟨k_pred + 1, hk_lt⟩ : Fin ((p_h :: p_rest, p_snd) :: rest).length) =
            Fin.succ ⟨k_pred, hk_lt'⟩ := rfl
        rw [h_fin_eq]
        have h_pos := posInGroup_cons_succ_child p_h p_rest p_snd rest ⟨k_pred, hk_lt'⟩
        rw [h_rest_fst, if_neg (by exact List.cons_ne_nil _ _), Nat.add_zero] at h_pos
        rw [h_pos]
        show (((p_h :: p_rest, p_snd) :: rest.set k_pred (([] : Path), newSnd) :
              List (Path × RoseTree α)).filterMap rootPrependFilter) =
             ((rest.filterMap rootPrependFilter).set
               (posInGroup rest ⟨k_pred, hk_lt'⟩) newSnd)
        rw [show (((p_h :: p_rest, p_snd) :: rest.set k_pred (([] : Path), newSnd) :
              List (Path × RoseTree α)).filterMap rootPrependFilter) =
              (rest.set k_pred (([] : Path), newSnd)).filterMap rootPrependFilter
              from rfl]
        rw [ih_applied]

/-- Auxiliary: setting `pairs[k]` (with empty fst) to `([], newSnd)` (also
    empty fst) leaves `filterMap headChildFilter` unchanged. -/
private theorem filterMap_headChild_set_root
    (pairs : List (Path × RoseTree α)) (k : Fin pairs.length)
    (h_fst : pairs[k.val].fst = []) (newSnd : RoseTree α) :
    (pairs.set k.val (([] : Path), newSnd)).filterMap headChildFilter =
    pairs.filterMap headChildFilter := by
  induction pairs with
  | nil => exact absurd k.isLt (by simp)
  | cons p rest ih =>
    obtain ⟨k_val, hk_lt⟩ := k
    obtain ⟨p_fst, p_snd⟩ := p
    cases k_val with
    | zero =>
      have h_p_fst : p_fst = [] := h_fst
      subst h_p_fst
      rfl
    | succ k_pred =>
      have hk_lt' : k_pred < rest.length := by
        simp [List.length_cons] at hk_lt; omega
      have h_idx_eq : (((p_fst, p_snd) :: rest) : List (Path × RoseTree α))[k_pred + 1] =
          rest[k_pred] := List.getElem_cons_succ ..
      have h_rest_fst : rest[k_pred].fst = [] := by rw [← h_idx_eq]; exact h_fst
      have ih_applied := ih ⟨k_pred, hk_lt'⟩ h_rest_fst
      show (((p_fst, p_snd) :: rest.set k_pred (([] : Path), newSnd) :
            List (Path × RoseTree α)).filterMap headChildFilter) =
           (((p_fst, p_snd) :: rest : List (Path × RoseTree α)).filterMap headChildFilter)
      rw [List.filterMap_cons, List.filterMap_cons]
      rw [ih_applied]

/-- Auxiliary: setting `pairs[k]` (with empty fst) to `([], newSnd)` (also
    empty fst) leaves `filterMap tailChildFilter` unchanged. -/
private theorem filterMap_tailChild_set_root
    (pairs : List (Path × RoseTree α)) (k : Fin pairs.length)
    (h_fst : pairs[k.val].fst = []) (newSnd : RoseTree α) :
    (pairs.set k.val (([] : Path), newSnd)).filterMap tailChildFilter =
    pairs.filterMap tailChildFilter := by
  induction pairs with
  | nil => exact absurd k.isLt (by simp)
  | cons p rest ih =>
    obtain ⟨k_val, hk_lt⟩ := k
    obtain ⟨p_fst, p_snd⟩ := p
    cases k_val with
    | zero =>
      have h_p_fst : p_fst = [] := h_fst
      subst h_p_fst
      rfl
    | succ k_pred =>
      have hk_lt' : k_pred < rest.length := by
        simp [List.length_cons] at hk_lt; omega
      have h_idx_eq : (((p_fst, p_snd) :: rest) : List (Path × RoseTree α))[k_pred + 1] =
          rest[k_pred] := List.getElem_cons_succ ..
      have h_rest_fst : rest[k_pred].fst = [] := by rw [← h_idx_eq]; exact h_fst
      have ih_applied := ih ⟨k_pred, hk_lt'⟩ h_rest_fst
      show (((p_fst, p_snd) :: rest.set k_pred (([] : Path), newSnd) :
            List (Path × RoseTree α)).filterMap tailChildFilter) =
           (((p_fst, p_snd) :: rest : List (Path × RoseTree α)).filterMap tailChildFilter)
      rw [List.filterMap_cons, List.filterMap_cons]
      rw [ih_applied]

/-- When `pairs[k].fst = []` and we replace `pairs[k]` with `([], newSnd)` (still
    empty fst), the multiGraftChildren is unchanged: descent filters drop empty-fst
    entries either way. -/
private theorem multiGraftChildren_set_root_unchanged
    (cs : List (RoseTree α)) (pairs : List (Path × RoseTree α)) (k : Fin pairs.length)
    (h_fst : pairs[k.val].fst = []) (newSnd : RoseTree α) :
    multiGraftChildren cs (pairs.set k.val (([] : Path), newSnd)) =
    multiGraftChildren cs pairs := by
  induction cs generalizing pairs with
  | nil => rfl
  | cons c cs_rest ih_cs =>
    show multiGraft c ((pairs.set k.val (([] : Path), newSnd)).filterMap headChildFilter) ::
         multiGraftChildren cs_rest ((pairs.set k.val (([] : Path), newSnd)).filterMap tailChildFilter)
       = multiGraft c (pairs.filterMap headChildFilter) ::
         multiGraftChildren cs_rest (pairs.filterMap tailChildFilter)
    rw [filterMap_headChild_set_root pairs k h_fst newSnd,
        filterMap_tailChild_set_root pairs k h_fst newSnd]

/-! ### §10.6.3 Helpers for the descent case -/

/-- `multiGraftChildren cs pairs` has the same length as `cs`. -/
private theorem multiGraftChildren_length :
    ∀ (cs : List (RoseTree α)) (pairs : List (Path × RoseTree α)),
    (multiGraftChildren cs pairs).length = cs.length
  | [], _ => rfl
  | c :: cs', pairs => by
    rw [multiGraftChildren_cons_cs, List.length_cons, List.length_cons,
        multiGraftChildren_length cs' (pairs.filterMap tailChildFilter)]

/-- Indexing `multiGraftChildren cs pairs` at `j` gives `multiGraft cs[j]
    (descentToChild j pairs)`. Stated via get? to avoid dependent typing. -/
private theorem multiGraftChildren_getElem?
    (cs : List (RoseTree α)) (pairs : List (Path × RoseTree α)) (j : ℕ) (h : j < cs.length) :
    (multiGraftChildren cs pairs)[j]? =
      some (multiGraft (cs[j]'h) (descentToChild j pairs)) := by
  induction cs generalizing pairs j with
  | nil => exact absurd h (by simp)
  | cons c cs' ih_cs =>
    cases j with
    | zero =>
      rw [multiGraftChildren_cons_cs, List.getElem?_cons_zero, descentToChild_zero]
      rfl
    | succ j_pred =>
      rw [multiGraftChildren_cons_cs, List.getElem?_cons_succ]
      have h' : j_pred < cs'.length := by simp [List.length_cons] at h; omega
      rw [ih_cs (pairs.filterMap tailChildFilter) j_pred h']
      rw [← descentToChild_succ]
      rfl

/-! ### §10.6.4 Helpers for the descent-case set commutation -/

/-- Setting `pairs[k]` to `(j :: rest_path, X)` (preserving its first index `j`)
    and descending into child `j` equals first descending then setting the
    descent-corresponding index. -/
private theorem descentToChild_set_same_head_eq (j : ℕ) (pairs : List (Path × RoseTree α))
    (k : Fin pairs.length) (rest_path : Path) (h : pairs[k.val].fst = j :: rest_path)
    (X : RoseTree α) :
    descentToChild j (pairs.set k.val (j :: rest_path, X)) =
      (descentToChild j pairs).set (descentIdxOf j pairs k) (rest_path, X) := by
  induction pairs with
  | nil => exact absurd k.isLt (by simp)
  | cons p rest ih =>
    obtain ⟨k_val, hk_lt⟩ := k
    obtain ⟨p_fst, p_snd⟩ := p
    cases k_val with
    | zero =>
      have h_p_fst : p_fst = j :: rest_path := h
      subst h_p_fst
      show descentToChild j (((j :: rest_path, X) :: rest) : List (Path × RoseTree α)) =
          (descentToChild j (((j :: rest_path, p_snd) :: rest) :
              List (Path × RoseTree α))).set
            (descentIdxOf j (((j :: rest_path, p_snd) :: rest) :
              List (Path × RoseTree α)) ⟨0, hk_lt⟩) (rest_path, X)
      rw [descentToChild_cons_consPath_eq, descentToChild_cons_consPath_eq,
          descentIdxOf_at_zero]
      rfl
    | succ k_pred =>
      have hk_lt' : k_pred < rest.length := by
        simp only [List.length_cons] at hk_lt; omega
      have h_idx_eq :
          (((p_fst, p_snd) :: rest) : List (Path × RoseTree α))[k_pred + 1] = rest[k_pred] :=
        List.getElem_cons_succ ..
      have h_rest_fst : rest[k_pred].fst = j :: rest_path := by
        rw [← h_idx_eq]; exact h
      have ih_applied := ih ⟨k_pred, hk_lt'⟩ h_rest_fst
      show descentToChild j ((((p_fst, p_snd) :: rest.set k_pred (j :: rest_path, X)) :
            List (Path × RoseTree α))) =
          (descentToChild j (((p_fst, p_snd) :: rest) : List (Path × RoseTree α))).set
            (descentIdxOf j (((p_fst, p_snd) :: rest) : List (Path × RoseTree α))
              ⟨k_pred + 1, hk_lt⟩) (rest_path, X)
      have h_fin_eq : (⟨k_pred + 1, hk_lt⟩ : Fin (((p_fst, p_snd) :: rest).length)) =
          Fin.succ ⟨k_pred, hk_lt'⟩ := rfl
      rw [h_fin_eq, descentIdxOf_cons_succ j (p_fst, p_snd) rest ⟨k_pred, hk_lt'⟩]
      cases p_fst with
      | nil =>
        rw [descentToChild_cons_nilPath, descentToChild_cons_nilPath, ih_applied]
        simp
      | cons p_h p_rest =>
        by_cases hjh : j = p_h
        · subst hjh
          rw [descentToChild_cons_consPath_eq j p_rest p_snd
                (rest.set k_pred (j :: rest_path, X)),
              descentToChild_cons_consPath_eq j p_rest p_snd rest, ih_applied]
          rw [show ((j :: p_rest, p_snd) : Path × RoseTree α).fst.head? = some j from rfl,
              if_pos rfl]
          exact List.set_cons_succ.symm
        · rw [descentToChild_cons_consPath_ne j p_h p_rest p_snd
                (rest.set k_pred (j :: rest_path, X)) hjh,
              descentToChild_cons_consPath_ne j p_h p_rest p_snd rest hjh, ih_applied]
          rw [show ((p_h :: p_rest, p_snd) : Path × RoseTree α).fst.head? = some p_h from rfl]
          rw [if_neg (by intro heq; injection heq with h1; exact hjh h1.symm)]
          simp

/-- Setting `pairs[k]` to a pair with first index `j` leaves `descentToChild j' pairs`
    unchanged for any `j' ≠ j` — descents into other children don't see the modified
    pair. -/
private theorem descentToChild_set_same_head_ne (j j' : ℕ) (h_jj : j ≠ j')
    (pairs : List (Path × RoseTree α)) (k : Fin pairs.length) (rest_path : Path)
    (h : pairs[k.val].fst = j :: rest_path) (X : RoseTree α) :
    descentToChild j' (pairs.set k.val (j :: rest_path, X)) = descentToChild j' pairs := by
  induction pairs with
  | nil => exact absurd k.isLt (by simp)
  | cons p rest ih =>
    obtain ⟨k_val, hk_lt⟩ := k
    obtain ⟨p_fst, p_snd⟩ := p
    cases k_val with
    | zero =>
      have h_p_fst : p_fst = j :: rest_path := h
      subst h_p_fst
      show descentToChild j' (((j :: rest_path, X) :: rest) : List (Path × RoseTree α)) =
          descentToChild j' (((j :: rest_path, p_snd) :: rest) : List (Path × RoseTree α))
      rw [descentToChild_cons_consPath_ne j' j rest_path X rest (Ne.symm h_jj),
          descentToChild_cons_consPath_ne j' j rest_path p_snd rest (Ne.symm h_jj)]
    | succ k_pred =>
      have hk_lt' : k_pred < rest.length := by
        simp only [List.length_cons] at hk_lt; omega
      have h_idx_eq :
          (((p_fst, p_snd) :: rest) : List (Path × RoseTree α))[k_pred + 1] = rest[k_pred] :=
        List.getElem_cons_succ ..
      have h_rest_fst : rest[k_pred].fst = j :: rest_path := by
        rw [← h_idx_eq]; exact h
      have ih_applied := ih ⟨k_pred, hk_lt'⟩ h_rest_fst
      show descentToChild j' ((((p_fst, p_snd) :: rest.set k_pred (j :: rest_path, X)) :
            List (Path × RoseTree α))) =
          descentToChild j' (((p_fst, p_snd) :: rest) : List (Path × RoseTree α))
      cases p_fst with
      | nil =>
        rw [descentToChild_cons_nilPath, descentToChild_cons_nilPath]
        exact ih_applied
      | cons p_h p_rest =>
        by_cases hjh' : j' = p_h
        · subst hjh'
          rw [descentToChild_cons_consPath_eq j' p_rest p_snd
                (rest.set k_pred (j :: rest_path, X)),
              descentToChild_cons_consPath_eq j' p_rest p_snd rest, ih_applied]
        · rw [descentToChild_cons_consPath_ne j' p_h p_rest p_snd
                (rest.set k_pred (j :: rest_path, X)) hjh',
              descentToChild_cons_consPath_ne j' p_h p_rest p_snd rest hjh']
          exact ih_applied

/-- When `pairs[k].fst = j :: rest_path` (so the pair targets child `j`) and we
    set its `snd` to `X` while keeping the same first index, `multiGraftChildren cs`
    changes only at the `j`-th position (when `j < cs.length`): the new value is
    `multiGraft cs[j]` of the descented pair list with the corresponding descent
    index updated. -/
private theorem multiGraftChildren_set_same_head (cs : List (RoseTree α))
    (pairs : List (Path × RoseTree α)) (k : Fin pairs.length) (j : ℕ) (rest_path : Path)
    (h : pairs[k.val].fst = j :: rest_path) (X : RoseTree α) (h_j_lt : j < cs.length) :
    multiGraftChildren cs (pairs.set k.val (j :: rest_path, X)) =
    (multiGraftChildren cs pairs).set j
      (multiGraft (cs[j]'h_j_lt)
        ((descentToChild j pairs).set (descentIdxOf j pairs k) (rest_path, X))) := by
  apply List.ext_getElem?
  intro i
  by_cases h_i_lt : i < cs.length
  · rw [multiGraftChildren_getElem? cs (pairs.set k.val (j :: rest_path, X)) i h_i_lt]
    rw [List.getElem?_set]
    by_cases h_ij : j = i
    · subst h_ij
      rw [if_pos rfl, if_pos (by rw [multiGraftChildren_length]; exact h_i_lt),
          descentToChild_set_same_head_eq j pairs k rest_path h X]
    · rw [if_neg h_ij,
          multiGraftChildren_getElem? cs pairs i h_i_lt,
          descentToChild_set_same_head_ne j i h_ij pairs k rest_path h X]
  · push Not at h_i_lt
    rw [List.getElem?_eq_none (by rw [multiGraftChildren_length]; exact h_i_lt),
        List.getElem?_eq_none (by
          rw [List.length_set, multiGraftChildren_length]; exact h_i_lt)]

/-- When `pairs[k].fst = j :: rest_path` with `j ≥ cs.length` (the pair targets a
    non-existent child of `cs`), setting `pairs[k]` while preserving the first
    index leaves `multiGraftChildren cs` unchanged: the modified pair is only
    visible to descents into out-of-range children. -/
private theorem multiGraftChildren_set_invalid_head (cs : List (RoseTree α))
    (pairs : List (Path × RoseTree α)) (k : Fin pairs.length) (j : ℕ) (rest_path : Path)
    (h : pairs[k.val].fst = j :: rest_path) (X : RoseTree α) (h_j_ge : cs.length ≤ j) :
    multiGraftChildren cs (pairs.set k.val (j :: rest_path, X)) =
    multiGraftChildren cs pairs := by
  apply List.ext_getElem?
  intro i
  by_cases h_i_lt : i < cs.length
  · rw [multiGraftChildren_getElem? cs (pairs.set k.val (j :: rest_path, X)) i h_i_lt,
        multiGraftChildren_getElem? cs pairs i h_i_lt]
    have h_ij : j ≠ i := fun heq => Nat.not_lt.mpr h_j_ge (heq ▸ h_i_lt)
    rw [descentToChild_set_same_head_ne j i h_ij pairs k rest_path h X]
  · push Not at h_i_lt
    rw [List.getElem?_eq_none (by rw [multiGraftChildren_length]; exact h_i_lt),
        List.getElem?_eq_none (by rw [multiGraftChildren_length]; exact h_i_lt)]

/-- When `pairs[k].fst ≠ []`, the new pair (with the same first index) is also
    excluded by `rootPrependFilter`, so the root-prepend filterMap is unchanged. -/
private theorem filterMap_rootPrepend_set_nonRoot
    (pairs : List (Path × RoseTree α)) (k : Fin pairs.length)
    (newPair : Path × RoseTree α) (h_old : pairs[k.val].fst ≠ [])
    (h_new : newPair.fst ≠ []) :
    (pairs.set k.val newPair).filterMap rootPrependFilter =
    pairs.filterMap rootPrependFilter := by
  induction pairs with
  | nil => exact absurd k.isLt (by simp)
  | cons p rest ih =>
    obtain ⟨k_val, hk_lt⟩ := k
    obtain ⟨p_fst, p_snd⟩ := p
    cases k_val with
    | zero =>
      have h_p_fst_ne : p_fst ≠ [] := h_old
      cases h_pf : p_fst with
      | nil => exact absurd h_pf h_p_fst_ne
      | cons p_h p_rest =>
        obtain ⟨npfst, npsnd⟩ := newPair
        cases h_npf : npfst with
        | nil => exact absurd h_npf h_new
        | cons npf_h npf_rest =>
          rfl
    | succ k_pred =>
      have hk_lt' : k_pred < rest.length := by
        simp only [List.length_cons] at hk_lt; omega
      have h_idx_eq :
          (((p_fst, p_snd) :: rest) : List (Path × RoseTree α))[k_pred + 1] = rest[k_pred] :=
        List.getElem_cons_succ ..
      have h_rest_fst_ne : rest[k_pred].fst ≠ [] := by rw [← h_idx_eq]; exact h_old
      have ih_applied := ih ⟨k_pred, hk_lt'⟩ h_rest_fst_ne
      show ((((p_fst, p_snd) :: rest.set k_pred newPair) :
            List (Path × RoseTree α)).filterMap rootPrependFilter) =
          (((p_fst, p_snd) :: rest) : List (Path × RoseTree α)).filterMap rootPrependFilter
      rw [List.filterMap_cons, List.filterMap_cons]
      rw [ih_applied]

/-! ### §10.6.5 Main statement -/

/-- Single-graft baby version of `multiGraft` composition: grafting `c` at a
    lifted-vertex path of `multiGraft T pairs` equals multi-grafting `T` with
    pair `k` modified to have `c` inserted into its tree at relative path `q`.

    This is the path-arithmetic substrate for Phase 4.2 of the A3.3 cons-case
    proof (`scratch/a33_cons_plan.md`). Single-graft only; multi-graft variants
    iterate this via the `q`-relative-to-modified-subtree update.

    Proof: structural induction on `T = RoseTree.node a cs`.
    - Case (a) `pairs[k.val].fst = []`: `liftMulti = posInGroup k :: q`.
      Both sides land at the `posInGroup k`-th rootPrepend, modified to
      `insertAt q c pairs[k.val].snd`.
    - Case (b) `pairs[k.val].fst = j :: rest`: by `liftMulti_at_child_descent`
      the lifted path is `(rootPrependCount pairs + j) :: liftMulti (descentToChild j pairs) k' q`.
      The LHS descends past root-prepends into the `j`-th element of
      `multiGraftChildren cs pairs` (= `multiGraft cs[j] (descentToChild j pairs)`)
      and applies the IH on `cs[j]`. The RHS is reassembled via
      `multiGraftChildren_set_same_head` (or `_invalid_head` when `j ≥ cs.length`,
      where both sides are no-ops). -/
theorem multiGraft_split_lifted_aux :
    ∀ (T : RoseTree α) (pairs : List (Path × RoseTree α))
    (k : Fin pairs.length) (q : Path) (c : RoseTree α),
    insertAt (liftMulti pairs k q) c (multiGraft T pairs) =
    multiGraft T (pairs.set k.val
      (pairs[k.val].fst, insertAt q c pairs[k.val].snd))
  | .node a cs, pairs, k, q, c => by
    -- Helper for case (a): bridge get? form to Fin-indexed form.
    have h_get_at_root :
        ∀ (h_fst : pairs[k.val].fst = []),
        (pairs.filterMap rootPrependFilter)[posInGroup pairs k]'(by
          rw [length_filterMap_rootPrependFilter]
          exact posInGroup_lt_rootPrependCount pairs k h_fst) = pairs[k.val].snd := by
      intro h_fst
      have h_some := rootPrepends_at_posInGroup_eq_snd pairs k h_fst
      rw [List.getElem?_eq_some_iff] at h_some
      obtain ⟨_, h⟩ := h_some
      exact h
    by_cases h_fst : pairs[k.val].fst = []
    · -- Case (a): pairs[k.val].fst = []
      have h_liftMulti : liftMulti pairs k q = posInGroup pairs k :: q := by
        unfold liftMulti
        show transport pairs pairs[k.val].fst ++ (posInGroup pairs k :: q) =
             posInGroup pairs k :: q
        rw [h_fst]
        rfl
      rw [h_liftMulti, multiGraft_node]
      set P := posInGroup pairs k with hP_def
      set rootPrepends := pairs.filterMap rootPrependFilter with hRP_def
      have hP_lt_rp : P < rootPrepends.length := by
        rw [hRP_def, length_filterMap_rootPrependFilter]
        exact posInGroup_lt_rootPrependCount pairs k h_fst
      have hP_lt_total : P < (rootPrepends ++ multiGraftChildren cs pairs).length := by
        rw [List.length_append]; omega
      rw [insertAt_cons_of_lt P q c a (rootPrepends ++ multiGraftChildren cs pairs) hP_lt_total]
      rw [List.getElem_append_left hP_lt_rp]
      rw [h_get_at_root h_fst]
      rw [List.set_append_left _ _ hP_lt_rp]
      -- LHS settled. Now massage RHS using h_fst and the helpers.
      rw [show (pairs[k.val].fst, insertAt q c pairs[k.val].snd) =
              (([] : Path), insertAt q c pairs[k.val].snd) from by rw [h_fst]]
      rw [multiGraft_node]
      rw [filterMap_rootPrepend_set_root pairs k h_fst (insertAt q c pairs[k.val].snd)]
      rw [multiGraftChildren_set_root_unchanged cs pairs k h_fst (insertAt q c pairs[k.val].snd)]
    · -- Case (b): pairs[k.val].fst ≠ [], so it's of form (j :: rest_path).
      obtain ⟨j, rest_path, h_fst_eq⟩ :
          ∃ j rest_path, pairs[k.val].fst = j :: rest_path := by
        cases h_pf : pairs[k.val].fst with
        | nil => exact absurd h_pf h_fst
        | cons jh jt => exact ⟨jh, jt, rfl⟩
      have h_old_ne : pairs[k.val].fst ≠ [] := by rw [h_fst_eq]; simp
      have h_new_ne :
          ((j :: rest_path, insertAt q c pairs[k.val].snd) : Path × RoseTree α).fst ≠ [] := by simp
      have h_pair_subst :
          (pairs[k.val].fst, insertAt q c pairs[k.val].snd) =
            (j :: rest_path, insertAt q c pairs[k.val].snd) := by rw [h_fst_eq]
      rw [liftMulti_at_child_descent pairs k j rest_path h_fst_eq q, multiGraft_node]
      set rootPrepends := pairs.filterMap rootPrependFilter with hRP_def
      set children := multiGraftChildren cs pairs with hC_def
      have h_rp_len : rootPrepends.length = rootPrependCount pairs := by
        rw [hRP_def, length_filterMap_rootPrependFilter]
      have h_ch_len : children.length = cs.length := by
        rw [hC_def, multiGraftChildren_length]
      by_cases h_j_lt : j < cs.length
      · -- Valid descent.
        have h_idx_lt :
            rootPrependCount pairs + j < (rootPrepends ++ children).length := by
          rw [List.length_append, h_rp_len, h_ch_len]; omega
        rw [insertAt_cons_of_lt _ _ _ _ _ h_idx_lt]
        have h_N_le : rootPrepends.length ≤ rootPrependCount pairs + j := by
          rw [h_rp_len]; omega
        -- Compute the indexed value (avoids proof-dependent rewrite chain).
        have h_val :
            (rootPrepends ++ children)[rootPrependCount pairs + j]'h_idx_lt =
              multiGraft (cs[j]'h_j_lt) (descentToChild j pairs) := by
          have h_some :
              (rootPrepends ++ children)[rootPrependCount pairs + j]? =
                some (multiGraft (cs[j]'h_j_lt) (descentToChild j pairs)) := by
            rw [List.getElem?_append_right h_N_le]
            rw [show rootPrependCount pairs + j - rootPrepends.length = j from by
                  rw [h_rp_len]; omega]
            rw [hC_def]
            exact multiGraftChildren_getElem? cs pairs j h_j_lt
          rw [List.getElem?_eq_some_iff] at h_some
          obtain ⟨_, h_eq⟩ := h_some
          exact h_eq
        rw [h_val]
        rw [List.set_append_right _ _ h_N_le]
        rw [show rootPrependCount pairs + j - rootPrepends.length = j from by
              rw [h_rp_len]; omega]
        have ih :=
          multiGraft_split_lifted_aux (cs[j]'h_j_lt) (descentToChild j pairs)
            ⟨descentIdxOf j pairs k, by
              rw [descentToChild_length_eq]
              exact descentIdxOf_lt j pairs k (by rw [h_fst_eq]; rfl)⟩ q c
        rw [ih, descentToChild_getElem_at_descentIdxOf j pairs k rest_path h_fst_eq]
        rw [h_pair_subst, multiGraft_node]
        rw [filterMap_rootPrepend_set_nonRoot pairs k _ h_old_ne h_new_ne]
        rw [multiGraftChildren_set_same_head cs pairs k j rest_path h_fst_eq
              (insertAt q c pairs[k.val].snd) h_j_lt]
      · -- Invalid descent: j ≥ cs.length, both sides no-op.
        push Not at h_j_lt
        have h_idx_ge : ¬ (rootPrependCount pairs + j < (rootPrepends ++ children).length) := by
          rw [List.length_append, h_rp_len, h_ch_len]; omega
        rw [insertAt_cons_of_not_lt _ _ _ _ _ h_idx_ge]
        rw [h_pair_subst, multiGraft_node]
        rw [filterMap_rootPrepend_set_nonRoot pairs k _ h_old_ne h_new_ne]
        rw [multiGraftChildren_set_invalid_head cs pairs k j rest_path h_fst_eq
              (insertAt q c pairs[k.val].snd) h_j_lt]
termination_by T _ _ _ _ => T.numNodes
decreasing_by exact numNodes_lt_of_getElem h_j_lt

/-! ## §10.7: `multiGraft_cons_pair` — preserved-vertex multiGraft-extend

Prepending a new pair `(v, c)` to the pair list equals inserting `c` at
the transported path of `v` in `multiGraft T pairs`. The "preserved" analog
of `multiGraft_split_lifted_aux` (§10.6), but in PREPEND form rather than
APPEND form — this avoids the planar-order mismatch at the root (where
`insertAt [] c` puts `c` first in children but `multiGraft T (pairs ++ [([], c)])`
puts `c` last in root-prepends).

**Why prepend form works without a validity hypothesis.**
- `v = []` case: both sides yield `node a (c :: rootPrepends ++ multiGraftChildren)`;
  the new `([], c)` pair is the *first* root-prepend, matching `insertAt [] c`'s
  prepend-to-children semantics.
- `v = j :: rest, j < cs.length` case: descend into the `j`-th child via the
  IH (decreasing on the child's weight); the `(rest, c)` descented pair is the
  first in the child's pair list.
- `v = j :: rest, j ≥ cs.length` case: both sides are no-ops (multiGraftChildren
  ignores the new pair since no valid descent target; insertAt is a no-op past
  the children-list bound).

The APPEND form `multiGraft T (pairs ++ [(v, c)])` follows from this lemma
plus `multiGraft_perm_pair` (only at PlanarEquiv level, since planar-order
differs between prepend and append at root).

This is the substrate for Phase D (T_orig and FA_orig buckets) of A3.3's
cons-case proof (`scratch/a33_phase4_2_session_prompt_16.md`). -/

/-- Helper: prepending an empty-path pair leaves `multiGraftChildren` unchanged
    (the new pair has empty path, so both `headChildFilter` and `tailChildFilter`
    drop it). Used in the `v = []` case of `multiGraft_cons_pair`. -/
private theorem multiGraftChildren_cons_nilPath_pair
    (cs : List (RoseTree α)) (pairs : List (Path × RoseTree α)) (c : RoseTree α) :
    multiGraftChildren cs (([], c) :: pairs) = multiGraftChildren cs pairs := by
  induction cs generalizing pairs with
  | nil => rfl
  | cons c' cs' ih =>
    show multiGraft c' (pairs.filterMap headChildFilter) ::
            multiGraftChildren cs' (pairs.filterMap tailChildFilter) =
         multiGraft c' (pairs.filterMap headChildFilter) ::
            multiGraftChildren cs' (pairs.filterMap tailChildFilter)
    rfl

/-- Prepend form: prepending `(v, c)` to the pair list equals inserting `c`
    at the transported path of `v` in `multiGraft T pairs`. No validity
    hypothesis on `v`: out-of-bounds case is a mutual no-op.

    The "preserved" analog of `multiGraft_split_lifted_aux` (§10.6). Phase A
    substrate for A3.3's cons-case proof
    (`scratch/a33_phase4_2_session_prompt_16.md`). -/
theorem multiGraft_cons_pair :
    ∀ (T : RoseTree α) (pairs : List (Path × RoseTree α))
      (v : Path) (c : RoseTree α),
    multiGraft T ((v, c) :: pairs) =
      insertAt (transport pairs v) c (multiGraft T pairs)
  | .node a cs, pairs, [], c => by
    -- Case v = []: new pair is a root prepend at position 0.
    rw [transport_nil_path, multiGraft_node, multiGraft_node]
    show RoseTree.node a (c :: pairs.filterMap rootPrependFilter ++
                          multiGraftChildren cs (([], c) :: pairs)) = _
    rw [multiGraftChildren_cons_nilPath_pair, insertAt_nil]
    rfl
  | .node a cs, pairs, j :: rest, c => by
    -- Case v = j :: rest. Recurse into the j-th child if j < cs.length.
    rw [transport_cons_path, multiGraft_node, multiGraft_node]
    show RoseTree.node a (pairs.filterMap rootPrependFilter ++
                          multiGraftChildren cs ((j :: rest, c) :: pairs)) = _
    set N := rootPrependCount pairs with hN_def
    set rootPrepends := pairs.filterMap rootPrependFilter with hRP_def
    set children := multiGraftChildren cs pairs with hC_def
    have h_rp_len : rootPrepends.length = N := by
      rw [hRP_def, length_filterMap_rootPrependFilter]
    have h_ch_len : children.length = cs.length := by
      rw [hC_def, multiGraftChildren_length]
    by_cases h_j_lt : j < cs.length
    · -- Valid descent: j + N is a valid index past the rootPrepends.
      have h_idx_lt : j + N < (rootPrepends ++ children).length := by
        rw [List.length_append, h_rp_len, h_ch_len]; omega
      rw [insertAt_cons_of_lt _ _ _ _ _ h_idx_lt]
      have h_N_le : rootPrepends.length ≤ j + N := by
        rw [h_rp_len]; omega
      have h_val :
          (rootPrepends ++ children)[j + N]'h_idx_lt =
            multiGraft (cs[j]'h_j_lt) (descentToChild j pairs) := by
        have h_some :
            (rootPrepends ++ children)[j + N]? =
              some (multiGraft (cs[j]'h_j_lt) (descentToChild j pairs)) := by
          rw [List.getElem?_append_right h_N_le]
          rw [show j + N - rootPrepends.length = j from by rw [h_rp_len]; omega]
          rw [hC_def]
          exact multiGraftChildren_getElem? cs pairs j h_j_lt
        rw [List.getElem?_eq_some_iff] at h_some
        obtain ⟨_, h_eq⟩ := h_some
        exact h_eq
      rw [h_val]
      rw [List.set_append_right _ _ h_N_le]
      rw [show j + N - rootPrepends.length = j from by rw [h_rp_len]; omega]
      -- Apply IH at cs[j], descentToChild j pairs, rest, c.
      have ih := multiGraft_cons_pair (cs[j]'h_j_lt) (descentToChild j pairs) rest c
      -- Show LHS-children = children.set j (...) using IH on the j-th component.
      rw [show multiGraftChildren cs ((j :: rest, c) :: pairs) =
              children.set j (multiGraft (cs[j]'h_j_lt)
                ((rest, c) :: descentToChild j pairs))
          from by
            apply List.ext_getElem?
            intro i
            by_cases h_i_lt : i < cs.length
            · rw [multiGraftChildren_getElem? cs ((j :: rest, c) :: pairs) i h_i_lt,
                  List.getElem?_set]
              by_cases h_ij : j = i
              · subst h_ij
                rw [if_pos rfl,
                    if_pos (by rw [hC_def, multiGraftChildren_length]; exact h_i_lt)]
                rw [descentToChild_cons_consPath_eq]
              · rw [if_neg h_ij, hC_def,
                    multiGraftChildren_getElem? cs pairs i h_i_lt,
                    descentToChild_cons_consPath_ne i j rest c pairs (Ne.symm h_ij)]
            · push Not at h_i_lt
              rw [List.getElem?_eq_none
                  (by rw [multiGraftChildren_length]; exact h_i_lt)]
              rw [List.getElem?_eq_none
                  (by rw [List.length_set, hC_def, multiGraftChildren_length];
                      exact h_i_lt)]]
      rw [ih]
    · -- Invalid descent: j ≥ cs.length, both sides no-op at children level.
      push Not at h_j_lt
      have h_idx_ge : ¬ (j + N < (rootPrepends ++ children).length) := by
        rw [List.length_append, h_rp_len, h_ch_len]; omega
      rw [insertAt_cons_of_not_lt _ _ _ _ _ h_idx_ge]
      rw [show multiGraftChildren cs ((j :: rest, c) :: pairs) = children
          from by
            apply List.ext_getElem?
            intro i
            by_cases h_i_lt : i < cs.length
            · rw [multiGraftChildren_getElem? cs ((j :: rest, c) :: pairs) i h_i_lt,
                  hC_def, multiGraftChildren_getElem? cs pairs i h_i_lt]
              have h_ij : i ≠ j := fun heq =>
                Nat.not_lt.mpr h_j_lt (heq ▸ h_i_lt)
              rw [descentToChild_cons_consPath_ne i j rest c pairs h_ij]
            · push Not at h_i_lt
              rw [List.getElem?_eq_none
                  (by rw [multiGraftChildren_length]; exact h_i_lt)]
              rw [hC_def, List.getElem?_eq_none
                  (by rw [multiGraftChildren_length]; exact h_i_lt)]]
termination_by T _ _ _ => T.numNodes
decreasing_by exact numNodes_lt_of_getElem h_j_lt

/-! ## §11: `multiGraft_compose` — full nested multi-graft composition

**Status (2026-05-15, 0.231.79):** plan landed; substrate not yet built.
See `scratch/multigraft_compose_plan.md` for full specification.

**Statement:**
```
theorem multiGraft_compose (T : RoseTree α)
    (outer_pairs : List (Path × RoseTree α))
    (inner_pairs : List (Path × RoseTree α))
    (h_outer_valid : ∀ p ∈ outer_pairs, IsValidPath p.fst T)
    (h_inner_valid : ∀ p ∈ inner_pairs, IsValidPath p.fst (multiGraft T outer_pairs)) :
    multiGraft (multiGraft T outer_pairs) inner_pairs =
    multiGraft T (composePairs outer_pairs inner_pairs)
```

**Why needed**: Closes A3.3 helpers `LHS_TRUE_eq_T_buckets` /
`LHS_FALSE_eq_FA_buckets` (substantive Phase 2-4 of each). The LHS contains
nested multi-grafts `mG T' (...)` where `T' = mG T outer_pairs`; collapsing
to a single multi-graft `mG T composed_pairs` enables matching the RHS
T_orig / T_graft / FA_orig / FA_graft summands.

**`composePairs` semantics**: for each inner pair `(p, c)` at position
`p ∈ vertices (mG T outer_pairs)`:
- **preserved/sourceSelf** (p = `transport outer_pairs v` for v ∈ vertices T):
  add `(v, c)` to outer_pairs.
- **lifted** (p = `liftMulti outer_pairs k q`): modify `outer_pairs[k].snd`
  to `insertAt q c outer_pairs[k].snd`.

These three classes are exhaustive by `vertices_multiGraft_decomp` (§9).

**Proof structure** (~600 LOC across 3-4 sessions):
- **Phase A** (~150 LOC): `composePairs` definition (operational via
  `decodePath` decoder) + theorem statement.
- **Phase B** (~150 LOC): inner_pairs = [] base case + cons-step setup
  via `multiGraft_cons_pair`.
- **Phase C** (~200 LOC): per-class handling in cons step
  (preserved/sourceSelf via `multiGraft_cons_pair`; lifted via
  `multiGraft_split_lifted_aux`).
- **Phase D** (~100 LOC): termination (decreasing weight argument).

**Substrate consumed**: `vertices_multiGraft_decomp` (§9),
`multiGraft_cons_pair` (§10.7), `multiGraft_split_lifted_aux` (§10.6),
`transport` / `liftMulti` / `pairSources` / `preserveMulti` (§7-8). -/

/-! ### §11.1: `absorbInnerPair` — single inner-pair absorption

For an inner pair `(p, c)` where `p ∈ vertices (mG T outer)`, returns the
modified outer pair list whose multi-graft of T equals `insertAt p c (mG T outer)`.

**Three-class semantics** (by `vertices_multiGraft_decomp`):
- preserved (p = `transport outer v`, v ∉ pairSources): `(v, c) :: outer` (PREPEND)
- sourceSelf (p = `transport outer v`, v ∈ pairSources): `(v, c) :: outer` (PREPEND)
- lifted (p = `liftMulti outer k q`): `outer.set k.val (..., insertAt q c outer[k].snd)`

**PREPEND, not APPEND** (subtle planar-order issue): the LHS `mG (mG T outer) inner`
puts inner root prepends FIRST in the result tree's children (followed by outer's
children). For the RHS to match planar-equally, `cp.filterMap rootPrependFilter` must
be `inner_root_prepends ++ outer_root_prepends`, i.e., NEW pairs go to the FRONT of
the pair list. APPEND would give `outer_root_prepends ++ inner_root_prepends` (wrong
order, planar-FALSE). See `[[feedback_multigraft_compose_prepend_foldr]]`.

**Implementation strategy** (recursive descent on p's structure relative to
`rootPrependCount outer`):
- If `p = []`: PREPEND `([], c)` to outer.
- If `p = i :: rest, i < rootPrependCount outer`: lifted in outer's i-th
  root prepend → modify outer.set k where k = rootPrependPairIdx outer i.
- If `p = i :: rest, i ≥ rootPrependCount outer`: descend into T's
  (i - rootPrependCount outer)-th child; recurse on descented outer pairs;
  lift back via `liftBackToOuter`.

Returns the original outer unchanged on invalid inputs (defensive). -/

/-- Find the pair-list index `k` whose pair contributes the `i`-th
    root-prepend (i.e., the (i+1)-th pair in pair-list order with `.fst = []`).
    Returns `none` if `i ≥ rootPrependCount outer`.

    Recursive on the outer list (as opposed to a filter over `List.finRange`):
    avoids dependent-type issues when proving recursive equation lemmas. -/
def rootPrependPairIdx : (outer : List (Path × RoseTree α)) → ℕ → Option (Fin outer.length)
  | [], _ => none
  | ([], _) :: rest, 0 => some (0 : Fin (rest.length + 1))
  | ([], _) :: rest, i + 1 => (rootPrependPairIdx rest i).map Fin.succ
  | (_ :: _, _) :: rest, i => (rootPrependPairIdx rest i).map Fin.succ

/-! ### §11.1.5: `rootPrependPairIdx` totality + bridge lemma

`rootPrependPairIdx_ne_none_of_lt` gives totality: when `i < rootPrependCount outer`,
the result is `some _`. The bridge lemma `posInGroup_of_rootPrependPairIdx`
relates the returned `Fin` index to `posInGroup`, used in the lifted-at-root
subcase of `absorbInnerPair_eq_insertAt`. -/

private theorem rootPrependPairIdx_ne_none_of_lt :
    ∀ (outer : List (Path × RoseTree α)) (i : ℕ),
    i < rootPrependCount outer → rootPrependPairIdx outer i ≠ none
  | [], i, h => absurd h (by simp)
  | ([], T) :: rest, 0, _ => by simp [rootPrependPairIdx]
  | ([], T) :: rest, i + 1, h => by
    rw [rootPrependCount_cons_nilPath] at h
    have h_rest : i < rootPrependCount rest := by omega
    have ih := rootPrependPairIdx_ne_none_of_lt rest i h_rest
    show (rootPrependPairIdx rest i).map Fin.succ ≠ none
    intro h_eq
    apply ih
    cases h_inner : rootPrependPairIdx rest i with
    | none => rfl
    | some k' => rw [h_inner] at h_eq; simp at h_eq
  | (j :: rp, T) :: rest, i, h => by
    rw [rootPrependCount_cons_consPath] at h
    have ih := rootPrependPairIdx_ne_none_of_lt rest i h
    show (rootPrependPairIdx rest i).map Fin.succ ≠ none
    intro h_eq
    apply ih
    cases h_inner : rootPrependPairIdx rest i with
    | none => rfl
    | some k' => rw [h_inner] at h_eq; simp at h_eq

/-- The bridge lemma: when `rootPrependPairIdx outer i = some k`, `k` indexes
    a root-prepend pair (`outer[k].fst = []`) and its position among
    root-prepend pairs is `i` (`posInGroup outer k = i`). Used in the lifted-at-root
    subcase of `absorbInnerPair_eq_insertAt` to bridge through
    `multiGraft_split_lifted_aux` + `liftMulti_at_root`. -/
private theorem posInGroup_of_rootPrependPairIdx :
    ∀ (outer : List (Path × RoseTree α)) (i : ℕ) (k : Fin outer.length),
    rootPrependPairIdx outer i = some k →
    outer[k.val].fst = [] ∧ posInGroup outer k = i
  | [], _, k, _ => absurd k.isLt (by simp)
  | ([], T) :: rest, 0, k, h => by
    -- rootPrependPairIdx (([], T) :: rest) 0 = some 0 by def
    show ((([], T) :: rest) : List (Path × RoseTree α))[k.val].fst = [] ∧
         posInGroup (([], T) :: rest) k = 0
    have h_def : rootPrependPairIdx (([], T) :: rest) 0 =
                 some (0 : Fin (rest.length + 1)) := rfl
    rw [h_def, Option.some_inj] at h
    subst h
    exact ⟨rfl, rfl⟩
  | ([], T) :: rest, i + 1, k, h => by
    have h_def : rootPrependPairIdx (([], T) :: rest) (i + 1) =
                 (rootPrependPairIdx rest i).map Fin.succ := rfl
    rw [h_def] at h
    cases h_inner : rootPrependPairIdx rest i with
    | none =>
      rw [h_inner] at h
      exact absurd h (by simp)
    | some k' =>
      rw [h_inner] at h
      rw [Option.map_some, Option.some_inj] at h
      subst h
      obtain ⟨h_fst', h_pos'⟩ :=
        posInGroup_of_rootPrependPairIdx rest i k' h_inner
      refine ⟨?_, ?_⟩
      · show ((([], T) :: rest) : List (Path × RoseTree α))[(Fin.succ k').val].fst = []
        show ((([], T) :: rest) : List (Path × RoseTree α))[k'.val + 1].fst = []
        rw [List.getElem_cons_succ]
        exact h_fst'
      · rw [posInGroup_cons_succ_root T rest k' h_fst']
        omega
  | (j :: rp, T) :: rest, i, k, h => by
    have h_def : rootPrependPairIdx ((j :: rp, T) :: rest) i =
                 (rootPrependPairIdx rest i).map Fin.succ := rfl
    rw [h_def] at h
    cases h_inner : rootPrependPairIdx rest i with
    | none =>
      rw [h_inner] at h
      exact absurd h (by simp)
    | some k' =>
      rw [h_inner] at h
      rw [Option.map_some, Option.some_inj] at h
      subst h
      obtain ⟨h_fst', h_pos'⟩ :=
        posInGroup_of_rootPrependPairIdx rest i k' h_inner
      refine ⟨?_, ?_⟩
      · show (((j :: rp, T) :: rest) : List (Path × RoseTree α))[(Fin.succ k').val].fst = []
        show (((j :: rp, T) :: rest) : List (Path × RoseTree α))[k'.val + 1].fst = []
        rw [List.getElem_cons_succ]
        exact h_fst'
      · rw [posInGroup_cons_succ_child j rp T rest k']
        rw [if_neg (by
          intro heq
          rw [h_fst'] at heq
          exact List.cons_ne_nil _ _ heq)]
        omega

/-- Walk through `outer`, substituting j-headed pair positions with the
    corresponding `modified` position (counted by `k'`), prefixed with `j`.
    Non-j-headed pairs are kept unchanged. Used by `liftBackToOuter` for
    the SET case.

    Substitutes the entire pair (with `j` prefix on `modified[k'].fst`) rather
    than just `.snd`, so that `descentToChild j (walkAndReplace ...) = modified`
    holds without needing a fst-preserve precondition. -/
private def walkAndReplace (j : ℕ) :
    List (Path × RoseTree α) → List (Path × RoseTree α) → ℕ → List (Path × RoseTree α)
  | [], _, _ => []
  | (p, T) :: rest, modified, k' =>
    if p.head? = some j then
      match modified[k']? with
      | some (q, T') => (j :: q, T') :: walkAndReplace j rest modified (k' + 1)
      | none => (p, T) :: walkAndReplace j rest modified (k' + 1)
    else
      (p, T) :: walkAndReplace j rest modified k'

/-- Lift a modification of `descented = descentToChild j outer` back to a
    modification of `outer`. Two cases by length:
    - `modified.length = descented.length + 1`: PREPEND case at descented level.
      `modified = (q, T) :: descented` for some `(q, T)`. Lift back: prepend
      `(j :: q, T)` to outer.
    - `modified.length = descented.length`: SET case at descented level.
      Walk through `outer`, substituting `.snd` at j-headed pair positions with
      corresponding modified positions (no-op at non-modified positions). -/
def liftBackToOuter (descented modified : List (Path × RoseTree α))
    (j : ℕ) (outer : List (Path × RoseTree α)) : List (Path × RoseTree α) :=
  if modified.length = descented.length + 1 then
    match modified with
    | (q, T) :: _ => (j :: q, T) :: outer
    | [] => outer
  else
    walkAndReplace j outer modified 0

/-- Absorb a single inner pair `(p, c)` into outer, returning the modified
    pair list. Recursive on path structure:
    - p = []: root vertex (preserved/sourceSelf class, v = []). PREPEND `([], c)` to outer.
    - p = i :: rest, i < rootPrependCount outer: lifted at pair k. Modify outer[k]
      to insert c at rest in outer[k].snd.
    - p = i :: rest, i ≥ rootPrependCount outer: descend into T's child at index
      (i - rootPrependCount outer). Recurse on the descended outer pairs, then
      lift back via `liftBackToOuter`. -/
def absorbInnerPair (outer : List (Path × RoseTree α))
    (p : Path) (c : RoseTree α) : List (Path × RoseTree α) :=
  match p with
  | [] =>
    -- Root vertex: preserved (or sourceSelf if [] ∈ pairSources outer).
    -- PREPEND ([], c) so that c becomes the FIRST root prepend in mG T outer'
    -- (matching insertAt [] c's prepend semantics — see multiGraft_cons_pair).
    ([], c) :: outer
  | i :: rest =>
    let N := rootPrependCount outer
    if i < N then
      -- Lifted: i indexes a rootPrepended subtree. Find pair k via rootPrependPairIdx.
      match rootPrependPairIdx outer i with
      | some k =>
        outer.set k.val (outer[k.val].fst, insertAt rest c outer[k.val].snd)
      | none => outer  -- defensive: should be unreachable since i < N
    else
      -- Child: (i - N) is a child index of T's root children.
      let descented := descentToChild (i - N) outer
      let modified := absorbInnerPair descented rest c
      liftBackToOuter descented modified (i - N) outer
termination_by p

/-! ### §11.1.6: `walkAndReplace` and `liftBackToOuter` substrate

Properties used in the descent case of `absorbInnerPair_eq_insertAt`. -/

@[simp] private theorem walkAndReplace_length (j : ℕ) :
    ∀ (outer modified : List (Path × RoseTree α)) (k' : ℕ),
    (walkAndReplace j outer modified k').length = outer.length
  | [], _, _ => rfl
  | (p, T) :: rest, modified, k' => by
    show (walkAndReplace j ((p, T) :: rest) modified k').length = rest.length + 1
    unfold walkAndReplace
    by_cases h_p : p.head? = some j
    · rw [if_pos h_p]
      cases h_inner : modified[k']? with
      | none =>
        rw [List.length_cons, walkAndReplace_length j rest modified (k' + 1)]
      | some pair =>
        obtain ⟨q, T'⟩ := pair
        rw [List.length_cons, walkAndReplace_length j rest modified (k' + 1)]
    · rw [if_neg h_p, List.length_cons, walkAndReplace_length j rest modified k']

/-! ### §11.1.7: `absorbInnerPair` equation lemmas + length dichotomy

Equation lemmas for the SET-at-root and descent cases of `absorbInnerPair`,
plus the length dichotomy: result length is `X.length` or `X.length + 1`. -/

private theorem absorbInnerPair_lifted_at_root_eq (outer : List (Path × RoseTree α))
    (i : ℕ) (rest : Path) (c : RoseTree α) (h_lt : i < rootPrependCount outer) :
    absorbInnerPair outer (i :: rest) c =
      (match rootPrependPairIdx outer i with
       | some k => outer.set k.val (outer[k.val].fst, insertAt rest c outer[k.val].snd)
       | none => outer) := by
  conv_lhs => unfold absorbInnerPair
  simp only [if_pos h_lt]

private theorem absorbInnerPair_descent_eq (outer : List (Path × RoseTree α))
    (i : ℕ) (rest : Path) (c : RoseTree α) (h_ge : ¬ i < rootPrependCount outer) :
    absorbInnerPair outer (i :: rest) c =
      liftBackToOuter (descentToChild (i - rootPrependCount outer) outer)
                      (absorbInnerPair (descentToChild (i - rootPrependCount outer) outer) rest c)
                      (i - rootPrependCount outer) outer := by
  conv_lhs => unfold absorbInnerPair
  simp only [if_neg h_ge]

private theorem liftBackToOuter_length (descented modified : List (Path × RoseTree α))
    (j : ℕ) (outer : List (Path × RoseTree α)) :
    (liftBackToOuter descented modified j outer).length =
    (if modified.length = descented.length + 1 then outer.length + 1 else outer.length) := by
  unfold liftBackToOuter
  by_cases h_len : modified.length = descented.length + 1
  · rw [if_pos h_len, if_pos h_len]
    cases h_modified : modified with
    | nil =>
      exfalso
      rw [h_modified] at h_len
      simp at h_len
    | cons head_pair tail =>
      obtain ⟨q, T⟩ := head_pair
      rfl
  · rw [if_neg h_len, if_neg h_len]
    exact walkAndReplace_length j outer modified 0

private theorem absorbInnerPair_nil_eq (X : List (Path × RoseTree α)) (c : RoseTree α) :
    absorbInnerPair X [] c = ([], c) :: X := by
  unfold absorbInnerPair
  rfl

private theorem absorbInnerPair_length_dichotomy :
    ∀ (X : List (Path × RoseTree α)) (p : Path) (c : RoseTree α),
    (absorbInnerPair X p c).length = X.length ∨
    (absorbInnerPair X p c).length = X.length + 1
  | X, [], c => by
    right
    rw [absorbInnerPair_nil_eq]
    rfl
  | X, i :: rest, c => by
    by_cases h_lt : i < rootPrependCount X
    · -- SET case
      left
      rw [absorbInnerPair_lifted_at_root_eq X i rest c h_lt]
      cases h_idx : rootPrependPairIdx X i with
      | none => rfl
      | some k => rw [List.length_set]
    · -- Descent case
      have ih := absorbInnerPair_length_dichotomy
                  (descentToChild (i - rootPrependCount X) X) rest c
      rw [absorbInnerPair_descent_eq X i rest c h_lt]
      rw [liftBackToOuter_length]
      rcases ih with h_eq | h_eq_succ
      · left
        rw [if_neg (by rw [h_eq]; omega)]
      · right
        rw [if_pos h_eq_succ]
termination_by _ p _ => p

/-! ### §11.1.8: `walkAndReplace` and `liftBackToOuter` correctness lemmas -/

/-- Helper: head-test fails for cons whose head ≠ j. -/
private lemma cons_head_ne (p_h j : ℕ) (p_tail : Path) (h : p_h ≠ j) :
    ¬ ((p_h :: p_tail : Path).head? = some j) := by
  intro heq
  apply h
  simp at heq
  exact heq

/-- `walkAndReplace_descentToChild_self_aux`: descent-to-j of the walked outer
    equals `modified.drop k'`, under the length precondition. -/
private theorem walkAndReplace_descentToChild_self_aux (j : ℕ) :
    ∀ (outer modified : List (Path × RoseTree α)) (k' : ℕ),
    modified.length = k' + (descentToChild j outer).length →
    descentToChild j (walkAndReplace j outer modified k') = modified.drop k'
  | [], modified, k', h => by
    show descentToChild j (walkAndReplace j [] modified k') = modified.drop k'
    show descentToChild j [] = modified.drop k'
    rw [descentToChild_nil]
    have h_eq : modified.length = k' := by
      simp only [descentToChild_nil, List.length_nil, Nat.add_zero] at h
      exact h
    exact (List.drop_eq_nil_iff.mpr (le_of_eq h_eq)).symm
  | (p, T) :: rest, modified, k', h => by
    show descentToChild j (walkAndReplace j ((p, T) :: rest) modified k') = modified.drop k'
    unfold walkAndReplace
    by_cases h_p : p.head? = some j
    · -- if branch: p.head? = some j, so p has form j :: p_tail
      rw [if_pos h_p]
      have h_p_form : ∃ p_tail, p = j :: p_tail := by
        cases p with
        | nil => exact absurd h_p (by simp)
        | cons p_h p_tail =>
          have : p_h = j := by simp at h_p; exact h_p
          exact ⟨p_tail, by rw [this]⟩
      obtain ⟨p_tail, h_p_eq⟩ := h_p_form
      subst h_p_eq
      have h_dC_unfold : descentToChild j (((j :: p_tail, T) :: rest) :
                          List (Path × RoseTree α)) =
                         (p_tail, T) :: descentToChild j rest :=
        descentToChild_cons_consPath_eq j p_tail T rest
      rw [h_dC_unfold] at h
      have h_modified_pos : k' < modified.length := by
        rw [h]; simp
      cases h_inner : modified[k']? with
      | none =>
        exfalso
        have := List.getElem?_eq_none_iff.mp h_inner
        omega
      | some pair =>
        obtain ⟨q, T'⟩ := pair
        rw [descentToChild_cons_consPath_eq j q T'
            (walkAndReplace j rest modified (k' + 1))]
        rw [walkAndReplace_descentToChild_self_aux j rest modified (k' + 1)
            (by rw [h, List.length_cons]; omega)]
        have h_get : modified[k']'h_modified_pos = (q, T') := by
          have h_some_eq := List.getElem?_eq_some_iff.mp h_inner
          obtain ⟨_, h_eq_get⟩ := h_some_eq
          exact h_eq_get
        rw [List.drop_eq_getElem_cons h_modified_pos]
        rw [h_get]
    · -- else branch: ¬ p.head? = some j
      rw [if_neg h_p]
      have h_dC_drop : descentToChild j (((p, T) :: walkAndReplace j rest modified k') :
                        List (Path × RoseTree α)) =
                       descentToChild j (walkAndReplace j rest modified k') := by
        cases p with
        | nil => exact descentToChild_cons_nilPath j T (walkAndReplace j rest modified k')
        | cons p_h p_tail =>
          have h_ph_ne : p_h ≠ j := by
            intro h_eq
            apply h_p
            simp [h_eq]
          exact descentToChild_cons_consPath_ne j p_h p_tail T
                  (walkAndReplace j rest modified k') (Ne.symm h_ph_ne)
      rw [h_dC_drop]
      have h_dC_drop_orig : descentToChild j (((p, T) :: rest) :
                              List (Path × RoseTree α)) = descentToChild j rest := by
        cases p with
        | nil => exact descentToChild_cons_nilPath j T rest
        | cons p_h p_tail =>
          have h_ph_ne : p_h ≠ j := by
            intro h_eq
            apply h_p
            simp [h_eq]
          exact descentToChild_cons_consPath_ne j p_h p_tail T rest (Ne.symm h_ph_ne)
      rw [h_dC_drop_orig] at h
      exact walkAndReplace_descentToChild_self_aux j rest modified k' h

private theorem walkAndReplace_descentToChild_self (j : ℕ)
    (outer modified : List (Path × RoseTree α))
    (h : modified.length = (descentToChild j outer).length) :
    descentToChild j (walkAndReplace j outer modified 0) = modified := by
  have := walkAndReplace_descentToChild_self_aux j outer modified 0 (by simp; exact h)
  simpa using this

/-- For `i ≠ j`, descent-to-i of the walked outer equals descent-to-i of original outer. -/
private theorem walkAndReplace_descentToChild_other (i j : ℕ) (h_ij : i ≠ j) :
    ∀ (outer modified : List (Path × RoseTree α)) (k' : ℕ),
    descentToChild i (walkAndReplace j outer modified k') = descentToChild i outer
  | [], _, _ => rfl
  | (p, T) :: rest, modified, k' => by
    show descentToChild i (walkAndReplace j ((p, T) :: rest) modified k') =
         descentToChild i (((p, T) :: rest) : List (Path × RoseTree α))
    unfold walkAndReplace
    by_cases h_p : p.head? = some j
    · -- p has form j :: p_tail
      rw [if_pos h_p]
      have h_p_form : ∃ p_tail, p = j :: p_tail := by
        cases p with
        | nil => exact absurd h_p (by simp)
        | cons p_h p_tail =>
          have : p_h = j := by simp at h_p; exact h_p
          exact ⟨p_tail, by rw [this]⟩
      obtain ⟨p_tail, h_p_eq⟩ := h_p_form
      subst h_p_eq
      cases h_inner : modified[k']? with
      | none =>
        show descentToChild i ((((j :: p_tail, T) :: walkAndReplace j rest modified (k' + 1)) :
              List (Path × RoseTree α))) =
             descentToChild i (((j :: p_tail, T) :: rest) : List (Path × RoseTree α))
        rw [descentToChild_cons_consPath_ne i j p_tail T _ h_ij,
            descentToChild_cons_consPath_ne i j p_tail T rest h_ij]
        exact walkAndReplace_descentToChild_other i j h_ij rest modified (k' + 1)
      | some pair =>
        obtain ⟨q, T'⟩ := pair
        show descentToChild i ((((j :: q, T') :: walkAndReplace j rest modified (k' + 1)) :
              List (Path × RoseTree α))) =
             descentToChild i (((j :: p_tail, T) :: rest) : List (Path × RoseTree α))
        rw [descentToChild_cons_consPath_ne i j q T' _ h_ij,
            descentToChild_cons_consPath_ne i j p_tail T rest h_ij]
        exact walkAndReplace_descentToChild_other i j h_ij rest modified (k' + 1)
    · -- p.head? ≠ some j
      rw [if_neg h_p]
      cases p with
      | nil =>
        rw [descentToChild_cons_nilPath, descentToChild_cons_nilPath]
        exact walkAndReplace_descentToChild_other i j h_ij rest modified k'
      | cons p_h p_tail =>
        have h_ph_ne_j : p_h ≠ j := by
          intro h_eq
          apply h_p
          simp [h_eq]
        by_cases h_ih : i = p_h
        · subst h_ih
          rw [descentToChild_cons_consPath_eq, descentToChild_cons_consPath_eq]
          congr 1
          exact walkAndReplace_descentToChild_other i j h_ij rest modified k'
        · rw [descentToChild_cons_consPath_ne i p_h p_tail T _ h_ih,
              descentToChild_cons_consPath_ne i p_h p_tail T rest h_ih]
          exact walkAndReplace_descentToChild_other i j h_ij rest modified k'

/-- `walkAndReplace` preserves filterMap rootPrependFilter (no empty-fst pairs added). -/
private theorem walkAndReplace_filterMap_rootPrepend (j : ℕ) :
    ∀ (outer modified : List (Path × RoseTree α)) (k' : ℕ),
    (walkAndReplace j outer modified k').filterMap rootPrependFilter =
    outer.filterMap rootPrependFilter
  | [], _, _ => rfl
  | (p, T) :: rest, modified, k' => by
    show (walkAndReplace j ((p, T) :: rest) modified k').filterMap rootPrependFilter =
         (((p, T) :: rest) : List (Path × RoseTree α)).filterMap rootPrependFilter
    unfold walkAndReplace
    by_cases h_p : p.head? = some j
    · rw [if_pos h_p]
      have h_p_form : ∃ p_tail, p = j :: p_tail := by
        cases p with
        | nil => exact absurd h_p (by simp)
        | cons p_h p_tail =>
          have : p_h = j := by simp at h_p; exact h_p
          exact ⟨p_tail, by rw [this]⟩
      obtain ⟨p_tail, h_p_eq⟩ := h_p_form
      subst h_p_eq
      cases h_inner : modified[k']? with
      | none =>
        show ((((j :: p_tail, T) :: walkAndReplace j rest modified (k' + 1)) :
              List (Path × RoseTree α)).filterMap rootPrependFilter) =
             (((j :: p_tail, T) :: rest) : List (Path × RoseTree α)).filterMap rootPrependFilter
        show ((walkAndReplace j rest modified (k' + 1)).filterMap rootPrependFilter) =
             (rest.filterMap rootPrependFilter)
        exact walkAndReplace_filterMap_rootPrepend j rest modified (k' + 1)
      | some pair =>
        obtain ⟨q, T'⟩ := pair
        show ((((j :: q, T') :: walkAndReplace j rest modified (k' + 1)) :
              List (Path × RoseTree α)).filterMap rootPrependFilter) =
             (((j :: p_tail, T) :: rest) : List (Path × RoseTree α)).filterMap rootPrependFilter
        show ((walkAndReplace j rest modified (k' + 1)).filterMap rootPrependFilter) =
             (rest.filterMap rootPrependFilter)
        exact walkAndReplace_filterMap_rootPrepend j rest modified (k' + 1)
    · rw [if_neg h_p]
      cases p with
      | nil =>
        show ((((([], T) :: walkAndReplace j rest modified k') :
              List (Path × RoseTree α)).filterMap rootPrependFilter) =
             ((([], T) :: rest) : List (Path × RoseTree α)).filterMap rootPrependFilter)
        show (T :: (walkAndReplace j rest modified k').filterMap rootPrependFilter) =
             (T :: rest.filterMap rootPrependFilter)
        rw [walkAndReplace_filterMap_rootPrepend j rest modified k']
      | cons p_h p_tail =>
        show ((((p_h :: p_tail, T) :: walkAndReplace j rest modified k') :
              List (Path × RoseTree α)).filterMap rootPrependFilter) =
             (((p_h :: p_tail, T) :: rest) : List (Path × RoseTree α)).filterMap rootPrependFilter
        show ((walkAndReplace j rest modified k').filterMap rootPrependFilter) =
             (rest.filterMap rootPrependFilter)
        exact walkAndReplace_filterMap_rootPrepend j rest modified k'

/-! ### §11.1.9: `liftBackToOuter` structural properties -/

private theorem liftBackToOuter_filterMap_rootPrepend
    (descented modified : List (Path × RoseTree α))
    (j : ℕ) (outer : List (Path × RoseTree α)) :
    (liftBackToOuter descented modified j outer).filterMap rootPrependFilter =
    outer.filterMap rootPrependFilter := by
  unfold liftBackToOuter
  by_cases h_len : modified.length = descented.length + 1
  · rw [if_pos h_len]
    cases h_modified : modified with
    | nil => rfl
    | cons head_pair tail =>
      obtain ⟨q, T⟩ := head_pair
      show ((((j :: q, T) :: outer) : List (Path × RoseTree α)).filterMap rootPrependFilter) =
           outer.filterMap rootPrependFilter
      rfl
  · rw [if_neg h_len]
    exact walkAndReplace_filterMap_rootPrepend j outer modified 0

private theorem liftBackToOuter_descentToChild_other (i : ℕ)
    (descented modified : List (Path × RoseTree α))
    (j : ℕ) (outer : List (Path × RoseTree α)) (h_ij : i ≠ j) :
    descentToChild i (liftBackToOuter descented modified j outer) =
    descentToChild i outer := by
  unfold liftBackToOuter
  by_cases h_len : modified.length = descented.length + 1
  · rw [if_pos h_len]
    cases h_modified : modified with
    | nil => rfl
    | cons head_pair tail =>
      obtain ⟨q, T⟩ := head_pair
      show descentToChild i ((((j :: q, T) :: outer) : List (Path × RoseTree α))) =
           descentToChild i outer
      rw [descentToChild_cons_consPath_ne i j q T outer h_ij]
  · rw [if_neg h_len]
    exact walkAndReplace_descentToChild_other i j h_ij outer modified 0

/-- `absorbInnerPair_prepend_structure`: when length increases by 1 (PREPEND case),
    the result is `head_pair :: X` (some new pair prepended to outer X). -/
private theorem absorbInnerPair_prepend_structure :
    ∀ (X : List (Path × RoseTree α)) (p : Path) (c : RoseTree α),
    (absorbInnerPair X p c).length = X.length + 1 →
    ∃ q T, absorbInnerPair X p c = (q, T) :: X
  | X, [], c, _ => ⟨[], c, absorbInnerPair_nil_eq X c⟩
  | X, i :: rest, c, h => by
    by_cases h_lt : i < rootPrependCount X
    · exfalso
      rw [absorbInnerPair_lifted_at_root_eq X i rest c h_lt] at h
      cases h_idx : rootPrependPairIdx X i with
      | none => rw [h_idx] at h; simp at h
      | some k => rw [h_idx] at h; rw [List.length_set] at h; omega
    · -- Descent case
      have ih := absorbInnerPair_length_dichotomy
                  (descentToChild (i - rootPrependCount X) X) rest c
      rw [absorbInnerPair_descent_eq X i rest c h_lt]
      rw [absorbInnerPair_descent_eq X i rest c h_lt] at h
      rcases ih with h_set | h_prepend
      · -- Inner SET → outer SET → length contradiction
        exfalso
        rw [liftBackToOuter_length] at h
        rw [if_neg (by rw [h_set]; omega)] at h
        omega
      · -- Inner PREPEND → outer PREPEND
        unfold liftBackToOuter
        rw [if_pos h_prepend]
        cases h_modified : absorbInnerPair (descentToChild (i - rootPrependCount X) X) rest c with
        | nil =>
          exfalso
          rw [h_modified] at h_prepend
          simp at h_prepend
        | cons head_pair tail =>
          obtain ⟨q, T⟩ := head_pair
          exact ⟨(i - rootPrependCount X) :: q, T, rfl⟩
termination_by _ p _ _ => p

/-- The key lemma: descent-to-j of `liftBackToOuter` equals `modified`. -/
private theorem liftBackToOuter_descentToChild_self
    (descented modified : List (Path × RoseTree α))
    (j : ℕ) (outer : List (Path × RoseTree α))
    (h_descented_eq : descented = descentToChild j outer)
    (h_modified_struct : modified.length = descented.length + 1 ∨
                         modified.length = descented.length)
    (h_modified_prepend : modified.length = descented.length + 1 →
                          ∃ q T, modified = (q, T) :: descented) :
    descentToChild j (liftBackToOuter descented modified j outer) = modified := by
  unfold liftBackToOuter
  by_cases h_len : modified.length = descented.length + 1
  · -- PREPEND case
    rw [if_pos h_len]
    obtain ⟨q, T, h_modif⟩ := h_modified_prepend h_len
    rw [h_modif]
    show descentToChild j ((((j :: q, T) :: outer) : List (Path × RoseTree α))) =
         (q, T) :: descented
    rw [descentToChild_cons_consPath_eq j q T outer]
    rw [h_descented_eq]
  · -- SET case
    rw [if_neg h_len]
    rcases h_modified_struct with h_succ | h_eq
    · exact absurd h_succ h_len
    · rw [h_descented_eq] at h_eq
      exact walkAndReplace_descentToChild_self j outer modified h_eq

/-! ### §11.2: `composePairs` — full inner-list composition

Composes inner pairs into outer via right-fold (foldr) with transport-based
path re-addressing. Each inner pair `(p, c)` has `p` as a vertex of the original
`mG T outer`; after composing the rest, the position of `p` in
`mG T (composePairs outer rest) = mG (mG T outer) rest` is `transport rest p`.
The re-addressing is essential for the cons-case proof of `multiGraft_compose`.

**Why foldr (not foldl)**: The leftmost inner pair must be absorbed LAST (so that
its empty-path PREPEND ends up FIRST in the result list — matching the planar
order of root prepends in the LHS `mG (mG T outer) inner`). foldl + PREPEND would
reverse inner-order; foldr + PREPEND preserves it. -/

def composePairs : List (Path × RoseTree α) →
    List (Path × RoseTree α) → List (Path × RoseTree α)
  | outer, []           => outer
  | outer, (p, c) :: rest =>
      -- Compose rest first (recursive), then absorb (p, c) with re-addressed path.
      -- The re-addressing `transport rest p` accounts for the position shift of p
      -- when rest is applied to mG T outer (yielding mG T (composePairs outer rest)).
      absorbInnerPair (composePairs outer rest) (transport rest p) c

@[simp] theorem composePairs_nil (outer : List (Path × RoseTree α)) :
    composePairs outer [] = outer := rfl

@[simp] theorem composePairs_cons (outer : List (Path × RoseTree α))
    (p : Path) (c : RoseTree α) (rest : List (Path × RoseTree α)) :
    composePairs outer ((p, c) :: rest) =
      absorbInnerPair (composePairs outer rest) (transport rest p) c := rfl

/-! ### §11.3: `absorbInnerPair_eq_insertAt` — singleton case

The singleton case of `multiGraft_compose`: absorbing one inner pair into outer
gives the same result as inserting at the corresponding position.

```
mG T (absorbInnerPair outer p c) = insertAt p c (mG T outer)
```

This holds (as PLANAR equality, no validity hypothesis) by case analysis on `p`:
- p = []: by `multiGraft_cons_pair` at (T, outer, [], c) — both sides reduce to
  `insertAt [] c (mG T outer)`.
- p = i :: rest, i < N: by `multiGraft_split_lifted_aux` plus the identity
  `liftMulti outer k rest = i :: rest` (which holds via `liftMulti_at_root` +
  `posInGroup_of_rootPrependPairIdx` bridge).
- p = i :: rest, i ≥ N (descent): by recursion on `rest` (smaller path), with
  `liftBackToOuter`'s structural properties (`_filterMap_rootPrepend`,
  `_descentToChild_self`, `_descentToChild_other`) bridging the modified outer
  back to the multiGraft of the original. Invalid descent (j ≥ cs.length) is a
  no-op on both sides. -/

/-- Equation lemma: empty-path case of `absorbInnerPair`. -/
@[simp] theorem absorbInnerPair_nil_path (outer : List (Path × RoseTree α))
    (c : RoseTree α) :
    absorbInnerPair outer [] c = ([], c) :: outer := by
  unfold absorbInnerPair
  rfl

/-- Equation lemma: lifted-at-root case of `absorbInnerPair`. When
    `i < rootPrependCount outer` and `rootPrependPairIdx outer i = some k`,
    the absorb operation modifies `outer[k]` by inserting `c` at `rest` in
    its tree component. -/
private theorem absorbInnerPair_lifted_at_root (outer : List (Path × RoseTree α))
    (i : ℕ) (rest : Path) (c : RoseTree α) (k : Fin outer.length)
    (h_lt : i < rootPrependCount outer)
    (h_idx : rootPrependPairIdx outer i = some k) :
    absorbInnerPair outer (i :: rest) c =
      outer.set k.val (outer[k.val].fst, insertAt rest c outer[k.val].snd) := by
  unfold absorbInnerPair
  simp only [if_pos h_lt, h_idx]

/-- The singleton case of `multiGraft_compose`. Stated unconditionally
    (no validity hypothesis); the empty-path case holds without validity, the
    lifted-at-root case via `multiGraft_split_lifted_aux` + the bridge
    `posInGroup_of_rootPrependPairIdx`, and the descent case via IH on rest +
    `liftBackToOuter` correctness (descentToChild_self/other, filterMap_rootPrepend). -/
theorem absorbInnerPair_eq_insertAt :
    ∀ (T : RoseTree α) (outer : List (Path × RoseTree α)) (p : Path) (c : RoseTree α),
    multiGraft T (absorbInnerPair outer p c) = insertAt p c (multiGraft T outer)
  | T, outer, [], c => by
    -- Empty-path case: by multiGraft_cons_pair + transport_nil_path.
    rw [absorbInnerPair_nil_path, multiGraft_cons_pair, transport_nil_path]
  | T, outer, i :: rest, c => by
    by_cases h_lt : i < rootPrependCount outer
    · -- Lifted-at-root: use rootPrependPairIdx + bridge lemma.
      cases h_idx : rootPrependPairIdx outer i with
      | none =>
        exact absurd h_idx (rootPrependPairIdx_ne_none_of_lt outer i h_lt)
      | some k =>
        rw [absorbInnerPair_lifted_at_root outer i rest c k h_lt h_idx]
        obtain ⟨h_fst, h_pos⟩ := posInGroup_of_rootPrependPairIdx outer i k h_idx
        rw [← multiGraft_split_lifted_aux T outer k rest c]
        rw [liftMulti_at_root outer k h_fst, h_pos]
    · -- Descent: i ≥ rootPrependCount outer.
      rw [absorbInnerPair_descent_eq outer i rest c h_lt]
      cases T with
      | node a cs =>
        rw [multiGraft_node a cs outer]
        rw [multiGraft_node a cs (liftBackToOuter (descentToChild (i - rootPrependCount outer) outer)
              (absorbInnerPair (descentToChild (i - rootPrependCount outer) outer) rest c)
              (i - rootPrependCount outer) outer)]
        set N := rootPrependCount outer with hN_def
        set j := i - N with hj_def
        set descented := descentToChild j outer with hdesc_def
        set modified := absorbInnerPair descented rest c with hmod_def
        set lifted := liftBackToOuter descented modified j outer with hlifted_def
        set rootPrepends := outer.filterMap rootPrependFilter with hRP_def
        have h_rp_eq : lifted.filterMap rootPrependFilter = rootPrepends :=
          liftBackToOuter_filterMap_rootPrepend descented modified j outer
        rw [h_rp_eq]
        have h_rp_len : rootPrepends.length = N := by
          rw [hRP_def, length_filterMap_rootPrependFilter]
        have h_ch_len : ∀ (xs : List (Path × RoseTree α)),
            (multiGraftChildren cs xs).length = cs.length := fun xs =>
          multiGraftChildren_length cs xs
        have h_N_le_i : N ≤ i := Nat.le_of_not_lt h_lt
        have h_i_eq_jN : i = j + N := by rw [hj_def]; omega
        by_cases h_j_lt : j < cs.length
        · -- Valid descent: j < cs.length
          have ih := absorbInnerPair_eq_insertAt (cs[j]'h_j_lt) descented rest c
          -- Show: multiGraftChildren cs lifted = (multiGraftChildren cs outer).set j (multiGraft cs[j] modified)
          have h_mGC : multiGraftChildren cs lifted =
              (multiGraftChildren cs outer).set j (multiGraft (cs[j]'h_j_lt) modified) := by
            apply List.ext_getElem?
            intro idx
            by_cases h_idx_lt : idx < cs.length
            · rw [multiGraftChildren_getElem? cs lifted idx h_idx_lt]
              rw [List.getElem?_set]
              by_cases h_jeq : j = idx
              · subst h_jeq
                rw [if_pos rfl, if_pos (by rw [h_ch_len]; exact h_idx_lt)]
                have h_dC_self :
                    descentToChild j lifted = modified := by
                  rw [hlifted_def]
                  exact liftBackToOuter_descentToChild_self descented modified j outer hdesc_def
                    (Or.symm (absorbInnerPair_length_dichotomy descented rest c))
                    (fun h_len => absorbInnerPair_prepend_structure descented rest c h_len)
                rw [h_dC_self]
              · rw [if_neg h_jeq, multiGraftChildren_getElem? cs outer idx h_idx_lt]
                congr 2
                rw [hlifted_def]
                exact liftBackToOuter_descentToChild_other idx descented modified j outer
                  (Ne.symm h_jeq)
            · push Not at h_idx_lt
              rw [List.getElem?_eq_none (by rw [h_ch_len]; exact h_idx_lt)]
              rw [List.getElem?_eq_none (by rw [List.length_set, h_ch_len]; exact h_idx_lt)]
          rw [h_mGC]
          -- Now RHS: insertAt (i :: rest) c (node a (rootPrepends ++ multiGraftChildren cs outer))
          have h_i_lt_total : i < (rootPrepends ++ multiGraftChildren cs outer).length := by
            rw [List.length_append, h_rp_len, h_ch_len]; omega
          rw [insertAt_cons_of_lt i rest c a (rootPrepends ++ multiGraftChildren cs outer)
                h_i_lt_total]
          have h_N_le_rp : rootPrepends.length ≤ i := by rw [h_rp_len]; exact h_N_le_i
          have h_val :
              (rootPrepends ++ multiGraftChildren cs outer)[i]'h_i_lt_total =
                (multiGraftChildren cs outer)[j]'(by rw [h_ch_len]; exact h_j_lt) := by
            have h_idx_eq : i - rootPrepends.length = j := by
              rw [h_rp_len, hj_def]
            have h_some :
                (rootPrepends ++ multiGraftChildren cs outer)[i]? =
                  some (multiGraft (cs[j]'h_j_lt) descented) := by
              rw [List.getElem?_append_right h_N_le_rp, h_idx_eq]
              exact multiGraftChildren_getElem? cs outer j h_j_lt
            have h_some' :
                (multiGraftChildren cs outer)[j]? = some (multiGraft (cs[j]'h_j_lt) descented) :=
              multiGraftChildren_getElem? cs outer j h_j_lt
            rw [List.getElem?_eq_some_iff] at h_some h_some'
            obtain ⟨_, h_eq⟩ := h_some
            obtain ⟨_, h_eq'⟩ := h_some'
            rw [h_eq, h_eq']
          rw [h_val]
          have h_idx_eq2 : i - rootPrepends.length = j := by
            rw [h_rp_len, hj_def]
          rw [List.set_append_right _ _ h_N_le_rp, h_idx_eq2]
          have h_ch_get :
              (multiGraftChildren cs outer)[j]'(by rw [h_ch_len]; exact h_j_lt) =
                multiGraft (cs[j]'h_j_lt) descented := by
            have h_some := multiGraftChildren_getElem? cs outer j h_j_lt
            rw [List.getElem?_eq_some_iff] at h_some
            obtain ⟨_, h_eq⟩ := h_some
            exact h_eq
          rw [h_ch_get]
          rw [ih]
        · -- Invalid descent: j ≥ cs.length, both sides no-op
          push Not at h_j_lt
          have h_mGC : multiGraftChildren cs lifted = multiGraftChildren cs outer := by
            apply List.ext_getElem?
            intro idx
            by_cases h_idx_lt : idx < cs.length
            · rw [multiGraftChildren_getElem? cs lifted idx h_idx_lt,
                  multiGraftChildren_getElem? cs outer idx h_idx_lt]
              congr 2
              rw [hlifted_def]
              have h_idx_ne_j : idx ≠ j := fun heq => Nat.not_lt.mpr h_j_lt (heq ▸ h_idx_lt)
              exact liftBackToOuter_descentToChild_other idx descented modified j outer h_idx_ne_j
            · push Not at h_idx_lt
              rw [List.getElem?_eq_none (by rw [h_ch_len]; exact h_idx_lt)]
              rw [List.getElem?_eq_none (by rw [h_ch_len]; exact h_idx_lt)]
          rw [h_mGC]
          have h_i_ge : ¬ i < (rootPrepends ++ multiGraftChildren cs outer).length := by
            rw [List.length_append, h_rp_len, h_ch_len]; omega
          rw [insertAt_cons_of_not_lt i rest c a (rootPrepends ++ multiGraftChildren cs outer) h_i_ge]
termination_by _ _ p _ => p

/-! ### §11.4: `multiGraft_compose` — main theorem -/

/-- **Nested multi-graft composition**. Collapses a multi-graft of a multi-graft
    into a single multi-graft of the original host with composed pairs.

    Proof structure: induction on `inner_pairs`. Cons case uses
    `multiGraft_cons_pair` to peel the head, IH to convert the inner mG of T,
    `composePairs_cons` to unfold the RHS, then `absorbInnerPair_eq_insertAt`
    to close.

    Currently depends on `absorbInnerPair_eq_insertAt` (§11.3) being closed. -/
theorem multiGraft_compose
    (T : RoseTree α) (outer_pairs : List (Path × RoseTree α))
    (inner_pairs : List (Path × RoseTree α))
    (_h_outer_valid : ∀ p ∈ outer_pairs, IsValidPath p.fst T)
    (h_inner_valid : ∀ p ∈ inner_pairs,
        IsValidPath p.fst (multiGraft T outer_pairs)) :
    multiGraft (multiGraft T outer_pairs) inner_pairs =
      multiGraft T (composePairs outer_pairs inner_pairs) := by
  induction inner_pairs with
  | nil =>
    rw [multiGraft_nil, composePairs_nil]
  | cons head tail ih =>
    obtain ⟨p, c⟩ := head
    -- Validity hypothesis for IH: tail's pairs are valid in mG T outer_pairs.
    have h_tail_valid : ∀ q ∈ tail, IsValidPath q.fst (multiGraft T outer_pairs) :=
      fun q hq => h_inner_valid q (List.mem_cons_of_mem _ hq)
    -- IH gives us the rest-collapsed equality.
    have h_ih : multiGraft (multiGraft T outer_pairs) tail =
                multiGraft T (composePairs outer_pairs tail) :=
      ih h_tail_valid
    -- Step 1: peel (p, c) from the inner via multiGraft_cons_pair.
    rw [multiGraft_cons_pair (multiGraft T outer_pairs) tail p c]
    -- Step 2: substitute IH into the LHS.
    rw [h_ih]
    -- Step 3: unfold composePairs cons on the RHS.
    rw [composePairs_cons]
    -- Step 4: close via absorbInnerPair_eq_insertAt.
    -- We need: insertAt (transport tail p) c (mG T cp_rest)
    --        = mG T (absorbInnerPair cp_rest (transport tail p) c)
    -- where cp_rest = composePairs outer_pairs tail.
    -- absorbInnerPair_eq_insertAt gives: mG T (absorbInnerPair _ _ _) = insertAt _ _ _
    -- so we use .symm.
    exact (absorbInnerPair_eq_insertAt T (composePairs outer_pairs tail)
              (transport tail p) c).symm

/-! ### §11.5: `liftedInnerAt`, `rootInner` — partition extractors

For an outer pair list and inner pair list (with inner paths valid in
`mG T outer`), the 3-class decomposition (§9 `vertices_multiGraft_decomp`)
classifies each inner path into one of:

- **lifted at outer[k]**: `p = liftMulti outer k q` for some `q`. Recovered
  by `stripLiftMulti outer k p = some q` (§8.10).
- **preserved/sourceSelf**: `p = transport outer v` for some `v ∈ vertices T`.
  Recovered by `untransport outer p = some v` (§8.11).

`liftedInnerAt outer inner k` collects the lifted-at-`k` inner pairs as
`(q, c)` (stripped paths). `rootInner outer inner` collects the
preserved/sourceSelf inner pairs as `(v, c)` (untransported paths).

The deprecated `composePairs` partition theorem that consumed these was
deleted on 2026-06-12 with the A3.3 route; the collectors remain as
generic substrate.

**Consumer status (2026-05-16)**: deprecated. The original consumer
(`InsertionAssoc.lean` §1.11.11 T-bucket bridges) has been deleted as
the project pivoted to the abstract pre-Lie route. These helpers remain
as generic vertex-decomposition primitives; revive if a future basis-
level analysis needs them. -/

/-- Inner pairs lifted at outer[k], with paths stripped to outer[k].snd vertices. -/
noncomputable def liftedInnerAt (outer inner : List (Path × RoseTree α))
    (k : Fin outer.length) : List (Path × RoseTree α) :=
  inner.filterMap fun p => (stripLiftMulti outer k p.fst).map (·, p.snd)

/-- Inner pairs in the preserved/sourceSelf class, with paths
    untransported back to T-coordinates. -/
noncomputable def rootInner (outer inner : List (Path × RoseTree α)) :
    List (Path × RoseTree α) :=
  inner.filterMap fun p => (untransport outer p.fst).map (·, p.snd)

@[simp] theorem liftedInnerAt_nil (outer : List (Path × RoseTree α))
    (k : Fin outer.length) :
    liftedInnerAt outer [] k = [] := rfl

@[simp] theorem rootInner_nil (outer : List (Path × RoseTree α)) :
    rootInner outer [] = [] := rfl

theorem liftedInnerAt_cons (outer : List (Path × RoseTree α))
    (p : Path × RoseTree α) (rest : List (Path × RoseTree α))
    (k : Fin outer.length) :
    liftedInnerAt outer (p :: rest) k =
      ((stripLiftMulti outer k p.fst).map (·, p.snd)).toList ++
      liftedInnerAt outer rest k := by
  unfold liftedInnerAt
  rw [List.filterMap_cons]
  cases hs : stripLiftMulti outer k p.fst with
  | none => simp
  | some _ => simp

theorem rootInner_cons (outer : List (Path × RoseTree α))
    (p : Path × RoseTree α) (rest : List (Path × RoseTree α)) :
    rootInner outer (p :: rest) =
      ((untransport outer p.fst).map (·, p.snd)).toList ++
      rootInner outer rest := by
  unfold rootInner
  rw [List.filterMap_cons]
  cases hu : untransport outer p.fst with
  | none => simp
  | some _ => simp

end Pathed

end RoseTree
