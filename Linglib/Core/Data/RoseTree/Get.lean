/-
Copyright (c) 2026 The Linglib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linglib contributors
-/
module

public import Linglib.Core.Data.RoseTree.Basic
public import Linglib.Core.Order.Branching
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Nodup

/-!
# Rose trees under Gorn addresses

A `RoseTree` is a `Branching` carrier, so `Branching.subtreeAt` navigates it by a **Gorn
address**, a `List ℕ` path of child indices. This file states what the concrete tree adds:
relabelling commutes with navigation, a subtree is no larger than its tree, a tree of height
above `k` descends `k` steps, `vertices` enumerates the addresses, and `replaceAt` replaces the
subtree at an address.

Unlike `BinaryTree.get` (indexed by a `PosNum` left/right path) there is no `indexOf`: that is
a binary-search-tree lookup, which has no analogue for a general rose tree.

## Main declarations

* `RoseTree.subtreeAt_map`: relabelling commutes with navigation.
* `RoseTree.exists_subtreeAt_height_sub`: a maximal descent from a tree of height above `k`.
* `RoseTree.numNodes_le_of_subtreeAt`: a subtree is no larger than its tree.
* `RoseTree.isSubtree_node_iff`, `Branching.IsSubtree.antisymm`: the subtree relation of
  `Branching.IsSubtree` on rose trees, a partial order with a decision procedure the kernel
  evaluates.
* `RoseTree.vertices`: the addresses in preorder, one per vertex (`length_vertices`,
  `nodup_vertices`) and exactly those inside the tree (`mem_vertices`).
* `RoseTree.replaceAt`: replacement at an address, splitting the frontier
  (`leafList_replaceAt`) and shrinking the tree when the new subtree is smaller
  (`numNodes_replaceAt_lt`).
-/

@[expose] public section

namespace RoseTree

open Core.Order Core.Order.Branching

variable {α : Type*}

instance : Branching (RoseTree α) := ⟨children⟩

@[simp] theorem branching_children (t : RoseTree α) : Branching.children t = t.children := rfl

/-- Relabelling commutes with subtree access. -/
theorem subtreeAt_map {β : Type*} (f : α → β) (t : RoseTree α) (p : List ℕ) :
    subtreeAt (map f t) p = (subtreeAt t p).map (map f) :=
  subtreeAt_map_of_children_map (fun t => by cases t; simp) t p

/-! ### Height and size along addresses -/

/-- A node of height above `1` has a child one shorter. -/
theorem exists_mem_children_height_add_one {t : RoseTree α} (h : 1 < t.height) :
    ∃ c ∈ t.children, c.height + 1 = t.height := by
  cases t with
  | node a cs =>
    rw [height_node] at h ⊢
    have hcs : cs ≠ [] := by rintro rfl; simp at h
    obtain ⟨c, hc, hce⟩ := List.mem_map.mp (List.maximum_mem
      (List.foldr_max_of_ne_nil (l := cs.map height) (by simpa using hcs)).symm)
    exact ⟨c, hc, by rw [hce]; rfl⟩

/-- A tree of height above `k` has a maximal descent of length `k`, along which the subtree at
the prefix of length `i` has height `t.height - i`. -/
theorem exists_subtreeAt_height_sub (t : RoseTree α) (k : ℕ) (hk : k < t.height) :
    ∃ p : List ℕ, p.length = k ∧
      ∀ i ≤ k, ∃ s, subtreeAt t (p.take i) = some s ∧ s.height = t.height - i := by
  induction k generalizing t with
  | zero =>
    exact ⟨[], rfl, fun i hi => by obtain rfl := Nat.le_zero.mp hi; exact ⟨t, rfl, by simp⟩⟩
  | succ k ih =>
    obtain ⟨c, hc, hch⟩ := exists_mem_children_height_add_one
      (Nat.lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le k)) hk)
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    obtain ⟨p, hp, hsub⟩ := ih c (by omega)
    refine ⟨j :: p, by simp [hp], fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨t, rfl, by simp⟩
    | succ i =>
      obtain ⟨s, hs, hsh⟩ := hsub i (Nat.le_of_succ_le_succ hi)
      exact ⟨s, by simp only [List.take_succ_cons, subtreeAt_cons, branching_children, hj,
        Option.bind_some, hs], by omega⟩

theorem numNodes_lt_of_mem {t c : RoseTree α} (h : c ∈ t.children) : c.numNodes < t.numNodes := by
  cases t with
  | node a cs =>
    rw [children_node] at h
    rw [numNodes_node]
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := numNodes) h)
    omega

theorem numNodes_le_of_subtreeAt {t s : RoseTree α} {p : List ℕ} (h : subtreeAt t p = some s) :
    s.numNodes ≤ t.numNodes := by
  induction p generalizing t with
  | nil => exact (Option.some.inj h).symm ▸ Nat.le_refl _
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp h
    exact Nat.le_trans (ih hcs) (Nat.le_of_lt (numNodes_lt_of_mem (List.mem_of_getElem? hc)))

theorem numNodes_lt_of_subtreeAt_cons {t s : RoseTree α} {i : ℕ} {p : List ℕ}
    (h : subtreeAt t (i :: p) = some s) : s.numNodes < t.numNodes := by
  obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp h
  exact Nat.lt_of_le_of_lt (numNodes_le_of_subtreeAt hcs)
    (numNodes_lt_of_mem (List.mem_of_getElem? hc))

/-! ### Subtrees -/

theorem isSubtree_node_iff {s : RoseTree α} {a : α} {cs : List (RoseTree α)} :
    IsSubtree s (node a cs) ↔ s = node a cs ∨ ∃ c ∈ cs, IsSubtree s c := by
  rw [IsSubtree, Relation.ReflTransGen.cases_tail_iff]
  simp only [IsChild, branching_children, children_node, eq_comm (a := node a cs)]
  exact or_congr_right ⟨fun ⟨c, h, hc⟩ ↦ ⟨c, hc, h⟩, fun ⟨c, hc, h⟩ ↦ ⟨c, h, hc⟩⟩

@[simp] theorem isSubtree_leaf_iff {s : RoseTree α} {a : α} :
    IsSubtree s (leaf a) ↔ s = leaf a := by
  simp [isSubtree_node_iff]

/-- A subtree is no larger than its tree. -/
theorem _root_.Core.Order.Branching.IsSubtree.numNodes_le {s t : RoseTree α}
    (h : IsSubtree s t) : s.numNodes ≤ t.numNodes :=
  let ⟨_, hp⟩ := isSubtree_iff_exists_subtreeAt.1 h; numNodes_le_of_subtreeAt hp

/-- A subtree as large as its tree is the tree. -/
theorem _root_.Core.Order.Branching.IsSubtree.eq_of_numNodes_le {s t : RoseTree α}
    (h : IsSubtree s t) (hn : t.numNodes ≤ s.numNodes) : s = t := by
  obtain ⟨_ | ⟨i, p⟩, hp⟩ := isSubtree_iff_exists_subtreeAt.1 h
  · exact (Option.some.inj hp).symm
  · exact absurd hn (not_le.2 (numNodes_lt_of_subtreeAt_cons hp))

theorem _root_.Core.Order.Branching.IsSubtree.antisymm {s t : RoseTree α}
    (h₁ : IsSubtree s t) (h₂ : IsSubtree t s) : s = t :=
  h₁.eq_of_numNodes_le h₂.numNodes_le

section DecidableIsSubtree
variable [DecidableEq α]

mutual
/-- Structural decision procedure for `IsSubtree`, which the kernel can evaluate. -/
protected def decIsSubtree (s : RoseTree α) : (t : RoseTree α) → Decidable (IsSubtree s t)
  | node a cs =>
    if h : s = node a cs then .isTrue (h ▸ .refl _)
    else
      match RoseTree.decIsSubtreeList s cs with
      | .isTrue hex => .isTrue (isSubtree_node_iff.2 (.inr hex))
      | .isFalse hno => .isFalse fun hc ↦ (isSubtree_node_iff.1 hc).elim h hno

/-- Decides whether some tree of `cs` has `s` as a subtree. -/
protected def decIsSubtreeList (s : RoseTree α) :
    (cs : List (RoseTree α)) → Decidable (∃ c ∈ cs, IsSubtree s c)
  | [] => .isFalse fun ⟨_, hmem, _⟩ ↦ by cases hmem
  | c :: cs =>
    match RoseTree.decIsSubtree s c with
    | .isTrue hc => .isTrue ⟨c, List.mem_cons_self .., hc⟩
    | .isFalse hc =>
      match RoseTree.decIsSubtreeList s cs with
      | .isTrue hex =>
        .isTrue (have ⟨d, hmem, hd⟩ := hex; ⟨d, List.mem_cons_of_mem _ hmem, hd⟩)
      | .isFalse hno => .isFalse fun ⟨d, hmem, hd⟩ ↦ by
          cases hmem with
          | head => exact hc hd
          | tail _ hmem => exact hno ⟨d, hmem, hd⟩
end

instance (s t : RoseTree α) : Decidable (IsSubtree s t) := RoseTree.decIsSubtree s t

end DecidableIsSubtree

/-! ### Enumerating the addresses -/

mutual
/-- `vertices t` lists the addresses of the vertices of `t` in preorder, the root `[]` first. -/
def vertices : RoseTree α → List (List ℕ)
  | node _ cs => [] :: verticesList cs
/-- `verticesList cs` lists the addresses of the vertices of the forest `cs`, each starting with
the index of its tree. -/
def verticesList : List (RoseTree α) → List (List ℕ)
  | [] => []
  | c :: cs => (vertices c).map (0 :: ·) ++ (verticesList cs).map (List.modifyHead (· + 1))
end

@[simp] theorem vertices_node (a : α) (cs : List (RoseTree α)) :
    vertices (node a cs) = [] :: verticesList cs := rfl

@[simp] theorem verticesList_nil : verticesList ([] : List (RoseTree α)) = [] := rfl

@[simp] theorem verticesList_cons (c : RoseTree α) (cs : List (RoseTree α)) :
    verticesList (c :: cs) =
      (vertices c).map (0 :: ·) ++ (verticesList cs).map (List.modifyHead (· + 1)) := rfl

theorem mem_verticesList {cs : List (RoseTree α)} {p : List ℕ} :
    p ∈ verticesList cs ↔ ∃ j q c, p = j :: q ∧ cs[j]? = some c ∧ q ∈ vertices c := by
  induction cs generalizing p with
  | nil => simp
  | cons c cs ih =>
    rw [verticesList_cons, List.mem_append, List.mem_map, List.mem_map]
    constructor
    · rintro (⟨q, hq, rfl⟩ | ⟨p', hp', rfl⟩)
      · exact ⟨0, q, c, rfl, rfl, hq⟩
      · obtain ⟨j, q, d, rfl, hd, hq⟩ := ih.mp hp'
        exact ⟨j + 1, q, d, rfl, hd, hq⟩
    · rintro ⟨_ | j, q, d, rfl, hd, hq⟩
      · exact .inl ⟨q, Option.some.inj hd ▸ hq, rfl⟩
      · exact .inr ⟨j :: q, ih.mpr ⟨j, q, d, rfl, hd, hq⟩, rfl⟩

theorem exists_cons_of_mem_verticesList {cs : List (RoseTree α)} {p : List ℕ}
    (hp : p ∈ verticesList cs) : ∃ j q, p = j :: q := by
  obtain ⟨j, q, -, rfl, -⟩ := mem_verticesList.mp hp
  exact ⟨j, q, rfl⟩

/-- The addresses listed by `vertices t` are exactly the addresses inside `t`. -/
theorem mem_vertices {t : RoseTree α} {p : List ℕ} :
    p ∈ t.vertices ↔ (subtreeAt t p).isSome := by
  induction t generalizing p with
  | node a cs ih =>
    rcases p with _ | ⟨j, q⟩
    · simp
    · simp only [vertices_node, List.mem_cons, reduceCtorEq, false_or, mem_verticesList,
        List.cons.injEq, subtreeAt_cons, branching_children, children_node]
      constructor
      · rintro ⟨_, _, c, ⟨rfl, rfl⟩, hc, hq⟩
        rw [hc, Option.bind_some]
        exact (ih c (List.mem_of_getElem? hc)).mp hq
      · intro h
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind h)
        rw [hc, Option.bind_some] at h
        exact ⟨j, q, c, ⟨rfl, rfl⟩, hc, (ih c (List.mem_of_getElem? hc)).mpr h⟩

mutual
theorem length_vertices : ∀ t : RoseTree α, t.vertices.length = t.numNodes
  | node _ cs => by rw [vertices_node, List.length_cons, length_verticesList cs, numNodes_node]
theorem length_verticesList : ∀ cs : List (RoseTree α),
    (verticesList cs).length = (cs.map numNodes).sum
  | [] => rfl
  | c :: cs => by
    rw [verticesList_cons, List.length_append, List.length_map, List.length_map,
      length_vertices c, length_verticesList cs, List.map_cons, List.sum_cons]
end

private theorem modifyHead_succ_injective : Function.Injective (List.modifyHead (· + 1)) := by
  rintro (_ | ⟨a, l⟩) (_ | ⟨b, m⟩) h <;> simp_all

mutual
theorem nodup_vertices : ∀ t : RoseTree α, t.vertices.Nodup
  | node _ cs => by
    rw [vertices_node, List.nodup_cons]
    refine ⟨fun h => ?_, nodup_verticesList cs⟩
    obtain ⟨_, _, h⟩ := exists_cons_of_mem_verticesList h
    exact List.cons_ne_nil _ _ h.symm
theorem nodup_verticesList : ∀ cs : List (RoseTree α), (verticesList cs).Nodup
  | [] => List.nodup_nil
  | c :: cs => by
    rw [verticesList_cons, List.nodup_append]
    refine ⟨List.Nodup.map List.cons_injective (nodup_vertices c),
      List.Nodup.map modifyHead_succ_injective (nodup_verticesList cs), ?_⟩
    rintro _ hp _ hq rfl
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
    obtain ⟨p', hp', h⟩ := List.mem_map.mp hq
    obtain ⟨j, q', rfl⟩ := exists_cons_of_mem_verticesList hp'
    simp at h
end

/-! ### Replacement at an address -/

/-- Replace the subtree at a Gorn address; an address outside the tree leaves it unchanged. -/
def replaceAt : RoseTree α → List ℕ → RoseTree α → RoseTree α
  | _, [], new => new
  | node a cs, i :: p, new => node a (cs.modify i (·.replaceAt p new))

@[simp] theorem replaceAt_nil (t new : RoseTree α) : t.replaceAt [] new = new := by
  cases t; rfl

theorem replaceAt_cons (a : α) (cs : List (RoseTree α)) (i : ℕ) (p : List ℕ)
    (new : RoseTree α) :
    (node a cs).replaceAt (i :: p) new = node a (cs.modify i (·.replaceAt p new)) := rfl

@[simp] theorem value_replaceAt_cons (t : RoseTree α) (i : ℕ) (p : List ℕ) (new : RoseTree α) :
    (t.replaceAt (i :: p) new).value = t.value := by
  cases t; rfl

/-- Replacing a subtree by one with the same root value keeps the root value. -/
theorem value_replaceAt {t s : RoseTree α} {p : List ℕ} (h : subtreeAt t p = some s)
    {new : RoseTree α} (hv : new.value = s.value) : (t.replaceAt p new).value = t.value := by
  cases p with
  | nil => rw [replaceAt_nil, hv, Option.some.inj h]
  | cons i p => exact value_replaceAt_cons t i p new

theorem replaceAt_cons_of_getElem? {t c : RoseTree α} {i : ℕ} (hc : t.children[i]? = some c)
    (p : List ℕ) (new : RoseTree α) :
    t.replaceAt (i :: p) new = node t.value (t.children.set i (c.replaceAt p new)) := by
  cases t with
  | node a cs =>
    have : Inhabited (RoseTree α) := ⟨c⟩
    rw [children_node] at hc
    rw [replaceAt_cons, List.modify_eq_set, hc, Option.getD_some, value_node, children_node]

private theorem eq_take_append_cons_drop {cs : List (RoseTree α)} {i : ℕ} {c : RoseTree α}
    (hc : cs[i]? = some c) : cs = cs.take i ++ c :: cs.drop (i + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]

private theorem set_eq_take_append_cons_drop {cs : List (RoseTree α)} {i : ℕ} {c : RoseTree α}
    (hc : cs[i]? = some c) (x : RoseTree α) : cs.set i x = cs.take i ++ x :: cs.drop (i + 1) := by
  rw [List.set_eq_take_append_cons_drop, ite_eq_left (List.getElem?_eq_some_iff.mp hc).1]

/-- Replacing inside the tree splits the frontier into the leaves left of the address, the
frontier of the subtree there, and the leaves to its right. -/
theorem leafList_replaceAt {t s : RoseTree α} {p : List ℕ} (h : subtreeAt t p = some s) :
    ∃ pre post : List α, t.leafList = pre ++ s.leafList ++ post ∧
      ∀ new : RoseTree α, (t.replaceAt p new).leafList = pre ++ new.leafList ++ post := by
  induction p generalizing t with
  | nil => exact ⟨[], [], by simp [Option.some.inj h], fun new => by simp⟩
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp h
    obtain ⟨pre, post, hy, hy'⟩ := ih hcs
    cases t with
    | node a cs =>
      rw [branching_children, children_node] at hc
      refine ⟨((cs.take i).map leafList).flatten ++ pre,
        post ++ ((cs.drop (i + 1)).map leafList).flatten, ?_, fun new => ?_⟩
      · conv_lhs => rw [eq_take_append_cons_drop hc]
        rw [leafList_node_of_ne_nil _ (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
          List.map_append, List.map_cons, List.flatten_append, List.flatten_cons, hy]
        simp only [List.append_assoc]
      · rw [replaceAt_cons_of_getElem? (by simpa using hc), value_node, children_node,
          set_eq_take_append_cons_drop hc,
          leafList_node_of_ne_nil _ (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)),
          List.map_append, List.map_cons, List.flatten_append, List.flatten_cons, hy']
        simp only [List.append_assoc]

/-- Replacing a subtree by a strictly smaller one shrinks the tree. -/
theorem numNodes_replaceAt_lt {t s : RoseTree α} {p : List ℕ} (h : subtreeAt t p = some s)
    {new : RoseTree α} (hlt : new.numNodes < s.numNodes) :
    (t.replaceAt p new).numNodes < t.numNodes := by
  induction p generalizing t with
  | nil => rw [replaceAt_nil, Option.some.inj h]; exact hlt
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp h
    cases t with
    | node a cs =>
      rw [branching_children, children_node] at hc
      rw [replaceAt_cons_of_getElem? (by simpa using hc), value_node, children_node,
        set_eq_take_append_cons_drop hc, numNodes_node]
      conv_rhs => rw [eq_take_append_cons_drop hc, numNodes_node]
      simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      have := ih hcs
      omega

end RoseTree
