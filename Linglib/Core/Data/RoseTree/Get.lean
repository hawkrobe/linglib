/-
Copyright (c) 2026 The Linglib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linglib contributors
-/
import Linglib.Core.Data.RoseTree.Basic

/-!
# Rose tree indexing by Gorn address

Navigation into an n-ary `RoseTree` by a **Gorn address**: a `List ℕ` path of child
indices. `subtreeAt` returns the subtree reached by descending along the path,
`get?` its root value, `getD` with a fallback.

Unlike `BinaryTree.get` (indexed by a `PosNum` left/right path) there is no
`indexOf`: that is a binary-search-tree lookup, which has no analogue for a
general (unordered-search) rose tree. The Gorn path replaces the `PosNum` path,
so this file needs no `Num` dependency.
-/

namespace RoseTree

variable {α : Type*}

/-- The subtree at a **Gorn address** (a path of child indices); `none` if the
path steps outside the tree. -/
def subtreeAt (t : RoseTree α) : List ℕ → Option (RoseTree α)
  | [] => some t
  | i :: rest => t.children[i]?.bind fun c => c.subtreeAt rest

@[simp] theorem subtreeAt_nil (t : RoseTree α) : t.subtreeAt [] = some t := rfl

@[simp] theorem subtreeAt_cons (t : RoseTree α) (i : ℕ) (rest : List ℕ) :
    t.subtreeAt (i :: rest) = t.children[i]?.bind fun c => c.subtreeAt rest := rfl

/-- Gorn composition: descending along `p ++ q` is descending along `p`, then
along `q` from the result. -/
theorem subtreeAt_append (t : RoseTree α) (p q : List ℕ) :
    t.subtreeAt (p ++ q) = (t.subtreeAt p).bind (·.subtreeAt q) := by
  induction p generalizing t with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.cons_append, subtreeAt_cons]
    cases t.children[i]? with
    | none => simp
    | some c => simpa using ih c

/-- The root value at a Gorn address; `none` if the path steps outside the tree. -/
def get? (t : RoseTree α) (path : List ℕ) : Option α :=
  (t.subtreeAt path).map value

/-- The root value at a Gorn address, or `v` if the path is invalid. -/
def getD (t : RoseTree α) (path : List ℕ) (v : α) : α :=
  (t.get? path).getD v

@[simp] theorem get?_nil (t : RoseTree α) : t.get? [] = some t.value := rfl

@[simp] theorem getD_nil (t : RoseTree α) (v : α) : t.getD [] v = t.value := rfl

theorem subtreeAt_cons_eq_some_iff {t s : RoseTree α} {i : ℕ} {p : List ℕ} :
    t.subtreeAt (i :: p) = some s ↔ ∃ c, t.children[i]? = some c ∧ c.subtreeAt p = some s := by
  simp [Option.bind_eq_some_iff]

/-- Relabelling commutes with subtree access. -/
theorem subtreeAt_map {β : Type*} (f : α → β) (t : RoseTree α) (p : List ℕ) :
    (map f t).subtreeAt p = (t.subtreeAt p).map (map f) := by
  induction p generalizing t with
  | nil => rfl
  | cons i p ih =>
    cases t with
    | node a cs =>
      simp only [map_node, subtreeAt_cons, children_node, List.getElem?_map]
      cases cs[i]? with
      | none => rfl
      | some c => simp [ih]

/-- Every prefix of an address inside the tree is inside the tree. -/
theorem subtreeAt_take_isSome {t s : RoseTree α} {p : List ℕ} (h : t.subtreeAt p = some s)
    (k : ℕ) : (t.subtreeAt (p.take k)).isSome := by
  rw [← List.take_append_drop k p, subtreeAt_append] at h
  cases hk : t.subtreeAt (p.take k) with
  | none => rw [hk] at h; simp at h
  | some _ => rfl

/-! ### Height and size along addresses -/

private theorem le_foldr_max_of_mem {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

private theorem foldr_max_le {l : List ℕ} {m : ℕ} (h : ∀ x ∈ l, x ≤ m) : l.foldr max 0 ≤ m := by
  induction l with
  | nil => exact Nat.zero_le m
  | cons y l ih =>
    exact Nat.max_le.2 ⟨h y (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)⟩

private theorem exists_mem_eq_foldr_max {l : List ℕ} (h : l ≠ []) : ∃ x ∈ l, x = l.foldr max 0 := by
  induction l with
  | nil => exact absurd rfl h
  | cons y l ih =>
    cases l with
    | nil => exact ⟨y, List.mem_cons_self .., (Nat.max_eq_left (Nat.zero_le y)).symm⟩
    | cons z l =>
      obtain ⟨x, hx, hxe⟩ := ih (List.cons_ne_nil z l)
      rw [List.foldr_cons, ← hxe]
      rcases Nat.le_total y x with hyx | hxy
      · exact ⟨x, List.mem_cons_of_mem _ hx, (Nat.max_eq_right hyx).symm⟩
      · exact ⟨y, List.mem_cons_self .., (Nat.max_eq_left hxy).symm⟩

private theorem le_sum_of_mem {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih h) (Nat.le_add_left _ _)

theorem height_lt_of_mem {t c : RoseTree α} (h : c ∈ t.children) : c.height < t.height := by
  cases t with
  | node a cs =>
    rw [height_node]
    exact le_foldr_max_of_mem (List.mem_map_of_mem (List.mem_map_of_mem h))

/-- A node of positive height has a child one shorter. -/
theorem exists_mem_children_height_add_one {t : RoseTree α} (h : 0 < t.height) :
    ∃ c ∈ t.children, c.height + 1 = t.height := by
  cases t with
  | node a cs =>
    rw [height_node] at h ⊢
    have hcs : cs ≠ [] := by rintro rfl; simp at h
    obtain ⟨x, hx, hxe⟩ := exists_mem_eq_foldr_max
      (l := (cs.map height).map (· + 1)) (by simpa using hcs)
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    exact ⟨c, hc, hxe⟩

/-- A maximal descent of length `k` from a tree of height at least `k`: the subtree at the
prefix of length `i` has height `t.height - i`. -/
theorem exists_subtreeAt_height_sub (t : RoseTree α) (k : ℕ) (hk : k ≤ t.height) :
    ∃ p : List ℕ, p.length = k ∧
      ∀ i ≤ k, ∃ s, t.subtreeAt (p.take i) = some s ∧ s.height = t.height - i := by
  induction k generalizing t with
  | zero =>
    exact ⟨[], rfl, fun i hi => by obtain rfl := Nat.le_zero.mp hi; exact ⟨t, rfl, by simp⟩⟩
  | succ k ih =>
    obtain ⟨c, hc, hch⟩ := exists_mem_children_height_add_one (Nat.lt_of_lt_of_le k.succ_pos hk)
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    obtain ⟨p, hp, hsub⟩ := ih c (by omega)
    refine ⟨j :: p, by simp [hp], fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨t, rfl, by simp⟩
    | succ i =>
      obtain ⟨s, hs, hsh⟩ := hsub i (Nat.le_of_succ_le_succ hi)
      exact ⟨s, by simp only [List.take_succ_cons, subtreeAt_cons, hj, Option.bind_some, hs],
        by omega⟩

theorem numNodes_lt_of_mem {t c : RoseTree α} (h : c ∈ t.children) : c.numNodes < t.numNodes := by
  cases t with
  | node a cs =>
    rw [children_node] at h
    rw [numNodes_node]
    have := le_sum_of_mem (List.mem_map_of_mem (f := numNodes) h)
    omega

theorem numNodes_le_of_subtreeAt {t s : RoseTree α} {p : List ℕ} (h : t.subtreeAt p = some s) :
    s.numNodes ≤ t.numNodes := by
  induction p generalizing t with
  | nil => exact (Option.some.inj h).symm ▸ Nat.le_refl _
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp h
    exact Nat.le_trans (ih hcs) (Nat.le_of_lt (numNodes_lt_of_mem (List.mem_of_getElem? hc)))

theorem numNodes_lt_of_subtreeAt_cons {t s : RoseTree α} {i : ℕ} {p : List ℕ}
    (h : t.subtreeAt (i :: p) = some s) : s.numNodes < t.numNodes := by
  obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp h
  exact Nat.lt_of_le_of_lt (numNodes_le_of_subtreeAt hcs)
    (numNodes_lt_of_mem (List.mem_of_getElem? hc))

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
theorem value_replaceAt {t s : RoseTree α} {p : List ℕ} (h : t.subtreeAt p = some s)
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
  rw [List.set_eq_take_append_cons_drop, if_pos (List.getElem?_eq_some_iff.mp hc).1]

/-- Replacing inside the tree splits the frontier into the leaves left of the address, the
frontier of the subtree there, and the leaves to its right. -/
theorem leafList_replaceAt {t s : RoseTree α} {p : List ℕ} (h : t.subtreeAt p = some s) :
    ∃ pre post : List α, t.leafList = pre ++ s.leafList ++ post ∧
      ∀ new : RoseTree α, (t.replaceAt p new).leafList = pre ++ new.leafList ++ post := by
  induction p generalizing t with
  | nil => exact ⟨[], [], by simp [Option.some.inj h], fun new => by simp⟩
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp h
    obtain ⟨pre, post, hy, hy'⟩ := ih hcs
    cases t with
    | node a cs =>
      rw [children_node] at hc
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
theorem numNodes_replaceAt_lt {t s : RoseTree α} {p : List ℕ} (h : t.subtreeAt p = some s)
    {new : RoseTree α} (hlt : new.numNodes < s.numNodes) :
    (t.replaceAt p new).numNodes < t.numNodes := by
  induction p generalizing t with
  | nil => rw [replaceAt_nil, Option.some.inj h]; exact hlt
  | cons i p ih =>
    obtain ⟨c, hc, hcs⟩ := subtreeAt_cons_eq_some_iff.mp h
    cases t with
    | node a cs =>
      rw [children_node] at hc
      rw [replaceAt_cons_of_getElem? (by simpa using hc), value_node, children_node,
        set_eq_take_append_cons_drop hc, numNodes_node]
      conv_rhs => rw [eq_take_append_cons_drop hc, numNodes_node]
      simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
      have := ih hcs
      omega

end RoseTree
