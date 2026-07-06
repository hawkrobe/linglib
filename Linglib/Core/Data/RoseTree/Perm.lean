/-
Copyright (c) 2026 The Linglib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Linglib contributors
-/
import Linglib.Core.Data.RoseTree.Basic
import Linglib.Core.Data.Multiset.Rel

/-!
# Permutation of rose trees

`RoseTree.Perm t s` says the trees agree up to reordering the children of every
vertex — the n-ary tree analogue of `List.Perm`, and the identity criterion of the
unordered quotient (`Nonplanar`, built downstream). Mirroring `List.Perm`,
transitivity is a constructor while reflexivity and symmetry are theorems, and the
list-level companion `PermList` (`List.Perm` with elements compared by `Perm`
instead of `Eq`) is mutually inductive with it, in the `fold`/`foldList` pattern.

## Main declarations

* `RoseTree.Perm`, `RoseTree.PermList`: the mutual permutation relations.
* `RoseTree.isSetoid`: the setoid the nonplanar quotient is taken over.

## Main results

* `RoseTree.permList_iff_rel`: `PermList cs ds ↔ Multiset.Rel Perm (↑cs : Multiset (RoseTree α)) ↑ds` — the
  list companion is `Multiset.Rel` in list clothing, so its theory is inherited.
* `RoseTree.perm_node_iff`: node inversion, `Perm (node a cs) (node b ds) ↔
  a = b ∧ Multiset.Rel Perm (↑cs : Multiset (RoseTree α)) ↑ds`.
-/

namespace RoseTree

variable {α : Type*}

mutual
/-- Two rose trees are equal up to reordering the children of every vertex.
    Transitivity is a constructor (as in `List.Perm`); reflexivity and symmetry
    are theorems. -/
inductive Perm : RoseTree α → RoseTree α → Prop where
  /-- Equal labels over permuted, componentwise-related children. -/
  | node {a : α} {cs ds : List (RoseTree α)} :
      PermList cs ds → Perm (.node a cs) (.node a ds)
  /-- Composition of permutations. -/
  | trans {t s u : RoseTree α} : Perm t s → Perm s u → Perm t u

/-- `List.Perm` with corresponding elements related by `Perm` instead of `Eq`. -/
inductive PermList : List (RoseTree α) → List (RoseTree α) → Prop where
  /-- Empty lists are related. -/
  | nil : PermList [] []
  /-- Related heads over related tails. -/
  | cons {c d : RoseTree α} {cs ds : List (RoseTree α)} :
      Perm c d → PermList cs ds → PermList (c :: cs) (d :: ds)
  /-- Swap the first two elements. -/
  | swap (c d : RoseTree α) (cs : List (RoseTree α)) :
      PermList (d :: c :: cs) (c :: d :: cs)
  /-- Composition of permutations. -/
  | trans {cs ds es : List (RoseTree α)} :
      PermList cs ds → PermList ds es → PermList cs es
end

@[inherit_doc] scoped infixl:50 " ~ " => RoseTree.Perm

/-! ### Equivalence -/

private theorem PermList.refl_of {cs : List (RoseTree α)}
    (h : ∀ c ∈ cs, Perm c c) : PermList cs cs := by
  induction cs with
  | nil => exact .nil
  | cons c cs ih =>
    exact .cons (h c List.mem_cons_self) (ih fun c hc => h c (List.mem_cons_of_mem _ hc))

@[refl] theorem Perm.refl (t : RoseTree α) : Perm t t := by
  induction t with
  | node a cs ih => exact .node (PermList.refl_of ih)

@[refl] theorem PermList.refl (cs : List (RoseTree α)) : PermList cs cs :=
  .refl_of fun c _ => Perm.refl c

mutual
@[symm] theorem Perm.symm : ∀ {t s : RoseTree α}, Perm t s → Perm s t
  | _, _, .node h => .node h.symm
  | _, _, .trans h₁ h₂ => .trans h₂.symm h₁.symm

@[symm] theorem PermList.symm : ∀ {cs ds : List (RoseTree α)}, PermList cs ds → PermList ds cs
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons h.symm hs.symm
  | _, _, .swap c d cs => .swap d c cs
  | _, _, .trans h₁ h₂ => .trans h₂.symm h₁.symm
end

instance : Trans (Perm (α := α)) Perm Perm := ⟨.trans⟩
instance : Trans (PermList (α := α)) PermList PermList := ⟨.trans⟩

protected theorem Perm.eqv : Equivalence (Perm (α := α)) :=
  ⟨.refl, .symm, .trans⟩

/-- The setoid of rose trees up to child reordering; the nonplanar quotient is
    taken over it. -/
instance isSetoid : Setoid (RoseTree α) := ⟨Perm, Perm.eqv⟩

/-! ### Constructors from list-level data -/

/-- Componentwise-related children give related nodes. -/
theorem PermList.of_forall₂ {cs ds : List (RoseTree α)}
    (h : List.Forall₂ Perm cs ds) : PermList cs ds := by
  induction h with
  | nil => exact .nil
  | cons hcd _ ih => exact .cons hcd ih

/-- A plain `List.Perm` of children gives related nodes. -/
theorem PermList.of_perm {cs ds : List (RoseTree α)} (h : cs.Perm ds) :
    PermList cs ds := by
  induction h with
  | nil => exact .nil
  | cons x _ ih => exact .cons (Perm.refl x) ih
  | swap x y l => exact .swap x y l
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A plain `List.Perm` of the children relates the nodes. -/
theorem Perm.node_of_perm {a : α} {cs ds : List (RoseTree α)} (h : cs.Perm ds) :
    Perm (.node a cs) (.node a ds) :=
  .node (.of_perm h)

/-- Componentwise-related children relate the nodes. -/
theorem Perm.node_of_forall₂ {a : α} {cs ds : List (RoseTree α)}
    (h : List.Forall₂ Perm cs ds) : Perm (.node a cs) (.node a ds) :=
  .node (.of_forall₂ h)

/-- Rewriting a single child by a `Perm`-related tree relates the nodes. -/
theorem Perm.congr_child {a : α} (pre post : List (RoseTree α))
    {old new : RoseTree α} (h : Perm old new) :
    Perm (.node a (pre ++ old :: post)) (.node a (pre ++ new :: post)) :=
  .node (.of_forall₂ (List.rel_append
    (List.forall₂_same.mpr fun c _ => Perm.refl c)
    (.cons h (List.forall₂_same.mpr fun c _ => Perm.refl c))))

/-! ### The `Multiset.Rel` characterization -/

private theorem PermList.rel : ∀ {cs ds : List (RoseTree α)}, PermList cs ds →
    Multiset.Rel Perm (↑cs : Multiset (RoseTree α)) ↑ds
  | _, _, .nil => .zero
  | _, _, .cons hcd hs => .cons hcd hs.rel
  | _, _, .swap c d cs => by
    rw [show (↑(d :: c :: cs) : Multiset (RoseTree α)) = ↑(c :: d :: cs) from
      Quot.sound (List.Perm.swap c d cs)]
    exact Multiset.rel_refl_of_refl_on fun t _ => Perm.refl t
  | _, _, .trans h₁ h₂ =>
    Multiset.rel_trans_of_trans_on (fun _ _ _ _ _ _ => Perm.trans) h₁.rel h₂.rel

/-- `PermList` is `Multiset.Rel Perm` in list clothing: its theory is inherited
    from the `Multiset.Rel` API. -/
theorem permList_iff_rel {cs ds : List (RoseTree α)} :
    PermList cs ds ↔ Multiset.Rel Perm (↑cs : Multiset (RoseTree α)) ↑ds := by
  refine ⟨PermList.rel, fun h => ?_⟩
  obtain ⟨ds', hf, hperm⟩ := Multiset.rel_coe_iff_exists.mp h
  exact (PermList.of_forall₂ hf).trans (PermList.of_perm hperm)

private theorem Perm.value_children : ∀ {t s : RoseTree α}, Perm t s →
    t.value = s.value ∧ Multiset.Rel Perm (↑t.children : Multiset (RoseTree α)) ↑s.children
  | _, _, .node h => ⟨rfl, h.rel⟩
  | _, _, .trans h₁ h₂ =>
    ⟨h₁.value_children.1.trans h₂.value_children.1,
     Multiset.rel_trans_of_trans_on (fun _ _ _ _ _ _ => Perm.trans)
       h₁.value_children.2 h₂.value_children.2⟩

/-- Node inversion: related trees have equal labels and `Multiset.Rel`-related
    children. -/
theorem perm_node_iff {a b : α} {cs ds : List (RoseTree α)} :
    Perm (.node a cs) (.node b ds) ↔ a = b ∧ Multiset.Rel Perm (↑cs : Multiset (RoseTree α)) ↑ds := by
  refine ⟨fun h => h.value_children, fun ⟨hab, hrel⟩ => hab ▸ ?_⟩
  exact .node (permList_iff_rel.mpr hrel)

/-- The label is a `Perm`-invariant. -/
theorem Perm.value_eq {t s : RoseTree α} (h : Perm t s) : t.value = s.value :=
  h.value_children.1

/-- The children, up to `Multiset.Rel Perm`, are a `Perm`-invariant. -/
theorem Perm.children_rel {t s : RoseTree α} (h : Perm t s) :
    Multiset.Rel Perm (↑t.children : Multiset (RoseTree α)) ↑s.children :=
  h.value_children.2

/-- Prepending a shared child preserves relatedness of nodes. -/
theorem Perm.cons_child (x : RoseTree α) {a : α} {cs ds : List (RoseTree α)}
    (h : Perm (.node a cs) (.node a ds)) :
    Perm (.node a (x :: cs)) (.node a (x :: ds)) := by
  have hrel := (perm_node_iff.mp h).2
  exact .node (permList_iff_rel.mpr (by
    rw [← Multiset.cons_coe, ← Multiset.cons_coe]
    exact hrel.cons (Perm.refl x)))

/-- `PermList`-related lists have equal length. -/
theorem PermList.length_eq {cs ds : List (RoseTree α)} (h : PermList cs ds) :
    cs.length = ds.length := by
  simpa using Multiset.card_eq_card_of_rel (permList_iff_rel.mp h)

/-- Inversion at singletons: `PermList [c] [d]` is just `Perm c d`. -/
theorem PermList.singleton_inv {c d : RoseTree α} (h : PermList [c] [d]) : Perm c d := by
  obtain ⟨l, hf, hp⟩ := Multiset.rel_coe_iff_exists.mp (permList_iff_rel.mp h)
  rw [List.perm_singleton.mp hp] at hf
  exact (List.forall₂_cons.mp hf).1

/-! ### Functoriality -/

variable {β : Type*}

mutual
/-- `RoseTree.map` preserves `Perm` (cf. `List.Perm.map`). -/
theorem Perm.map (f : α → β) : ∀ {t s : RoseTree α}, Perm t s → Perm (t.map f) (s.map f)
  | _, _, .node h => by
    rw [map_node, map_node]; exact .node (PermList.map f h)
  | _, _, .trans h₁ h₂ => .trans (Perm.map f h₁) (Perm.map f h₂)

/-- `List.map ∘ RoseTree.map` preserves `PermList`. -/
theorem PermList.map (f : α → β) : ∀ {cs ds : List (RoseTree α)}, PermList cs ds →
    PermList (cs.map (RoseTree.map f)) (ds.map (RoseTree.map f))
  | _, _, .nil => .nil
  | _, _, .cons h hs => by
    rw [List.map_cons, List.map_cons]; exact .cons (Perm.map f h) (PermList.map f hs)
  | _, _, .swap c d cs => by
    simp only [List.map_cons]; exact .swap _ _ _
  | _, _, .trans h₁ h₂ => .trans (PermList.map f h₁) (PermList.map f h₂)
end

/-! ### Fold invariance

A `fold` whose algebra is congruent along `Multiset.Rel S` of the folded children
carries `Perm` to `S` (`fold_rel`): the generic dissolver of per-function invariance
inductions, relational so that tree-valued folds descend too. `fold_perm` is the
`S := Eq` case; the counts below are such folds. -/

private theorem rel_refl_coe {β : Type*} {S : β → β → Prop} (hrefl : ∀ b, S b b) :
    ∀ L : List β, Multiset.Rel S ↑L ↑L
  | [] => Multiset.Rel.zero
  | b :: L => Multiset.Rel.cons (hrefl b) (rel_refl_coe hrefl L)

mutual
/-- A `fold` whose algebra is congruent along `Multiset.Rel S` carries `Perm` to any
    reflexive transitive `S`. -/
theorem fold_rel {β : Type*} {S : β → β → Prop} {g : α → List β → β}
    (hrefl : ∀ b, S b b) (htrans : ∀ {b₁ b₂ b₃}, S b₁ b₂ → S b₂ b₃ → S b₁ b₃)
    (hg : ∀ (a : α) {l₁ l₂ : List β}, Multiset.Rel S ↑l₁ ↑l₂ → S (g a l₁) (g a l₂)) :
    ∀ {t s : RoseTree α}, Perm t s → S (fold g t) (fold g s)
  | _, _, .node h => by
    rw [fold_node, fold_node]
    exact hg _ (foldList_rel hrefl htrans hg h)
  | _, _, .trans h₁ h₂ =>
    htrans (fold_rel hrefl htrans hg h₁) (fold_rel hrefl htrans hg h₂)

/-- Folded children of `PermList`-related lists are `Multiset.Rel S`-related. -/
theorem foldList_rel {β : Type*} {S : β → β → Prop} {g : α → List β → β}
    (hrefl : ∀ b, S b b) (htrans : ∀ {b₁ b₂ b₃}, S b₁ b₂ → S b₂ b₃ → S b₁ b₃)
    (hg : ∀ (a : α) {l₁ l₂ : List β}, Multiset.Rel S ↑l₁ ↑l₂ → S (g a l₁) (g a l₂)) :
    ∀ {cs ds : List (RoseTree α)}, PermList cs ds →
      Multiset.Rel S ↑(cs.map (fold g)) ↑(ds.map (fold g))
  | _, _, .nil => Multiset.Rel.zero
  | _, _, .cons h hs => by
    simp only [List.map_cons, ← Multiset.cons_coe]
    exact Multiset.Rel.cons (fold_rel hrefl htrans hg h) (foldList_rel hrefl htrans hg hs)
  | _, _, .swap c d cs => by
    simp only [List.map_cons, ← Multiset.cons_coe]
    rw [Multiset.cons_swap]
    exact Multiset.Rel.cons (hrefl _) (Multiset.Rel.cons (hrefl _) (rel_refl_coe hrefl _))
  | _, _, .trans h₁ h₂ =>
    Multiset.rel_trans_of_trans_on (fun _ _ _ _ _ _ h₁' h₂' => htrans h₁' h₂')
      (foldList_rel hrefl htrans hg h₁) (foldList_rel hrefl htrans hg h₂)
end

/-- A `fold` with a permutation-invariant algebra is `Perm`-invariant. -/
theorem fold_perm {β : Type*} {g : α → List β → β}
    (hg : ∀ (a : α) (l₁ l₂ : List β), l₁.Perm l₂ → g a l₁ = g a l₂) :
    ∀ {t s : RoseTree α}, Perm t s → fold g t = fold g s :=
  fold_rel (fun _ => rfl) (fun h₁ h₂ => h₁.trans h₂)
    (fun a {l₁ l₂} h => hg a l₁ l₂ (Multiset.coe_eq_coe.mp (Multiset.rel_eq.mp h)))

/-- `numNodes` is a `Perm`-invariant (`List.Perm.sum_eq`). -/
theorem numNodes_perm {t s : RoseTree α} (h : Perm t s) : t.numNodes = s.numNodes :=
  fold_perm (fun _ _ _ h' => congrArg (1 + ·) h'.sum_eq) h

/-- `numLeaves` is a `Perm`-invariant. -/
theorem numLeaves_perm {t s : RoseTree α} (h : Perm t s) : t.numLeaves = s.numLeaves :=
  fold_perm (fun _ _ _ h' => congrArg (max 1) h'.sum_eq) h

/-- `depth` is a `Perm`-invariant (`List.Perm.foldr_eq`, `max` being commutative). -/
theorem depth_perm {t s : RoseTree α} (h : Perm t s) : t.depth = s.depth :=
  fold_perm (fun _ _ _ h' => congrArg (1 + ·) (h'.foldr_eq 0)) h

/-- Arity (root child count) is a `Perm`-invariant. -/
theorem arity_perm {t s : RoseTree α} (h : Perm t s) : t.arity = s.arity := by
  simpa [arity] using Multiset.card_eq_card_of_rel h.children_rel

/-- Leaf-ness is a `Perm`-invariant. -/
theorem isLeaf_perm {t s : RoseTree α} (h : Perm t s) : t.isLeaf = s.isLeaf := by
  have harity := arity_perm h
  rw [Bool.eq_iff_iff]
  simp only [isLeaf, List.isEmpty_iff_length_eq_zero]
  unfold arity at harity
  omega

end RoseTree
