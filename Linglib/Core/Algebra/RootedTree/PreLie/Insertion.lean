/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Graft
import Linglib.Core.Algebra.RootedTree.PreLie.InsertSum
import Linglib.Core.Data.List.Perm
import Linglib.Core.Data.List.Sublists
import Linglib.Core.Data.Multiset.Powerset
import Linglib.Core.Data.UnorderedTree.Basic
import Mathlib.Data.Multiset.Bind

/-!
# Multi-tree insertion on `RoseTree α`

Foissy's multi-tree, multi-vertex insertion: `insertion T gs` sums, over all assignments of the
guests `gs` to vertices of the host `T`, the simultaneous graft `multiGraft`; `insertionForest`
is the same sum over the vertices of a host forest. Both are multisets so that the sum over
assignments is commutative.

## Main results

* `bind_listChoices_filter`: the keystone. A sum over vertex assignments, viewed through a
  predicate on vertices, is a sum over `gs.sublists'.revzip` of independent assignments for the
  two buckets. `insertionForest_cons`, `insertionForest_append`, and `insertion_node` are its
  instances.
* `bind_listChoices_zip_perm`: permuting the guests permutes the assignments, so `insertion` and
  `insertionForest` are invariant under guest permutation once outputs are read through
  `UnorderedTree.mk`.
* `insertion_perm_host`, `insertionForest_permList_host_msform`,
  `insertionForest_perm_host_msform`, `insertionForest_msform_invariance_guests`: the
  invariances that make `UnorderedTree.insertionMultiset` well defined.
* `insertion_singleton`: with a single guest, insertion is the pre-Lie product `insertSum`.

## References

* [foissy-typed-decorated-rooted-trees-2018]
* [foissy-introduction-hopf-algebras-trees]
-/

namespace RoseTree

namespace Pathed

open RoseTree UnorderedTree

variable {α : Type*}

/-! ## `listChoices`: assignments of guests to vertices -/

/-- All length-`n` lists with entries from `xs`, with repetition: the assignments of `n`
    guests to the vertices `xs`. -/
def listChoices {β : Type*} : List β → Nat → List (List β)
  | _,  0     => [[]]
  | xs, n + 1 => xs.flatMap fun v => (listChoices xs n).map (v :: ·)

@[simp] theorem listChoices_zero {β : Type*} (xs : List β) :
    listChoices xs 0 = [[]] := rfl

@[simp] theorem listChoices_succ {β : Type*} (xs : List β) (n : Nat) :
    listChoices xs (n + 1) =
      xs.flatMap fun v => (listChoices xs n).map (v :: ·) := rfl

theorem coe_listChoices_succ {β : Type*} (xs : List β) (n : ℕ) :
    (listChoices xs (n + 1) : Multiset (List β)) =
      (xs : Multiset β).bind fun v => (listChoices xs n : Multiset (List β)).map (v :: ·) := by
  rw [listChoices_succ, ← Multiset.coe_bind]
  rfl

@[simp] theorem listChoices_singleton {β : Type*} (x : β) (n : ℕ) :
    listChoices [x] n = [List.replicate n x] := by
  induction n with
  | zero => rfl
  | succ n ih => rw [listChoices_succ, ih]; rfl

/-- A choice is a word of the prescribed length over the alphabet. -/
theorem mem_listChoices {β : Type*} {xs : List β} {n : ℕ} {ch : List β} :
    ch ∈ listChoices xs n ↔ ch.length = n ∧ ∀ x ∈ ch, x ∈ xs := by
  induction n generalizing ch with
  | zero => cases ch <;> simp
  | succ n ih =>
    cases ch with
    | nil => simp
    | cons x ch => simp [ih, and_left_comm]

/-- `listChoices` is compatible with `List.map`: applying `f` element-wise
    to choices in `xs.map f` gives the same as mapping `List.map f` over
    `listChoices xs n`. -/
theorem listChoices_map {β γ : Type*} (f : β → γ) (xs : List β) (n : Nat) :
    listChoices (xs.map f) n = (listChoices xs n).map (List.map f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [listChoices_succ, listChoices_succ]
    -- (xs.map f).flatMap (fun v => listChoices (xs.map f) n .map (v :: ·)) =
    -- (xs.flatMap (fun v => listChoices xs n .map (v :: ·))).map (List.map f)
    rw [List.flatMap_map]
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro b _
    rw [ih]
    rw [List.map_map, List.map_map]
    rfl

/-! ### Guest splits as `sublists'.revzip` -/

/-- **Keystone.** A sum over length-`gs.length` choices from `xs`, viewed through the two
buckets of a predicate `P` on `xs`, is a sum over `gs.sublists'.revzip` of independent choices
from `xs.filter P` for the first bucket and from its complement for the second. -/
theorem bind_listChoices_filter {β γ δ : Type*} (P : β → Prop) [DecidablePred P]
    (xs : List β) (gs : List γ) (G : List (β × γ) → List (β × γ) → Multiset δ) :
    (listChoices xs gs.length : Multiset (List β)).bind (fun ch =>
        G ((ch.zip gs).filter fun p => decide (P p.1))
          ((ch.zip gs).filter fun p => decide (¬ P p.1))) =
      (gs.sublists'.revzip : Multiset (List γ × List γ)).bind fun p =>
        (listChoices (xs.filter fun x => decide (P x)) p.1.length :
            Multiset (List β)).bind fun u =>
          (listChoices (xs.filter fun x => decide (¬ P x)) p.2.length :
              Multiset (List β)).bind fun w =>
            G (u.zip p.1) (w.zip p.2) := by
  induction gs generalizing G with
  | nil => simp
  | cons g gs ih =>
    rw [List.length_cons, coe_listChoices_succ, Multiset.bind_assoc,
      ← Multiset.filter_add_not (fun x => P x) (xs : Multiset β), Multiset.add_bind,
      List.revzip_sublists'_cons, ← Multiset.coe_add, Multiset.add_bind, ← Multiset.map_coe,
      ← Multiset.map_coe, Multiset.bind_map, Multiset.bind_map]
    simp only [Prod.map_fst, Prod.map_snd, id_eq, List.length_cons, coe_listChoices_succ,
      Multiset.bind_assoc, Multiset.bind_map, Multiset.filter_coe, List.zip_cons_cons]
    rw [add_comm]
    congr 1
    · conv_rhs => enter [2, p]; rw [Multiset.bind_bind]
      rw [Multiset.bind_bind (↑gs.sublists'.revzip : Multiset (List γ × List γ))
        (↑(xs.filter fun x => decide (¬ P x)) : Multiset β)]
      refine Multiset.bind_congr fun v hv => ?_
      have hv : ¬ P v := by simpa using (List.mem_filter.mp (Multiset.mem_coe.mp hv)).2
      simp only [List.filter_cons, decide_eq_true_eq, hv, not_false_eq_true, ite_true, ite_false]
      exact ih fun a b => G a ((v, g) :: b)
    · rw [Multiset.bind_bind (↑gs.sublists'.revzip : Multiset (List γ × List γ))
        (↑(xs.filter fun x => decide (P x)) : Multiset β)]
      refine Multiset.bind_congr fun v hv => ?_
      have hv : P v := by simpa using (List.mem_filter.mp (Multiset.mem_coe.mp hv)).2
      simp only [List.filter_cons, decide_eq_true_eq, hv, not_true_eq_false, ite_true, ite_false]
      exact ih fun a b => G ((v, g) :: a) b

/-- Permuting the guests permutes the zipped pair lists: a sum over choices of a
`Perm`-invariant function of `ch.zip gs` does not depend on the order of `gs`. -/
theorem bind_listChoices_zip_perm {β γ δ : Type*} (xs : List β) {gs gs' : List γ}
    (h : gs.Perm gs') (G : List (β × γ) → Multiset δ)
    (hG : ∀ {ps ps' : List (β × γ)}, ps.Perm ps' → G ps = G ps') :
    (listChoices xs gs.length : Multiset (List β)).bind (fun ch => G (ch.zip gs)) =
      (listChoices xs gs'.length : Multiset (List β)).bind fun ch => G (ch.zip gs') := by
  induction h generalizing G with
  | nil => rfl
  | cons g _ ih =>
    simp only [List.length_cons, coe_listChoices_succ, Multiset.bind_assoc, Multiset.bind_map,
      List.zip_cons_cons]
    exact Multiset.bind_congr fun v _ => ih (fun ps => G ((v, g) :: ps)) fun hp => hG (hp.cons _)
  | swap a b l =>
    simp only [List.length_cons, coe_listChoices_succ, Multiset.bind_assoc, Multiset.bind_map,
      List.zip_cons_cons]
    rw [Multiset.bind_bind]
    exact Multiset.bind_congr fun v _ => Multiset.bind_congr fun w _ =>
      Multiset.bind_congr fun ch _ => hG (List.Perm.swap _ _ _)
  | trans _ _ ih₁ ih₂ => exact (ih₁ G hG).trans (ih₂ G hG)

/-! ## `insertion`: single-tree host -/

/-- Multi-graft on a single-tree host: the sum over `(v₁, …, vₙ) ∈ V(T)ⁿ` of
    `multiGraft T [(v₁, T₁), …, (vₙ, Tₙ)]`. -/
def insertion (T : RoseTree α) (Ts : List (RoseTree α)) : Multiset (RoseTree α) :=
  Multiset.ofList <| (listChoices (vertices T) Ts.length).map
    fun choice => multiGraft T (choice.zip Ts)

theorem insertion_def (T : RoseTree α) (Ts : List (RoseTree α)) :
    insertion T Ts =
      Multiset.ofList ((listChoices (vertices T) Ts.length).map
        fun choice => multiGraft T (choice.zip Ts)) := rfl

/-! ## `insertionForest`: forest host -/

/-- Multi-graft into a host forest: the sum over assignments of guests to forest vertices of
    the simultaneous `multiGraftChildren`. -/
def insertionForest (cs gs : List (RoseTree α)) : Multiset (List (RoseTree α)) :=
  Multiset.ofList <| (listChoices (verticesAux 0 cs) gs.length).map
    fun ch => multiGraftChildren cs (ch.zip gs)

theorem insertionForest_def (cs gs : List (RoseTree α)) :
    insertionForest cs gs =
      Multiset.ofList ((listChoices (verticesAux 0 cs) gs.length).map
        fun ch => multiGraftChildren cs (ch.zip gs)) := rfl

@[simp] theorem insertionForest_nil_nil :
    insertionForest ([] : List (RoseTree α)) [] = ({[]} : Multiset (List (RoseTree α))) := rfl

@[simp] theorem insertionForest_empty_host_nonempty_guests
    (T_g : RoseTree α) (Ts : List (RoseTree α)) :
    insertionForest ([] : List (RoseTree α)) (T_g :: Ts) = 0 := rfl

@[simp] theorem insertionForest_cons_host_nil_guests
    (T : RoseTree α) (F : List (RoseTree α)) :
    insertionForest (T :: F) ([] : List (RoseTree α)) =
      ({T :: F} : Multiset (List (RoseTree α))) := by
  show (Multiset.ofList [multiGraftChildren (T :: F) []] : Multiset _) = _
  rw [multiGraftChildren_nil_pairs]
  rfl

theorem insertionForest_nil_guests (F : List (RoseTree α)) :
    insertionForest F [] = ({F} : Multiset (List (RoseTree α))) := by
  cases F
  · exact insertionForest_nil_nil
  · exact insertionForest_cons_host_nil_guests _ _

/-- Zipping a mapped list and undoing the map on the first components. -/
private theorem map_zip_map_left {β β' γ : Type*} {f : β → β'} {f' : β' → β}
    (h : ∀ x, f' (f x) = x) (l : List β) (r : List γ) :
    ((l.map f).zip r).map (Prod.map f' id) = l.zip r := by
  rw [List.zip_map_left, List.map_map]
  exact (List.map_congr_left fun ⟨x, y⟩ _ => by simp [h]).trans (List.map_id _)

/-- The host-forest recursion: the head host takes a sublist of the guests, the tail forest the
complement. -/
theorem insertionForest_cons (T : RoseTree α) (F gs : List (RoseTree α)) :
    insertionForest (T :: F) gs =
      (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun p =>
        (insertion T p.1).bind fun T' => (insertionForest F p.2).map (T' :: ·) := by
  have hne : ∀ p ∈ verticesAux 0 (T :: F), p ≠ [] := fun p hp => by
    obtain ⟨k, q, -, rfl⟩ := exists_cons_of_mem_verticesAux hp
    exact List.cons_ne_nil k q
  have hG : ∀ ch ∈ (listChoices (verticesAux 0 (T :: F)) gs.length : Multiset (List Path)),
      ({multiGraftChildren (T :: F) (ch.zip gs)} : Multiset (List (RoseTree α))) =
        {multiGraft T (((ch.zip gs).filter fun p => decide (p.1.head? = some 0)).map
            (Prod.map List.tail id)) ::
          multiGraftChildren F (((ch.zip gs).filter fun p => decide (¬ p.1.head? = some 0)).map
            (Prod.map (List.modifyHead (· - 1)) id))} := by
    intro ch hch
    rw [multiGraftChildren_cons_cs, filterMap_headChildFilter, filterMap_tailChildFilter]
    exact fun p hp =>
      hne _ ((mem_listChoices.mp (Multiset.mem_coe.mp hch)).2 _ (List.of_mem_zip hp).1)
  have hfilter :
      (verticesAux 0 (T :: F)).filter (fun q : Path => decide (q.head? = some 0)) =
          (vertices T).map (0 :: ·) ∧
        (verticesAux 0 (T :: F)).filter (fun q : Path => decide (¬ q.head? = some 0)) =
          (verticesAux 0 F).map (List.modifyHead (· + 1)) := by
    rw [verticesAux_cons, Nat.zero_add, verticesAux_eq_map_modifyHead 1 F, List.filter_append,
      List.filter_append, List.filter_map, List.filter_map, List.filter_map, List.filter_map]
    constructor
    · rw [List.filter_eq_self.2 fun q _ => by simp, List.filter_eq_nil_iff.2 fun q hq => ?_,
        List.map_nil, List.append_nil]
      obtain ⟨k, q, -, rfl⟩ := exists_cons_of_mem_verticesAux hq
      simp
    · rw [List.filter_eq_nil_iff.2 fun q _ => by simp, List.map_nil, List.nil_append,
        List.filter_eq_self.2 fun q hq => ?_]
      obtain ⟨k, q, -, rfl⟩ := exists_cons_of_mem_verticesAux hq
      simp
  rw [insertionForest_def, ← Multiset.map_coe, ← Multiset.bind_singleton,
    Multiset.bind_congr hG,
    bind_listChoices_filter (fun q : Path => q.head? = some 0) _ gs fun a b =>
      {multiGraft T (a.map (Prod.map List.tail id)) ::
        multiGraftChildren F (b.map (Prod.map (List.modifyHead (· - 1)) id))},
    hfilter.1, hfilter.2]
  symm
  refine Multiset.bind_congr fun p _ => ?_
  rw [insertion_def, insertionForest_def, ← Multiset.map_coe, ← Multiset.map_coe,
    Multiset.bind_map, listChoices_map, listChoices_map, ← Multiset.map_coe, ← Multiset.map_coe,
    Multiset.bind_map]
  refine Multiset.bind_congr fun u _ => ?_
  rw [Multiset.bind_map, Multiset.map_map, ← Multiset.bind_singleton]
  refine Multiset.bind_congr fun w _ => ?_
  rw [map_zip_map_left fun _ => rfl, map_zip_map_left fun q => by cases q <;> simp]
  rfl

/-- Only the split assigning no guest to the empty forest contributes. -/
private theorem bind_revzip_insertionForest_nil {δ : Type*} (gs : List (RoseTree α))
    (H : List (RoseTree α) → List (RoseTree α) → Multiset δ) :
    (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind
        (fun p => (insertionForest [] p.1).bind fun A => H A p.2) = H [] gs := by
  induction gs generalizing H with
  | nil => simp
  | cons g gs ih =>
    simp only [List.revzip_sublists'_cons, ← Multiset.coe_add, Multiset.add_bind,
      ← Multiset.map_coe, Multiset.bind_map, Prod.map_fst, Prod.map_snd, id_eq,
      insertionForest_empty_host_nonempty_guests, Multiset.zero_bind, Multiset.bind_zero,
      add_zero]
    exact ih fun A s => H A (g :: s)

/-- Grafting into a concatenated host: the guests split into a sublist for the left forest and
its complement for the right one. -/
theorem insertionForest_append (xs ys gs : List (RoseTree α)) :
    insertionForest (xs ++ ys) gs =
      (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun p =>
        (insertionForest xs p.1).bind fun A => (insertionForest ys p.2).map (A ++ ·) := by
  induction xs generalizing gs with
  | nil =>
    rw [List.nil_append,
      bind_revzip_insertionForest_nil gs fun A s => (insertionForest ys s).map (A ++ ·)]
    exact (Multiset.map_id' _).symm
  | cons x xs ih =>
    rw [List.cons_append, insertionForest_cons]
    simp only [ih, insertionForest_cons, Multiset.map_bind, Multiset.map_map, Multiset.bind_assoc,
      Multiset.bind_map]
    rw [← Multiset.bind_revzip_sublists'_assoc gs fun r₁ s₁ s =>
      (insertion x r₁).bind fun T' => (insertionForest xs s₁).bind fun A =>
        (insertionForest ys s).map ((T' :: A) ++ ·)]
    exact Multiset.bind_congr fun p _ => Multiset.bind_bind _ _

/-- **Split law**: splits of an output list are splits of the hosts and of the guests, each
guest following its host. Stated in continuation form over a function `K` of the two parts. -/
theorem insertionForest_bind_revzip_sublists' {δ : Type*} (hs gs : List (RoseTree α))
    (K : List (RoseTree α) → List (RoseTree α) → Multiset δ) :
    (insertionForest hs gs).bind (fun L =>
        (L.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun x =>
          K x.1 x.2) =
      (hs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun h =>
        (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun q =>
          (insertionForest h.2 q.2).bind fun L₂ =>
            (insertionForest h.1 q.1).bind fun L₁ => K L₁ L₂ := by
  induction hs generalizing gs K with
  | nil =>
    simp only [List.sublists'_nil, List.revzip_singleton, Multiset.coe_singleton,
      Multiset.singleton_bind]
    rw [Multiset.bind_revzip_sublists'_swap gs fun x y =>
        (insertionForest [] y).bind fun L₂ => (insertionForest [] x).bind fun L₁ => K L₁ L₂,
      bind_revzip_insertionForest_nil gs fun L₂ s =>
        (insertionForest [] s).bind fun L₁ => K L₁ L₂]
    cases gs <;> simp
  | cons T hs ih =>
    have hL : (insertionForest (T :: hs) gs).bind (fun L =>
          (L.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun x =>
            K x.1 x.2) =
        (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun p =>
          (insertion T p.1).bind fun T' =>
            ((hs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind
              fun h => (p.2.sublists'.revzip :
                  Multiset (List (RoseTree α) × List (RoseTree α))).bind fun q =>
                (insertionForest h.2 q.2).bind fun L₂ =>
                  (insertionForest h.1 q.1).bind fun L₁ => K L₁ (T' :: L₂)) +
            ((hs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind
              fun h => (p.2.sublists'.revzip :
                  Multiset (List (RoseTree α) × List (RoseTree α))).bind fun q =>
                (insertionForest h.2 q.2).bind fun L₂ =>
                  (insertionForest h.1 q.1).bind fun L₁ => K (T' :: L₁) L₂) := by
      rw [insertionForest_cons, Multiset.bind_assoc]
      refine Multiset.bind_congr fun p _ => ?_
      rw [Multiset.bind_assoc]
      refine Multiset.bind_congr fun T' _ => ?_
      simp only [Multiset.bind_map, List.revzip_sublists'_cons, ← Multiset.coe_add,
        Multiset.add_bind, ← Multiset.map_coe, Prod.map_fst, Prod.map_snd, id_eq,
        Multiset.bind_add]
      rw [ih p.2 fun a b => K a (T' :: b), ih p.2 fun a b => K (T' :: a) b]
    rw [hL]
    simp only [Multiset.bind_add, List.revzip_sublists'_cons, ← Multiset.coe_add,
      Multiset.add_bind, ← Multiset.map_coe, Multiset.bind_map, Prod.map_fst, Prod.map_snd,
      id_eq, insertionForest_cons, Multiset.bind_assoc]
    rw [Multiset.bind_bind_bind_comm, Multiset.bind_bind_bind_comm]
    congr 1
    · exact Multiset.bind_congr fun h _ => Multiset.bind_revzip_sublists'_bind_assoc gs
        (insertion T) fun T' g₁ g₂ => (insertionForest h.2 g₂).bind fun L₂ =>
          (insertionForest h.1 g₁).bind fun L₁ => K L₁ (T' :: L₂)
    · refine Multiset.bind_congr fun h _ => ?_
      rw [Multiset.bind_revzip_sublists'_bind_assoc' gs (insertion T) fun T' g₁ g₂ =>
        (insertionForest h.2 g₂).bind fun L₂ => (insertionForest h.1 g₁).bind fun L₁ =>
          K (T' :: L₁) L₂]
      exact Multiset.bind_congr fun q _ => Multiset.bind_bind_bind_comm _ _ _ _

/-- **Node-host decomposition**: guests split into a sublist prepended at the root, in guest
order, and its complement grafted into the child forest. -/
theorem insertion_node (a : α) (cs gs : List (RoseTree α)) :
    insertion (RoseTree.node a cs) gs =
      (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun p =>
        (insertionForest cs p.2).map fun cs' => RoseTree.node a (p.1 ++ cs') := by
  have hG :
      ∀ ch ∈ (listChoices (vertices (RoseTree.node a cs)) gs.length : Multiset (List Path)),
      ({multiGraft (RoseTree.node a cs) (ch.zip gs)} : Multiset (RoseTree α)) =
        {RoseTree.node a (((ch.zip gs).filter fun p => decide (p.1 = [])).map Prod.snd ++
          multiGraftChildren cs ((ch.zip gs).filter fun p => decide (¬ p.1 = [])))} := by
    intro ch _
    rw [multiGraft_node, filterMap_rootPrependFilter, ← multiGraftChildren_filter_ne_nil]
  have hfilter :
      (vertices (RoseTree.node a cs)).filter (fun q : Path => decide (q = [])) = [[]] ∧
        (vertices (RoseTree.node a cs)).filter (fun q : Path => decide (¬ q = [])) =
          verticesAux 0 cs := by
    have h : ∀ q ∈ verticesAux 0 cs, q ≠ [] := fun q hq => by
      obtain ⟨k, q, -, rfl⟩ := exists_cons_of_mem_verticesAux hq
      exact List.cons_ne_nil k q
    rw [vertices_node]
    constructor
    · rw [List.filter_cons_of_pos (by simp), List.filter_eq_nil_iff.2 fun q hq => by simp [h q hq]]
    · rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.2 fun q hq => by simp [h q hq]]
  rw [insertion_def, ← Multiset.map_coe, ← Multiset.bind_singleton, Multiset.bind_congr hG,
    bind_listChoices_filter (fun q : Path => q = []) _ gs fun r s =>
      {RoseTree.node a (r.map Prod.snd ++ multiGraftChildren cs s)},
    hfilter.1, hfilter.2]
  refine Multiset.bind_congr fun p _ => ?_
  rw [listChoices_singleton, Multiset.coe_singleton, Multiset.singleton_bind,
    List.map_snd_zip (by simp), insertionForest_def, ← Multiset.map_coe,
    Multiset.map_map, ← Multiset.bind_singleton]
  rfl

/-! ## Pair-list `Perm` invariance for `multiGraft`

`multiGraft T pairs` is `Perm`-invariant under permutation of the
pair list: grafts at distinct paths commute, and grafts at the same
path are root-list permutations (lift via `Perm.node_of_perm`).

Path-based reformulation of the legacy `multiGraft_perm_pair` /
`multiGraftList_perm_pair`. -/

mutual
/-- `Perm` of `multiGraft T pairs` and `multiGraft T pairs'`
    follows from a `List.Perm` between `pairs` and `pairs'`. Mutual
    recursion on `T` with the children-list aux. -/
private theorem multiGraft_perm_pair : ∀ (T : RoseTree α)
    {pairs pairs' : List (Path × RoseTree α)},
    pairs.Perm pairs' →
    Perm (multiGraft T pairs) (multiGraft T pairs')
  | .node a cs, pairs, pairs', h => by
    rw [multiGraft_node, multiGraft_node]
    exact (Perm.node_of_perm
            ((h.filterMap rootPrependFilter).append_right _)).trans
          (Perm.node_of_forall₂
            (List.rel_append
              (List.forall₂_same.mpr fun _ _ => Perm.refl _)
              (multiGraftChildren_perm_pair cs h)))
/-- List-level companion to `multiGraft_perm_pair`: pair-list `Perm`
    lifts to `Forall₂ Perm` on the children list output of
    `multiGraftChildren`. -/
private theorem multiGraftChildren_perm_pair : ∀ (cs : List (RoseTree α))
    {pairs pairs' : List (Path × RoseTree α)},
    pairs.Perm pairs' →
    List.Forall₂ Perm
      (multiGraftChildren cs pairs) (multiGraftChildren cs pairs')
  | [],      _, _, _ => List.Forall₂.nil
  | c :: cs, pairs, pairs', h => by
    rw [multiGraftChildren_cons_cs, multiGraftChildren_cons_cs]
    refine List.Forall₂.cons ?_ ?_
    · exact multiGraft_perm_pair c (h.filterMap _)
    · exact multiGraftChildren_perm_pair cs (h.filterMap _)
end

/-! ### Forall₂-version of `multiGraft_perm_pair`

For `insertion_perm_guests` we need: when `Ts ~ᶠ Ts'` (Forall₂
Perm) and we zip with the same choice, the resulting pair lists
satisfy a Forall₂ relation (same fst, Perm snd). Then this lifts
to `multiGraft T pairs ~ multiGraft T pairs'` (`Perm`).

Path-based version of the legacy `multiGraft_perm_pair_Forall₂`. -/

private theorem zip_pair_Forall₂ {β γ : Type*} {R : γ → γ → Prop}
    (choice : List β) :
    ∀ {Ts Ts' : List γ}, List.Forall₂ R Ts Ts' →
      List.Forall₂ (fun p p' : β × γ => p.fst = p'.fst ∧ R p.snd p'.snd)
        (choice.zip Ts) (choice.zip Ts') := by
  induction choice with
  | nil => intro Ts Ts' _; exact List.Forall₂.nil
  | cons c cs ih =>
    intro Ts Ts' h
    cases h with
    | nil => exact List.Forall₂.nil
    | cons hTT' hrest =>
      simp only [List.zip_cons_cons]
      exact List.Forall₂.cons ⟨rfl, hTT'⟩ (ih hrest)

mutual
/-- `Perm` of `multiGraft T pairs` and `multiGraft T pairs'`
    follows from pair-`Forall₂` (same fst, `Perm` snds). -/
private theorem multiGraft_perm_pair_Forall₂ : ∀ (T : RoseTree α)
    {pairs pairs' : List (Path × RoseTree α)},
    List.Forall₂ (fun p p' : Path × RoseTree α =>
        p.fst = p'.fst ∧ Perm p.snd p'.snd) pairs pairs' →
    Perm (multiGraft T pairs) (multiGraft T pairs')
  | .node a cs, pairs, pairs', h => by
    rw [multiGraft_node, multiGraft_node]
    apply Perm.node_of_forall₂
    apply List.rel_append
    · -- root-prepended children: Forall₂ Perm after filterMap
      refine List.rel_filterMap (P := Perm) ?_ h
      rintro ⟨xfst, xsnd⟩ ⟨yfst, ysnd⟩ ⟨hfst, hsnd⟩
      simp only at hfst
      subst hfst
      cases xfst with
      | nil       => exact Option.Rel.some hsnd
      | cons _ _  => exact Option.Rel.none
    · -- children: Forall₂ Perm on multiGraftChildren output
      exact multiGraftChildren_perm_pair_Forall₂ cs h

/-- List-level companion. -/
private theorem multiGraftChildren_perm_pair_Forall₂ :
    ∀ (cs : List (RoseTree α))
    {pairs pairs' : List (Path × RoseTree α)},
    List.Forall₂ (fun p p' : Path × RoseTree α =>
        p.fst = p'.fst ∧ Perm p.snd p'.snd) pairs pairs' →
    List.Forall₂ Perm
      (multiGraftChildren cs pairs) (multiGraftChildren cs pairs')
  | [],      _, _, _ => List.Forall₂.nil
  | c :: cs, pairs, pairs', h => by
    rw [multiGraftChildren_cons_cs, multiGraftChildren_cons_cs]
    refine List.Forall₂.cons ?_ ?_
    · apply multiGraft_perm_pair_Forall₂
      refine List.rel_filterMap ?_ h
      rintro ⟨xfst, xsnd⟩ ⟨yfst, ysnd⟩ ⟨hfst, hsnd⟩
      simp only at hfst
      subst hfst
      cases xfst with
      | nil => exact Option.Rel.none
      | cons k _ =>
        cases k with
        | zero   => exact Option.Rel.some ⟨rfl, hsnd⟩
        | succ _ => exact Option.Rel.none
    · apply multiGraftChildren_perm_pair_Forall₂
      refine List.rel_filterMap ?_ h
      rintro ⟨xfst, xsnd⟩ ⟨yfst, ysnd⟩ ⟨hfst, hsnd⟩
      simp only at hfst
      subst hfst
      cases xfst with
      | nil => exact Option.Rel.none
      | cons k _ =>
        cases k with
        | zero   => exact Option.Rel.none
        | succ _ => exact Option.Rel.some ⟨rfl, hsnd⟩
end

/-! ## Guest invariance

`bind_listChoices_zip_perm` permutes the zipped pair lists along a guest permutation, and
`multiGraft` is `Perm`-invariant in its pair list. -/

/-- Single-tree `insertion` is `mk`-invariant under `List.Perm` of guests. -/
theorem insertion_perm_guests (t : RoseTree α)
    {Ts Ts' : List (RoseTree α)} (h : Ts.Perm Ts') :
    (insertion t Ts).map UnorderedTree.mk =
      (insertion t Ts').map UnorderedTree.mk := by
  rw [insertion_def, insertion_def, ← Multiset.map_coe, ← Multiset.map_coe, Multiset.map_map,
    Multiset.map_map, ← Multiset.bind_singleton, ← Multiset.bind_singleton]
  exact bind_listChoices_zip_perm (vertices t) h
    (fun ps => {UnorderedTree.mk (multiGraft t ps)})
    fun hp => by rw [UnorderedTree.mk_eq_mk_iff.mpr (multiGraft_perm_pair t hp)]

/-- `List.Forall₂ Perm` lifts to `List` equality after mapping by
    `UnorderedTree.mk` — used for the `Ts = []` base case of forest host
    invariance. -/
private theorem map_mk_eq_of_forall2_perm {F F' : List (RoseTree α)}
    (h : List.Forall₂ Perm F F') :
    F.map UnorderedTree.mk = F'.map UnorderedTree.mk := by
  induction h with
  | nil => rfl
  | cons hd_pe _ ih => simp [UnorderedTree.mk_eq_mk_iff.mpr hd_pe, ih]

/-- Forest guest invariance: `List.Perm` of guests lifts to `mk`-equality of
    `insertionForest`. -/
theorem insertionForest_perm_guests
    (F : List (RoseTree α)) {Ts Ts' : List (RoseTree α)} (h : Ts.Perm Ts') :
    (insertionForest F Ts).map (List.map UnorderedTree.mk) =
      (insertionForest F Ts').map (List.map UnorderedTree.mk) := by
  rw [insertionForest_def, insertionForest_def, ← Multiset.map_coe, ← Multiset.map_coe,
    Multiset.map_map, Multiset.map_map, ← Multiset.bind_singleton, ← Multiset.bind_singleton]
  exact bind_listChoices_zip_perm (verticesAux 0 F) h
    (fun ps => {(multiGraftChildren F ps).map UnorderedTree.mk})
    fun hp => by rw [map_mk_eq_of_forall2_perm (multiGraftChildren_perm_pair F hp)]

/-- Guest-list `Forall₂ Perm` lifts to `mk`-equality of `insertionForest`. -/
theorem insertionForest_forall₂_perm_guests
    (F : List (RoseTree α)) {Ts Ts' : List (RoseTree α)} (h : List.Forall₂ Perm Ts Ts') :
    (insertionForest F Ts).map (List.map UnorderedTree.mk) =
      (insertionForest F Ts').map (List.map UnorderedTree.mk) := by
  rw [insertionForest_def, insertionForest_def, Multiset.map_coe, Multiset.map_coe,
    List.map_map, List.map_map, h.length_eq]
  congr 1
  exact List.map_congr_left fun choice _ => map_mk_eq_of_forall2_perm
    (multiGraftChildren_perm_pair_Forall₂ F (zip_pair_Forall₂ choice h))

/-! ## Descent to `UnorderedTree.mk`

`UnorderedTree.insertionMultiset` reads `insertionForest` through `L ↦ ↑(L.map mk)`, which
forgets the order of each output list. At that level the host list may be permuted, each host
may be replaced by a `Perm`-related tree, and the guests by any list with the same `mk`-image:
`insertion_node` and `insertionForest_cons` push `mk` through the recursion, and a host
permutation reduces to swapping two adjacent hosts under `insertionForest_append`. -/

private theorem msform_cons (T : RoseTree α) (L : List (RoseTree α)) :
    (↑((T :: L).map UnorderedTree.mk) : Multiset (UnorderedTree α)) =
      UnorderedTree.mk T ::ₘ ↑(L.map UnorderedTree.mk) := rfl

private theorem msform_append (A B : List (RoseTree α)) :
    (↑((A ++ B).map UnorderedTree.mk) : Multiset (UnorderedTree α)) =
      ↑(A.map UnorderedTree.mk) + ↑(B.map UnorderedTree.mk) := by
  rw [List.map_append, Multiset.coe_add]

/-- The host-forest recursion under `mk`. -/
theorem insertionForest_cons_msform (T : RoseTree α) (F gs : List (RoseTree α)) :
    (insertionForest (T :: F) gs).map
        (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α))) =
      (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun p =>
        ((insertion T p.1).map UnorderedTree.mk).bind fun X =>
          ((insertionForest F p.2).map
            (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α)))).map
            (X ::ₘ ·) := by
  rw [insertionForest_cons, Multiset.map_bind]
  refine Multiset.bind_congr fun p _ => ?_
  rw [Multiset.map_bind, Multiset.bind_map]
  refine Multiset.bind_congr fun T' _ => ?_
  rw [Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun L _ => msform_cons T' L

/-- The node-host decomposition under `mk`. -/
theorem insertion_node_msform (a : α) (cs gs : List (RoseTree α)) :
    (insertion (RoseTree.node a cs) gs).map UnorderedTree.mk =
      (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun p =>
        ((insertionForest cs p.2).map
            (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α)))).map fun X =>
          UnorderedTree.node a (↑(p.1.map UnorderedTree.mk) + X) := by
  rw [insertion_node, Multiset.map_bind]
  refine Multiset.bind_congr fun p _ => ?_
  rw [Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun cs' _ => ?_
  show UnorderedTree.mk (RoseTree.node a (p.1 ++ cs')) = _
  rw [← UnorderedTree.node_mk_tree_list, List.map_append, ← Multiset.coe_add]
  rfl

/-- Two hosts commute once output order is forgotten. -/
private theorem insertionForest_pair_swap_msform (x y : RoseTree α) (gs : List (RoseTree α)) :
    (insertionForest [y, x] gs).map
        (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α))) =
      (insertionForest [x, y] gs).map
        (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α))) := by
  rw [show [y, x] = [y] ++ [x] from rfl, show [x, y] = [x] ++ [y] from rfl,
    insertionForest_append, insertionForest_append, Multiset.map_bind, Multiset.map_bind,
    Multiset.bind_revzip_sublists'_swap gs fun r s =>
      ((insertionForest [y] r).bind fun A => (insertionForest [x] s).map (A ++ ·)).map
        (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α)))]
  refine Multiset.bind_congr fun p _ => ?_
  rw [Multiset.map_bind, Multiset.map_bind]
  simp only [Multiset.map_map]
  simp only [← Multiset.bind_singleton]
  rw [Multiset.bind_bind]
  refine Multiset.bind_congr fun A _ => Multiset.bind_congr fun B _ => ?_
  show ({(↑((B ++ A).map UnorderedTree.mk) : Multiset (UnorderedTree α))} : Multiset _) =
    {(↑((A ++ B).map UnorderedTree.mk) : Multiset (UnorderedTree α))}
  rw [msform_append, msform_append, add_comm]

/-- Host-`Perm` invariance once output order is forgotten. -/
theorem insertionForest_perm_host_msform {host host' : List (RoseTree α)} (h : host.Perm host')
    (gs : List (RoseTree α)) :
    (insertionForest host gs).map
        (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α))) =
      (insertionForest host' gs).map
        (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α))) := by
  induction h generalizing gs with
  | nil => rfl
  | cons x _ ih =>
    rw [insertionForest_cons, insertionForest_cons, Multiset.map_bind, Multiset.map_bind]
    refine Multiset.bind_congr fun p _ => ?_
    rw [Multiset.map_bind, Multiset.map_bind]
    refine Multiset.bind_congr fun T' _ => ?_
    rw [Multiset.map_map, Multiset.map_map,
      show ((fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α))) ∘ (T' :: ·)) =
        ((UnorderedTree.mk T' ::ₘ ·) ∘
          (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α)))) from
        funext fun L => msform_cons T' L,
      ← Multiset.map_map, ← Multiset.map_map, ih]
  | swap x y l =>
    rw [show y :: x :: l = [y, x] ++ l from rfl, show x :: y :: l = [x, y] ++ l from rfl,
      insertionForest_append, insertionForest_append, Multiset.map_bind, Multiset.map_bind]
    refine Multiset.bind_congr fun p _ => ?_
    have key : ∀ hs : List (RoseTree α),
        ((insertionForest hs p.1).bind fun A => (insertionForest l p.2).map (A ++ ·)).map
            (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α))) =
          ((insertionForest hs p.1).map
            (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α)))).bind fun M =>
            (insertionForest l p.2).map fun B => M + ↑(B.map UnorderedTree.mk) := by
      intro hs
      rw [Multiset.map_bind, Multiset.bind_map]
      refine Multiset.bind_congr fun A _ => ?_
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun B _ => msform_append A B
    rw [key, key, insertionForest_pair_swap_msform]
  | trans _ _ ih₁ ih₂ => exact (ih₁ gs).trans (ih₂ gs)

mutual
/-- `insertion` is `mk`-invariant under `Perm` of the host. -/
theorem insertion_perm_host : ∀ {t t' : RoseTree α}, Perm t t' → ∀ Ts : List (RoseTree α),
    (insertion t Ts).map UnorderedTree.mk = (insertion t' Ts).map UnorderedTree.mk
  | _, _, .node h, Ts => by
    rw [insertion_node_msform, insertion_node_msform]
    exact Multiset.bind_congr fun p _ => by rw [insertionForest_permList_host_msform h]
  | _, _, .trans h₁ h₂, Ts => (insertion_perm_host h₁ Ts).trans (insertion_perm_host h₂ Ts)
/-- `insertionForest` is `mk`-invariant under `PermList` of the hosts. -/
theorem insertionForest_permList_host_msform :
    ∀ {cs ds : List (RoseTree α)}, PermList cs ds → ∀ gs : List (RoseTree α),
    (insertionForest cs gs).map
        (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α))) =
      (insertionForest ds gs).map
        (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α)))
  | _, _, .nil, _ => rfl
  | _, _, .cons hcd hs, gs => by
    rw [insertionForest_cons_msform, insertionForest_cons_msform]
    exact Multiset.bind_congr fun p _ => by
      rw [insertion_perm_host hcd, insertionForest_permList_host_msform hs]
  | _, _, .swap c d cs, gs => insertionForest_perm_host_msform (List.Perm.swap c d cs) gs
  | _, _, .trans h₁ h₂, gs =>
    (insertionForest_permList_host_msform h₁ gs).trans
      (insertionForest_permList_host_msform h₂ gs)
end

/-- Guest invariance once output order is forgotten: guest lists with the same `mk`-image
    multiset give the same outputs. -/
theorem insertionForest_msform_invariance_guests [DecidableEq α]
    (host : List (RoseTree α)) {gs1 gs2 : List (RoseTree α)}
    (h : (gs1.map UnorderedTree.mk).Perm (gs2.map UnorderedTree.mk)) :
    (insertionForest host gs1).map
        (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α))) =
      (insertionForest host gs2).map
        (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α))) := by
  obtain ⟨gs_mid, hperm, hF⟩ := List.exists_perm_forall₂_of_map_perm h
  have h_forall : List.Forall₂ RoseTree.Perm gs_mid gs2 :=
    hF.imp fun a b (h : UnorderedTree.mk a = UnorderedTree.mk b) => UnorderedTree.mk_eq_mk_iff.mp h
  have hwrap : ∀ s : Multiset (List (RoseTree α)),
      s.map (fun L => (↑(L.map UnorderedTree.mk) : Multiset (UnorderedTree α))) =
        (s.map (List.map UnorderedTree.mk)).map
          fun L : List (UnorderedTree α) => (↑L : Multiset (UnorderedTree α)) := by
    intro s
    rw [Multiset.map_map]
    rfl
  rw [hwrap, hwrap, insertionForest_perm_guests host hperm,
    insertionForest_forall₂_perm_guests host h_forall]

/-! ## Singleton hosts and single guests

A one-tree host reduces `insertionForest` to `insertion`, and a single guest reduces
`insertion` to the pre-Lie product `RoseTree.insertSum`. -/

/-- Choices of length one are the letters. -/
theorem listChoices_one {β : Type*} (xs : List β) : listChoices xs 1 = xs.map fun x => [x] :=
  List.map_eq_flatMap.symm

/-- With a single guest, the multi-insertion is the Chapoton–Livernet pre-Lie product. -/
theorem insertion_singleton (T g : RoseTree α) : insertion T [g] = RoseTree.insertSum T g := by
  rw [insertion_def, insertSum_eq_coe_map_insertAt, List.length_singleton, listChoices_one,
    List.map_map]
  congr 1
  exact List.map_congr_left fun v _ => multiGraft_singleton T v g

/-- `insertion T []` is the singleton `{T}` — multi-graft of no guests is
    the identity. -/
theorem insertion_nil_guests (T : RoseTree α) :
    insertion T ([] : List (RoseTree α)) = ({T} : Multiset (RoseTree α)) := by
  rw [insertion_def]
  simp only [List.length_nil, listChoices_zero, List.zip_nil_right,
             multiGraft_nil, List.map_cons, List.map_nil,
             Multiset.coe_singleton]

/-- **Singleton-host insertion**: when the host has exactly one tree, `insertionForest` is
    single-tree `insertion` with each output wrapped in a singleton list. -/
theorem insertionForest_singleton (T : RoseTree α) (gs : List (RoseTree α)) :
    insertionForest [T] gs = (insertion T gs).map (fun T' => [T']) := by
  rw [insertionForest_def, insertion_def, verticesAux_cons, verticesAux_nil, List.append_nil,
    listChoices_map, ← Multiset.map_coe, ← Multiset.map_coe, ← Multiset.map_coe,
    Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun u _ => ?_
  show multiGraftChildren [T] ((u.map (0 :: ·)).zip gs) = [multiGraft T (u.zip gs)]
  rw [multiGraftChildren_cons_cs, multiGraftChildren_nil_cs, filterMap_headChildFilter,
    List.filter_eq_self.2 fun p hp => ?_, map_zip_map_left fun _ => rfl]
  obtain ⟨q, T'⟩ := p
  obtain ⟨q', -, rfl⟩ := List.mem_map.mp (List.of_mem_zip hp).1
  simp

end Pathed

end RoseTree
