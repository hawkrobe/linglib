/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Graft
import Linglib.Core.Data.List.Sublists
import Linglib.Core.Data.Multiset.Powerset
import Linglib.Core.Data.UnorderedTree.Basic
import Mathlib.Data.Multiset.Bind

/-!
# Foissy 2021 Theorem 5.1 multi-tree insertion (path-based)
[foissy-typed-decorated-rooted-trees-2018]
[foissy-introduction-hopf-algebras-trees]

The Foissy 2021 Theorem 5.1 multi-tree multi-vertex insertion operator.
Defined as a sum over functions `Ts → V(T)` of `multiGraft`, taken as
a `Multiset` to make the sum-over-choices commutative.

Sibling to `Graft.lean` (path-based multi-graft primitive). Lives under
namespace `RoseTree.Pathed`.

## File scope

- §1: `listChoices` — choice-list enumeration, and the keystone `bind_listChoices_filter`
  splitting choices over `gs.sublists'.revzip`.
- §2: `insertion` — Foissy 2021 Theorem 5.1, single-tree host.
- §3: `insertionForest` — forest host, its `sublists'.revzip` recursion
  (`insertionForest_cons`, `insertionForest_append`), and the node-host decomposition
  (`insertion_node`).
- §4: Pair-list `Perm`-invariance for `multiGraft`.
- §5: Guest-list invariance for `insertion` (`insertion_perm_guests`).
- §5.5: Validity discharge for `listChoices`-derived pair lists.
- §6: Host invariance via the `swapPathAt` path-relabel bijection.
- §7: Forest invariance (`insertionForest_perm_host`,
  `insertionForest_perm_guests`).
- §8: Singleton-host insertion.

## Status

`[UPSTREAM]` candidate. **Sorry-free**.
-/

namespace RoseTree

namespace Pathed

open RoseTree UnorderedTree

variable {α : Type*}

/-! ## §1: `listChoices` enumeration -/

/-- All length-`n` lists with entries from `xs` (with repetition).
    The "n-fold list power" used in Foissy 2021 Theorem 5.1's
    vertex-choice sum. Representation-independent (no `Vertex`
    dependence): copied from the legacy `Insertion.lean`. -/
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

/-! ## §2: `insertion` — Foissy 2021 Theorem 5.1 -/

/-- Foissy 2021 Theorem 5.1 multi-graft on a single-tree host. Sum over
    `(v₁, …, vₙ) ∈ V(T)ⁿ` of `multiGraft T [(v₁, T₁), …, (vₙ, Tₙ)]`. -/
def insertion (T : RoseTree α) (Ts : List (RoseTree α)) : Multiset (RoseTree α) :=
  Multiset.ofList <| (listChoices (vertices T) Ts.length).map
    fun choice => multiGraft T (choice.zip Ts)

theorem insertion_def (T : RoseTree α) (Ts : List (RoseTree α)) :
    insertion T Ts =
      Multiset.ofList ((listChoices (vertices T) Ts.length).map
        fun choice => multiGraft T (choice.zip Ts)) := rfl

/-! ## §3: `insertionForest` — forest host -/

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

/-! ## §4: Pair-list `Perm` invariance for `multiGraft`

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

/-! ## §5: Guest-list invariance for `insertion`

`bind_listChoices_zip_perm` (§1) permutes the zipped pair lists along a guest permutation, and
`multiGraft` is `Perm`-invariant in its pair list. -/

/-- Single-tree `insertion` is `mk`-invariant under `List.Perm` of guests. -/
private theorem insertion_perm_guests (t : RoseTree α)
    {Ts Ts' : List (RoseTree α)} (h : Ts.Perm Ts') :
    (insertion t Ts).map UnorderedTree.mk =
      (insertion t Ts').map UnorderedTree.mk := by
  rw [insertion_def, insertion_def, ← Multiset.map_coe, ← Multiset.map_coe, Multiset.map_map,
    Multiset.map_map, ← Multiset.bind_singleton, ← Multiset.bind_singleton]
  exact bind_listChoices_zip_perm (vertices t) h
    (fun ps => {UnorderedTree.mk (multiGraft t ps)})
    fun hp => by rw [UnorderedTree.mk_eq_mk_iff.mpr (multiGraft_perm_pair t hp)]

/-- Guest-list `Forall₂ Perm` lifts to `insertion mk`-equality. -/
theorem insertion_forall₂_perm_guests (t : RoseTree α)
    {Ts Ts' : List (RoseTree α)} (h : List.Forall₂ Perm Ts Ts') :
    (insertion t Ts).map UnorderedTree.mk =
      (insertion t Ts').map UnorderedTree.mk := by
  have hlen : Ts.length = Ts'.length := h.length_eq
  rw [insertion_def, insertion_def, Multiset.map_coe, Multiset.map_coe,
      List.map_map, List.map_map, hlen]
  congr 1
  apply List.map_congr_left
  intro choice _
  apply UnorderedTree.mk_eq_mk_iff.mpr
  -- multiGraft t (choice.zip Ts) ~ multiGraft t (choice.zip Ts')
  -- via List.Forall₂ for the pair (fst eq, snd perm)
  exact multiGraft_perm_pair_Forall₂ t (zip_pair_Forall₂ choice h)

/-! ## §5.5: Validity discharge for `listChoices`-derived pair lists -/

/-- Every path in a `choice.zip Ts` pair list is a valid path in `T`, when
    `choice ∈ listChoices (vertices T) Ts.length`. Discharges the validity
    hypothesis of the graft operations for `listChoices`-derived pair lists. -/
theorem forall_zip_isValidPath_of_listChoices
    (T : RoseTree α) (Ts : List (RoseTree α))
    (choice : List Path)
    (h_choice : choice ∈ listChoices (vertices T) Ts.length)
    (pair : Path × RoseTree α) (h_pair : pair ∈ choice.zip Ts) :
    IsValidPath pair.fst T := by
  exact forall_isValidPath T ((mem_listChoices.mp h_choice).2 _ (List.of_mem_zip h_pair).1)

/-! ## §6: Host invariance via path-swap bijection

`insertion T Ts` is `mk`-invariant under `Perm` of the host: the
original blocker for the path-based refactor.

Strategy:
1. `swapPathAt n` — swap the first index `n ↔ n+1` in a path.
2. `vertices_swap_perm` — applying `swapPathAt pre.length` to vertices of
   `node a (pre ++ l :: r :: post)` is a `List.Perm` of vertices of
   `node a (pre ++ r :: l :: post)`. Reduces to a `List.Perm` of two
   appendable middle blocks, via `verticesAux_append` + a
   `List.perm_append_comm`.
3. `multiGraft_swap_perm` — the multiGraft results differ only by
   the swap of l/r in the root children list.
4. `vertices_recurse_perm` / `multiGraft_recurse_perm` — the child-recursion
   building block, lifting an inner bijection via `pathLiftRecurse`.
5. `hasPathBij_of_perm` (with its `PermList` companion) assembles these
   building blocks over the mutual `Perm`/`PermList` structure;
   `insertion_eq_of_pathBij` turns the bijection into `mk`-equality. -/

/-- Swap the first index `n ↔ n+1` of a path. Acts as identity on paths
    starting outside `{n, n+1}` and on the root path `[]`. -/
private def swapPathAt (n : ℕ) : Path → Path
  | []        => []
  | i :: rest =>
      if i = n then (n + 1) :: rest
      else if i = n + 1 then n :: rest
      else i :: rest

@[simp] private theorem swapPathAt_nil (n : ℕ) : swapPathAt n [] = [] := rfl

private theorem swapPathAt_cons_eq (n : ℕ) (rest : Path) :
    swapPathAt n (n :: rest) = (n + 1) :: rest := by
  simp [swapPathAt]

private theorem swapPathAt_cons_eq_succ (n : ℕ) (rest : Path) :
    swapPathAt n ((n + 1) :: rest) = n :: rest := by
  simp [swapPathAt]

private theorem swapPathAt_cons_of_ne (n i : ℕ) (rest : Path)
    (h1 : i ≠ n) (h2 : i ≠ n + 1) :
    swapPathAt n (i :: rest) = i :: rest := by
  simp [swapPathAt, h1, h2]

/-- For paths produced by `verticesAux start cs` with all indices
    bounded below `n`, `swapPathAt n` acts as the identity. -/
private theorem map_swapPathAt_verticesAux_below
    (n start : ℕ) (cs : List (RoseTree α)) (h : start + cs.length ≤ n) :
    (verticesAux start cs).map (swapPathAt n) = verticesAux start cs := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    rw [verticesAux_cons, List.map_append, List.map_map]
    have hlt : start < n := by simp [List.length_cons] at h; omega
    have hcs : start + 1 + cs.length ≤ n := by
      simp [List.length_cons] at h; omega
    congr 1
    · refine List.map_congr_left fun q _ => ?_
      show swapPathAt n (start :: q) = start :: q
      exact swapPathAt_cons_of_ne n start q (Nat.ne_of_lt hlt) (by omega)
    · exact ih (start + 1) hcs

/-- For paths produced by `verticesAux start cs` with all indices
    bounded above `n + 1`, `swapPathAt n` acts as the identity. -/
private theorem map_swapPathAt_verticesAux_above
    (n start : ℕ) (cs : List (RoseTree α)) (h : n + 1 < start) :
    (verticesAux start cs).map (swapPathAt n) = verticesAux start cs := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    rw [verticesAux_cons, List.map_append, List.map_map]
    have h' : n + 1 < start + 1 := by omega
    congr 1
    · refine List.map_congr_left fun q _ => ?_
      show swapPathAt n (start :: q) = start :: q
      exact swapPathAt_cons_of_ne n start q (by omega) (by omega)
    · exact ih (start + 1) h'

/-- Vertices of `node a (pre ++ l :: r :: post)` mapped through
    `swapPathAt pre.length` is a `List.Perm` of vertices of
    `node a (pre ++ r :: l :: post)`. -/
private theorem vertices_swap_perm (a : α) (pre : List (RoseTree α))
    (l r : RoseTree α) (post : List (RoseTree α)) :
    ((vertices (RoseTree.node a (pre ++ l :: r :: post))).map
        (swapPathAt pre.length)).Perm
      (vertices (RoseTree.node a (pre ++ r :: l :: post))) := by
  set n := pre.length with hn
  rw [vertices_node, vertices_node]
  -- Expand verticesAux via _append, plus verticesAux_cons twice
  rw [verticesAux_append, verticesAux_append, Nat.zero_add,
      verticesAux_cons, verticesAux_cons, verticesAux_cons, verticesAux_cons,
      List.map_cons]
  rw [swapPathAt_nil]
  refine List.Perm.cons _ ?_
  -- Distribute List.map over ++
  rw [List.map_append, List.map_append, List.map_append]
  -- pre's slice: identity
  rw [map_swapPathAt_verticesAux_below n 0 pre (by simp [hn])]
  -- post's slice: identity
  rw [map_swapPathAt_verticesAux_above n (n + 2) post (by omega)]
  -- l's slice: n → n+1
  have hl : (List.map (fun x => n :: x) (vertices l)).map (swapPathAt n) =
            List.map (fun x => (n + 1) :: x) (vertices l) := by
    rw [List.map_map]
    refine List.map_congr_left fun q _ => ?_
    exact swapPathAt_cons_eq n q
  -- r's slice: n+1 → n
  have hr : (List.map (fun x => (n + 1) :: x) (vertices r)).map (swapPathAt n) =
            List.map (fun x => n :: x) (vertices r) := by
    rw [List.map_map]
    refine List.map_congr_left fun q _ => ?_
    exact swapPathAt_cons_eq_succ n q
  rw [hl, hr]
  -- Goal: pre' ++ (l@n+1) ++ ((r@n) ++ post') ~ pre' ++ ((r@n) ++ ((l@n+1) ++ post'))
  -- Common prefix `pre'` peels off; then swap two middle blocks.
  refine List.Perm.append_left _ ?_
  rw [← List.append_assoc, ← List.append_assoc]
  refine List.Perm.append_right _ ?_
  exact List.perm_append_comm

/-! ### §6.2 substrate: pair-relabel + perm prefix-cons-lift -/

/-- The path-relabel function for swapAtRoot. -/
private def pathRelabelSwap (n : ℕ) : Path × RoseTree α → Path × RoseTree α :=
  Prod.map (swapPathAt n) id

@[simp] private theorem pathRelabelSwap_fst (n : ℕ) (p : Path × RoseTree α) :
    (pathRelabelSwap n p).fst = swapPathAt n p.fst := rfl

@[simp] private theorem pathRelabelSwap_snd (n : ℕ) (p : Path × RoseTree α) :
    (pathRelabelSwap n p).snd = p.snd := rfl

/-- Path bijection for a single-child recursion: lift an inner path
    bijection `f` (applicable to vertices of the changed subtree at child
    position `n`) to the whole tree. Identity on paths not going through
    child `n`. -/
private def pathLiftRecurse (n : ℕ) (f : Path → Path) : Path → Path
  | []        => []
  | i :: rest => if i = n then n :: f rest else i :: rest

@[simp] private theorem pathLiftRecurse_nil (n : ℕ) (f : Path → Path) :
    pathLiftRecurse n f [] = [] := rfl

private theorem pathLiftRecurse_cons_eq (n : ℕ) (f : Path → Path) (rest : Path) :
    pathLiftRecurse n f (n :: rest) = n :: f rest := by
  simp [pathLiftRecurse]

private theorem pathLiftRecurse_cons_of_ne (n i : ℕ) (f : Path → Path) (rest : Path)
    (h : i ≠ n) :
    pathLiftRecurse n f (i :: rest) = i :: rest := by
  simp [pathLiftRecurse, h]

/-- `pathLiftRecurse n f` acts as identity on paths produced by
    `verticesAux start cs` when those paths' first indices are all below `n`. -/
private theorem map_pathLiftRecurse_verticesAux_below
    (n start : ℕ) (f : Path → Path) (cs : List (RoseTree α))
    (h : start + cs.length ≤ n) :
    (verticesAux start cs).map (pathLiftRecurse n f) = verticesAux start cs := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    rw [verticesAux_cons, List.map_append, List.map_map]
    have hlt : start < n := by simp [List.length_cons] at h; omega
    have hcs : start + 1 + cs.length ≤ n := by simp [List.length_cons] at h; omega
    congr 1
    · refine List.map_congr_left fun q _ => ?_
      show pathLiftRecurse n f (start :: q) = start :: q
      exact pathLiftRecurse_cons_of_ne n start f q (Nat.ne_of_lt hlt)
    · exact ih (start + 1) hcs

/-- `pathLiftRecurse n f` acts as identity on paths produced by
    `verticesAux start cs` when those paths' first indices are all above `n`. -/
private theorem map_pathLiftRecurse_verticesAux_above
    (n start : ℕ) (f : Path → Path) (cs : List (RoseTree α))
    (h : n < start) :
    (verticesAux start cs).map (pathLiftRecurse n f) = verticesAux start cs := by
  induction cs generalizing start with
  | nil => rfl
  | cons c cs ih =>
    rw [verticesAux_cons, List.map_append, List.map_map]
    have h' : n < start + 1 := by omega
    congr 1
    · refine List.map_congr_left fun q _ => ?_
      show pathLiftRecurse n f (start :: q) = start :: q
      exact pathLiftRecurse_cons_of_ne n start f q (by omega : start ≠ n)
    · exact ih (start + 1) h'

/-- Vertices Perm under a single-child recursion: given a path bijection on
    the changed subtree, lift to a Perm on the bigger tree's vertices. -/
private theorem vertices_recurse_perm (a : α) (pre : List (RoseTree α))
    (old new : RoseTree α) (post : List (RoseTree α)) (f : Path → Path)
    (hf : ((vertices old).map f).Perm (vertices new)) :
    ((vertices (RoseTree.node a (pre ++ old :: post))).map
        (pathLiftRecurse pre.length f)).Perm
      (vertices (RoseTree.node a (pre ++ new :: post))) := by
  set n := pre.length with hn_eq
  rw [vertices_node, vertices_node,
      verticesAux_append, verticesAux_append, Nat.zero_add,
      verticesAux_cons, verticesAux_cons, List.map_cons, pathLiftRecurse_nil]
  refine List.Perm.cons _ ?_
  rw [List.map_append, List.map_append]
  rw [map_pathLiftRecurse_verticesAux_below n 0 f pre (by simp [hn_eq])]
  rw [map_pathLiftRecurse_verticesAux_above n (n + 1) f post (by omega)]
  -- Goal: pre' ++ ((vertices old).map (n :: ·)).map (pathLiftRecurse n f) ++ post' ~Perm~
  --       pre' ++ (vertices new).map (n :: ·) ++ post'
  refine List.Perm.append_left _ (List.Perm.append_right _ ?_)
  -- Goal: ((vertices old).map (n :: ·)).map (pathLiftRecurse n f) ~Perm~ (vertices new).map (n :: ·)
  rw [List.map_map]
  -- Goal: List.map (pathLiftRecurse n f ∘ fun x => n :: x) (vertices old) ~Perm~ ...
  have h_map_eq : List.map (pathLiftRecurse n f ∘ fun x => n :: x) (vertices old) =
                  ((vertices old).map f).map (fun x => n :: x) := by
    rw [List.map_map]
    refine List.map_congr_left fun q _ => ?_
    show pathLiftRecurse n f (n :: q) = n :: f q
    exact pathLiftRecurse_cons_eq n f q
  rw [h_map_eq]
  exact hf.map _

/-- Helper: `Perm` of two trees with a common children prefix.
    Lifts `(node a cs) ~ (node a ds)` to `(node a (pre ++ cs)) ~ (node a (pre ++ ds))`
    by iterated `Perm.cons_child`. -/
private theorem perm_append_left_node {a : α} (pre : List (RoseTree α))
    {cs ds : List (RoseTree α)}
    (h : Perm (.node a cs) (.node a ds)) :
    Perm (.node a (pre ++ cs)) (.node a (pre ++ ds)) := by
  induction pre with
  | nil => exact h
  | cons p pre' ih => exact Perm.cons_child p ih

/-- `multiGraft` is `Perm`-invariant under a single-child recursion:
    if the inner subtree change `old → new` admits a path-bijection `f`
    that turns `multiGraft old` into `multiGraft new ∘ relabel-via-f`, then
    the same holds for the host with prefix `pre` and suffix `post`, using
    `pathLiftRecurse pre.length f`. -/
private theorem multiGraft_recurse_perm (a : α)
    {old new : RoseTree α} (f : Path → Path)
    (hf : ∀ sub_pairs, Perm (multiGraft old sub_pairs)
                                    (multiGraft new (sub_pairs.map (Prod.map f id)))) :
    ∀ (pre : List (RoseTree α)) (post : List (RoseTree α))
      (pairs : List (Path × RoseTree α)),
    Perm
      (multiGraft (RoseTree.node a (pre ++ old :: post)) pairs)
      (multiGraft (RoseTree.node a (pre ++ new :: post))
                  (pairs.map (Prod.map (pathLiftRecurse pre.length f) id))) := by
  intro pre post pairs
  induction pre generalizing pairs with
  | nil =>
    simp only [List.nil_append, List.length_nil]
    rw [multiGraft_node, multiGraft_node]
    rw [multiGraftChildren_cons_cs old post, multiGraftChildren_cons_cs new post]
    -- Three filter equalities.
    have h_RP : pairs.filterMap rootPrependFilter =
                (pairs.map (Prod.map (pathLiftRecurse 0 f) id)).filterMap
                  rootPrependFilter := by
      rw [List.filterMap_map]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, rootPrependFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = 0
        · subst h1; simp [hp, rootPrependFilter, pathLiftRecurse]
        · simp [hp, rootPrependFilter, pathLiftRecurse_cons_of_ne 0 i f rest h1]
    have h_cP : (pairs.filterMap headChildFilter).map (Prod.map f id) =
                (pairs.map (Prod.map (pathLiftRecurse 0 f) id)).filterMap
                  headChildFilter := by
      rw [List.filterMap_map, List.map_filterMap]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, headChildFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = 0
        · subst h1; simp [hp, headChildFilter, pathLiftRecurse_cons_eq]
        · simp [hp, headChildFilter,
                pathLiftRecurse_cons_of_ne 0 i f rest h1]
          cases i with
          | zero => exact absurd rfl h1
          | succ k => rfl
    have h_csP : pairs.filterMap tailChildFilter =
                 (pairs.map (Prod.map (pathLiftRecurse 0 f) id)).filterMap
                   tailChildFilter := by
      rw [List.filterMap_map]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = 0
        · subst h1; simp [hp, tailChildFilter, pathLiftRecurse_cons_eq]
        · simp [hp, tailChildFilter, pathLiftRecurse_cons_of_ne 0 i f rest h1]
    -- Use hf on the head child; identity on root prepends and post; lift via recurse.
    have h_old := hf (pairs.filterMap headChildFilter)
    rw [h_cP] at h_old
    rw [← h_RP, ← h_csP]
    -- Goal: node a (RP ++ multiGraft old cP :: mGC post csP) ~PE~
    --        node a (RP ++ multiGraft new cP' :: mGC post csP) where
    --        cP' = (pairs.map ...).filterMap headChildFilter = cP.map (Prod.map f id)
    exact perm_append_left_node _
      (Perm.congr_child [] _ h_old)
  | cons c pre' ih =>
    rw [show (c :: pre') ++ old :: post = c :: (pre' ++ old :: post) from rfl,
        show (c :: pre') ++ new :: post = c :: (pre' ++ new :: post) from rfl,
        show (c :: pre').length = pre'.length + 1 from rfl]
    rw [multiGraft_node, multiGraft_node]
    rw [multiGraftChildren_cons_cs c (pre' ++ old :: post),
        multiGraftChildren_cons_cs c (pre' ++ new :: post)]
    -- Three filter equalities.
    have h_RP : pairs.filterMap rootPrependFilter =
                (pairs.map (Prod.map (pathLiftRecurse (pre'.length + 1) f) id)).filterMap
                  rootPrependFilter := by
      rw [List.filterMap_map]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, rootPrependFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1; simp [hp, rootPrependFilter, pathLiftRecurse_cons_eq]
        · simp [hp, rootPrependFilter,
                pathLiftRecurse_cons_of_ne (pre'.length + 1) i f rest h1]
    have h_cP : pairs.filterMap headChildFilter =
                (pairs.map (Prod.map (pathLiftRecurse (pre'.length + 1) f) id)).filterMap
                  headChildFilter := by
      rw [List.filterMap_map]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, headChildFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1
          simp [hp, headChildFilter, pathLiftRecurse_cons_eq]
        · simp [hp, headChildFilter,
                pathLiftRecurse_cons_of_ne (pre'.length + 1) i f rest h1]
    have h_csP : (pairs.filterMap tailChildFilter).map
                   (Prod.map (pathLiftRecurse pre'.length f) id) =
                 (pairs.map (Prod.map (pathLiftRecurse (pre'.length + 1) f) id)).filterMap
                   tailChildFilter := by
      rw [List.filterMap_map, List.map_filterMap]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1
          simp [hp, tailChildFilter, pathLiftRecurse_cons_eq,
                pathLiftRecurse_cons_eq pre'.length f rest]
        · simp [hp, tailChildFilter,
                pathLiftRecurse_cons_of_ne (pre'.length + 1) i f rest h1]
          cases i with
          | zero => simp
          | succ j =>
            have hjne : j ≠ pre'.length := by intro heq; apply h1; omega
            simp [pathLiftRecurse_cons_of_ne pre'.length j f rest hjne]
    -- Apply IH on pre' with input csP (= pairs.filterMap tailChildFilter).
    -- IH gives PE on multiGrafts; unfold via multiGraft_node and discard empty rootPrepends
    -- (tailChildFilter only produces non-empty fsts).
    have h_ih := ih (pairs.filterMap tailChildFilter)
    rw [h_csP] at h_ih
    rw [multiGraft_node, multiGraft_node] at h_ih
    have h_RP_lhs : (pairs.filterMap tailChildFilter).filterMap rootPrependFilter = [] := by
      rw [List.filterMap_filterMap]
      apply List.filterMap_eq_nil_iff.mpr
      intro pair _
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter]
      | cons i rest =>
        cases i with
        | zero => simp [hp, tailChildFilter]
        | succ j => simp [hp, tailChildFilter, rootPrependFilter]
    have h_RP_rhs : ((pairs.map (Prod.map (pathLiftRecurse (pre'.length + 1) f) id)).filterMap
                       tailChildFilter).filterMap rootPrependFilter = [] := by
      rw [List.filterMap_filterMap, List.filterMap_map]
      apply List.filterMap_eq_nil_iff.mpr
      intro pair _
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter, pathLiftRecurse]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1
          simp [hp, tailChildFilter, pathLiftRecurse_cons_eq, rootPrependFilter]
        · simp [hp, tailChildFilter,
                pathLiftRecurse_cons_of_ne (pre'.length + 1) i f rest h1]
          cases i with
          | zero => simp
          | succ j => simp [rootPrependFilter]
    rw [h_RP_lhs, List.nil_append] at h_ih
    rw [h_RP_rhs, List.nil_append] at h_ih
    rw [← h_RP, ← h_cP]
    -- Goal: node a (RP ++ multiGraft c cP :: mGC (pre' ++ old :: post) csP) ~PE~
    --        node a (RP ++ multiGraft c cP :: mGC (pre' ++ new :: post) csP_relabeled)
    exact perm_append_left_node _ (Perm.cons_child _ h_ih)

/-- `multiGraft` is `Perm`-invariant under swap of two adjacent
    root children, with pairs relabeled via `swapPathAt`. The proof
    decomposes both sides into matching children lists (up to a single
    swap of the two adjacent root children).

    Sub-lemmas for the filter equalities are proved inline as `have`
    statements to ensure the inline-match expressions unify with the
    matcher generated by `multiGraft_node`. -/
private theorem multiGraft_swap_perm
    (a : α) (pre : List (RoseTree α)) (l r : RoseTree α)
    (post : List (RoseTree α)) (pairs : List (Path × RoseTree α)) :
    Perm
      (multiGraft (RoseTree.node a (pre ++ l :: r :: post)) pairs)
      (multiGraft (RoseTree.node a (pre ++ r :: l :: post))
                  (pairs.map (pathRelabelSwap pre.length))) := by
  -- The cleanest path: induct on pre, peeling off one child at a time.
  -- Base case (pre = []) does the actual swap; inductive case lifts via
  -- Perm.cons_child.
  induction pre generalizing pairs with
  | nil =>
    simp only [List.nil_append, List.length_nil]
    rw [multiGraft_node, multiGraft_node]
    -- Build sub-perms and combine via Perm.node_of_perm.
    have h_RP_perm : (pairs.filterMap fun pair => match pair.fst with
                                                    | []     => some pair.snd
                                                    | _ :: _ => none).Perm
                      ((pairs.map (pathRelabelSwap 0)).filterMap
                          fun pair => match pair.fst with
                                       | []     => some pair.snd
                                       | _ :: _ => none) := by
      rw [List.filterMap_map]
      apply List.Perm.of_eq
      refine List.filterMap_congr fun pair _ => ?_
      simp only [Function.comp, pathRelabelSwap_fst, pathRelabelSwap_snd]
      cases hp : pair.fst with
      | nil => rw [swapPathAt_nil]
      | cons i rest =>
        by_cases h1 : i = 0
        · subst h1; rw [swapPathAt_cons_eq]
        · by_cases h2 : i = 1
          · subst h2; rw [swapPathAt_cons_eq_succ]
          · rw [swapPathAt_cons_of_ne 0 i rest h1 h2]
    have h_mGC_perm : (multiGraftChildren (l :: r :: post) pairs).Perm
                      (multiGraftChildren (r :: l :: post)
                          (pairs.map (pathRelabelSwap 0))) := by
      -- Decompose both via cons_cs (now using top-level filter helpers).
      rw [multiGraftChildren_cons_cs l (r :: post),
          multiGraftChildren_cons_cs r (l :: post),
          multiGraftChildren_cons_cs r post,
          multiGraftChildren_cons_cs l post]
      -- Three filter equalities, each via List.filterMap_map +
      -- List.filterMap_filterMap + List.filterMap_congr + case analysis.
      have h_l : pairs.filterMap headChildFilter =
                 ((pairs.map (pathRelabelSwap 0)).filterMap tailChildFilter).filterMap
                    headChildFilter := by
        rw [List.filterMap_map, List.filterMap_filterMap]
        refine List.filterMap_congr fun pair _ => ?_
        cases hp : pair.fst with
        | nil => simp [hp, headChildFilter, tailChildFilter]
        | cons i rest =>
          by_cases h1 : i = 0
          · subst h1; simp [hp, headChildFilter, tailChildFilter,
                            pathRelabelSwap, swapPathAt]
          · by_cases h2 : i = 1
            · subst h2; simp [hp, headChildFilter, tailChildFilter,
                              pathRelabelSwap, swapPathAt]
            · cases i with
              | zero => exact absurd rfl h1
              | succ j =>
                cases j with
                | zero => exact absurd rfl h2
                | succ k => simp [hp, headChildFilter, tailChildFilter,
                                  pathRelabelSwap, swapPathAt]
      have h_r : (pairs.filterMap tailChildFilter).filterMap headChildFilter =
                 (pairs.map (pathRelabelSwap 0)).filterMap headChildFilter := by
        rw [List.filterMap_map, List.filterMap_filterMap]
        refine List.filterMap_congr fun pair _ => ?_
        cases hp : pair.fst with
        | nil => simp [hp, headChildFilter, tailChildFilter]
        | cons i rest =>
          by_cases h1 : i = 0
          · subst h1; simp [hp, headChildFilter, tailChildFilter,
                            pathRelabelSwap, swapPathAt]
          · by_cases h2 : i = 1
            · subst h2; simp [hp, headChildFilter, tailChildFilter,
                              pathRelabelSwap, swapPathAt]
            · cases i with
              | zero => exact absurd rfl h1
              | succ j =>
                cases j with
                | zero => exact absurd rfl h2
                | succ k => simp [hp, headChildFilter, tailChildFilter,
                                  pathRelabelSwap, swapPathAt]
      have h_post : (pairs.filterMap tailChildFilter).filterMap tailChildFilter =
                    ((pairs.map (pathRelabelSwap 0)).filterMap tailChildFilter).filterMap
                       tailChildFilter := by
        rw [List.filterMap_map, List.filterMap_filterMap, List.filterMap_filterMap]
        refine List.filterMap_congr fun pair _ => ?_
        cases hp : pair.fst with
        | nil => simp [hp, tailChildFilter]
        | cons i rest =>
          by_cases h1 : i = 0
          · subst h1; simp [hp, tailChildFilter, pathRelabelSwap, swapPathAt]
          · by_cases h2 : i = 1
            · subst h2; simp [hp, tailChildFilter, pathRelabelSwap, swapPathAt]
            · cases i with
              | zero => exact absurd rfl h1
              | succ j =>
                cases j with
                | zero => exact absurd rfl h2
                | succ k => simp [hp, tailChildFilter, pathRelabelSwap, swapPathAt]
      rw [h_l, h_r, h_post]
      exact List.Perm.swap _ _ _
    exact Perm.node_of_perm (List.Perm.append h_RP_perm h_mGC_perm)
  | cons c pre' ih =>
    -- pre = c :: pre'. n = pre'.length + 1.
    -- Strategy: peel off `c` via multiGraftChildren_cons_cs, identify the
    -- rootPrepends and head-child filter (invariant under relabel-at-(n+1)
    -- since the relabel only swaps indices n+1, n+2), then apply IH on
    -- pre' with input = pairs.filterMap tailChildFilter.
    rw [show (c :: pre') ++ l :: r :: post = c :: (pre' ++ l :: r :: post) from rfl,
        show (c :: pre') ++ r :: l :: post = c :: (pre' ++ r :: l :: post) from rfl,
        show (c :: pre').length = pre'.length + 1 from rfl]
    rw [multiGraft_node, multiGraft_node]
    rw [multiGraftChildren_cons_cs c (pre' ++ l :: r :: post),
        multiGraftChildren_cons_cs c (pre' ++ r :: l :: post)]
    -- Three filter equalities.
    have h_RP : pairs.filterMap rootPrependFilter =
                (pairs.map (pathRelabelSwap (pre'.length + 1))).filterMap
                  rootPrependFilter := by
      rw [List.filterMap_map]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, rootPrependFilter, pathRelabelSwap, swapPathAt]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1; simp [hp, rootPrependFilter, pathRelabelSwap, swapPathAt]
        · by_cases h2 : i = pre'.length + 1 + 1
          · subst h2; simp [hp, rootPrependFilter, pathRelabelSwap, swapPathAt]
          · simp [hp, rootPrependFilter, pathRelabelSwap,
                  swapPathAt_cons_of_ne (pre'.length + 1) i rest h1 h2]
    have h_X_l : pairs.filterMap headChildFilter =
                 (pairs.map (pathRelabelSwap (pre'.length + 1))).filterMap
                   headChildFilter := by
      rw [List.filterMap_map]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, headChildFilter, pathRelabelSwap, swapPathAt]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1; simp [hp, headChildFilter, pathRelabelSwap, swapPathAt]
        · by_cases h2 : i = pre'.length + 1 + 1
          · subst h2; simp [hp, headChildFilter, pathRelabelSwap, swapPathAt]
          · simp [hp, headChildFilter, pathRelabelSwap,
                  swapPathAt_cons_of_ne (pre'.length + 1) i rest h1 h2]
    have h_X_pre : (pairs.map (pathRelabelSwap (pre'.length + 1))).filterMap
                       tailChildFilter =
                   (pairs.filterMap tailChildFilter).map
                       (pathRelabelSwap pre'.length) := by
      rw [List.filterMap_map, List.map_filterMap]
      refine List.filterMap_congr fun pair _ => ?_
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter, pathRelabelSwap, swapPathAt]
      | cons i rest =>
        by_cases h1 : i = pre'.length + 1
        · subst h1
          simp [hp, tailChildFilter, pathRelabelSwap, swapPathAt]
        · by_cases h2 : i = pre'.length + 1 + 1
          · subst h2
            simp [hp, tailChildFilter, pathRelabelSwap, swapPathAt]
          · cases i with
            | zero =>
              simp [hp, tailChildFilter, pathRelabelSwap,
                    swapPathAt_cons_of_ne (pre'.length + 1) 0 rest h1 h2]
            | succ j =>
              have hjne : j ≠ pre'.length := by intro heq; apply h1; omega
              have hjne2 : j ≠ pre'.length + 1 := by intro heq; apply h2; omega
              simp [hp, tailChildFilter, pathRelabelSwap,
                    swapPathAt_cons_of_ne (pre'.length + 1) (j + 1) rest h1 h2,
                    swapPathAt_cons_of_ne pre'.length j rest hjne hjne2]
    -- Use IH on pre' with input = pairs.filterMap tailChildFilter.
    have h_ih := ih (pairs.filterMap tailChildFilter)
    -- IH: Perm (multiGraft (node a (pre' ++ l :: r :: post)) X_pre)
    --                 (multiGraft (node a (pre' ++ r :: l :: post)) (X_pre.map ...))
    -- Unfold both sides of IH to expose mGC.
    rw [multiGraft_node, multiGraft_node] at h_ih
    -- The rootPrepends in h_ih's LHS: (pairs.filterMap tailChildFilter).filterMap rootPrependFilter.
    -- tailChildFilter never outputs empty fst, so this is [].
    have h_empty_RP_lhs :
        (pairs.filterMap tailChildFilter).filterMap rootPrependFilter = [] := by
      rw [List.filterMap_filterMap]
      apply List.filterMap_eq_nil_iff.mpr
      intro pair _
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter]
      | cons i rest =>
        cases i with
        | zero => simp [hp, tailChildFilter]
        | succ j => simp [hp, tailChildFilter, rootPrependFilter]
    have h_empty_RP_rhs :
        ((pairs.filterMap tailChildFilter).map (pathRelabelSwap pre'.length)).filterMap
          rootPrependFilter = [] := by
      rw [List.filterMap_map, List.filterMap_filterMap]
      apply List.filterMap_eq_nil_iff.mpr
      intro pair _
      cases hp : pair.fst with
      | nil => simp [hp, tailChildFilter]
      | cons i rest =>
        cases i with
        | zero => simp [hp, tailChildFilter]
        | succ j =>
          by_cases hj1 : j = pre'.length
          · subst hj1
            simp [hp, tailChildFilter, pathRelabelSwap, rootPrependFilter,
                  swapPathAt_cons_eq]
          · by_cases hj2 : j = pre'.length + 1
            · subst hj2
              simp [hp, tailChildFilter, pathRelabelSwap, rootPrependFilter,
                    swapPathAt_cons_eq_succ]
            · simp [hp, tailChildFilter, pathRelabelSwap, rootPrependFilter,
                    swapPathAt_cons_of_ne pre'.length j rest hj1 hj2]
    rw [h_empty_RP_lhs, List.nil_append] at h_ih
    rw [h_empty_RP_rhs, List.nil_append] at h_ih
    -- Now h_ih has form: Perm (node a (mGC ... X_pre)) (node a (mGC ... X_pre_relabeled))
    -- Use h_X_pre to rewrite X_pre_relabeled inside.
    rw [← h_X_pre] at h_ih
    -- Lift IH through cons (multiGraft c X_l ::) and append_left (RP ++).
    have h_after_cons : Perm
        (RoseTree.node a (multiGraft c (pairs.filterMap headChildFilter) ::
                         multiGraftChildren (pre' ++ l :: r :: post)
                           (pairs.filterMap tailChildFilter)))
        (RoseTree.node a (multiGraft c (pairs.filterMap headChildFilter) ::
                         multiGraftChildren (pre' ++ r :: l :: post)
                           ((pairs.map (pathRelabelSwap (pre'.length + 1))).filterMap
                             tailChildFilter))) :=
      Perm.cons_child _ h_ih
    have h_after_append := perm_append_left_node
                            (pairs.filterMap rootPrependFilter) h_after_cons
    -- Goal's RHS uses relabeled forms; rewrite back to unrelabeled to match
    -- h_after_append.
    rw [← h_RP, ← h_X_l]
    exact h_after_append

/-! ### §6.3 substrate for `insertion_perm_host`

The `swapAtRoot` case of `insertion_permStep_host` needs to lift a Perm
of vertices into a Perm of choice lists (via `listChoices`), then combine
with `multiGraft_swap_perm` to get equal `mk`-mapped insertion
outputs. Helpers below build this bridge. -/

/-- `listChoices` respects `List.Perm` of the source: a Perm of `xs` and
    `ys` lifts to a Perm of `listChoices xs n` and `listChoices ys n`. -/
private theorem listChoices_perm {β : Type*} {xs ys : List β}
    (h : xs.Perm ys) (n : Nat) :
    (listChoices xs n).Perm (listChoices ys n) := by
  induction n with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    rw [listChoices_succ, listChoices_succ]
    refine h.flatMap (fun b _ => ?_)
    exact ih.map _

/-- Generic lifting: a path bijection `f` that turns vertices of `t` into a
    `Perm` of vertices of `t'` and turns `multiGraft t pairs` into a
    `Perm` of `multiGraft t' (pairs.map (Prod.map f id))` lifts to
    `mk`-equality of `insertion t Ts` and `insertion t' Ts`. -/
private theorem insertion_eq_of_pathBij {t t' : RoseTree α}
    (f : Path → Path)
    (hf_perm : ((vertices t).map f).Perm (vertices t'))
    (hf_graft : ∀ pairs, Perm (multiGraft t pairs)
                                      (multiGraft t' (pairs.map (Prod.map f id))))
    (Ts : List (RoseTree α)) :
    (insertion t Ts).map UnorderedTree.mk = (insertion t' Ts).map UnorderedTree.mk := by
  rw [insertion_def, insertion_def, Multiset.map_coe, Multiset.map_coe,
      List.map_map, List.map_map]
  refine Quot.sound ?_
  have hlc_eq : listChoices ((vertices t).map f) Ts.length =
                (listChoices (vertices t) Ts.length).map (List.map f) :=
    listChoices_map _ _ _
  have hlc_perm := listChoices_perm hf_perm Ts.length
  rw [hlc_eq] at hlc_perm
  -- LHS values agree with t'-multiGraft after relabel; RHS values are just t'-multiGraft.
  have step1 :
      ((listChoices (vertices t) Ts.length).map
          (fun choice => UnorderedTree.mk (multiGraft t (choice.zip Ts)))).Perm
      ((listChoices (vertices t) Ts.length).map
          (fun choice => UnorderedTree.mk (multiGraft t' ((choice.map f).zip Ts)))) := by
    apply List.Perm.of_eq
    apply List.map_congr_left
    intro choice _
    apply UnorderedTree.mk_eq_mk_iff.mpr
    have h_mge := hf_graft (choice.zip Ts)
    have h_zip : (choice.zip Ts).map (Prod.map f id) = (choice.map f).zip Ts := by
      simp [List.zip_map_left]
    rw [h_zip] at h_mge
    exact h_mge
  have step2 :
      ((listChoices (vertices t) Ts.length).map
          (fun choice => UnorderedTree.mk (multiGraft t' ((choice.map f).zip Ts)))).Perm
      ((listChoices (vertices t') Ts.length).map
          (fun choice => UnorderedTree.mk (multiGraft t' (choice.zip Ts)))) := by
    have := hlc_perm.map (fun choice => UnorderedTree.mk (multiGraft t' (choice.zip Ts)))
    rw [List.map_map] at this
    exact this
  exact step1.trans step2

/-- A path bijection `f` relating the vertex enumeration and `multiGraft`
    behaviour of `t` and `t'`, the data `insertion_eq_of_pathBij` turns into
    `mk`-equality. Reflexive and transitive, and produced by every `Perm`
    of hosts (`hasPathBij_of_perm`). -/
private def HasPathBij (t t' : RoseTree α) : Prop :=
  ∃ f : Path → Path,
    ((vertices t).map f).Perm (vertices t') ∧
    ∀ pairs, Perm (multiGraft t pairs)
                  (multiGraft t' (pairs.map (Prod.map f id)))

private theorem HasPathBij.refl (t : RoseTree α) : HasPathBij t t :=
  ⟨id, by simp, fun pairs => by simpa using Perm.refl _⟩

private theorem HasPathBij.trans {t t' t'' : RoseTree α}
    (h₁ : HasPathBij t t') (h₂ : HasPathBij t' t'') : HasPathBij t t'' := by
  obtain ⟨f, hvf, hgf⟩ := h₁
  obtain ⟨g, hvg, hgg⟩ := h₂
  refine ⟨g ∘ f, ?_, fun pairs => ?_⟩
  · rw [← List.map_map]
    exact (hvf.map g).trans hvg
  · refine (hgf pairs).trans ?_
    have h := hgg (pairs.map (Prod.map f id))
    rw [List.map_map,
        show (Prod.map g id ∘ Prod.map f id) = Prod.map (g ∘ f) id from
          funext fun _ => rfl] at h
    exact h

mutual
/-- Every `Perm` of hosts admits a path bijection. For a `swap` of two root
    children the bijection is `swapPathAt`; for a `cons` (a `Perm` on one
    child) it is `pathLiftRecurse` of the child's bijection; both thread a
    child-prefix context via the mutually-recursive `PermList` companion. -/
private theorem hasPathBij_of_perm :
    ∀ {t t' : RoseTree α}, Perm t t' → HasPathBij t t'
  | _, _, .node h => hasPathBij_of_permList h _ []
  | _, _, .trans h₁ h₂ => (hasPathBij_of_perm h₁).trans (hasPathBij_of_perm h₂)

/-- Companion of `hasPathBij_of_perm`: a `PermList` of children, in any
    prefix context, gives a path bijection on the enclosing node. -/
private theorem hasPathBij_of_permList :
    ∀ {cs ds : List (RoseTree α)}, PermList cs ds →
      ∀ (a : α) (pre : List (RoseTree α)),
        HasPathBij (.node a (pre ++ cs)) (.node a (pre ++ ds))
  | _, _, .nil, _, _ => .refl _
  | _, _, @PermList.cons _ c d cs ds hcd hs, a, pre => by
    obtain ⟨f, hvf, hgf⟩ := hasPathBij_of_perm hcd
    have head : HasPathBij (.node a (pre ++ c :: cs)) (.node a (pre ++ d :: cs)) :=
      ⟨pathLiftRecurse pre.length f,
       vertices_recurse_perm a pre c d cs f hvf,
       fun pairs => multiGraft_recurse_perm a f hgf pre cs pairs⟩
    have tail := hasPathBij_of_permList hs a (pre ++ [d])
    simp only [List.append_assoc, List.singleton_append] at tail
    exact head.trans tail
  | _, _, .swap c d cs, a, pre =>
    ⟨swapPathAt pre.length, vertices_swap_perm a pre d c cs,
     fun pairs => multiGraft_swap_perm a pre d c cs pairs⟩
  | _, _, .trans h₁ h₂, a, pre =>
    (hasPathBij_of_permList h₁ a pre).trans (hasPathBij_of_permList h₂ a pre)
end

/-- `insertion T Ts` is `mk`-invariant under `Perm` of the host. -/
private theorem insertion_perm_host (Ts : List (RoseTree α))
    {t t' : RoseTree α} (h : Perm t t') :
    (insertion t Ts).map UnorderedTree.mk =
      (insertion t' Ts).map UnorderedTree.mk := by
  obtain ⟨f, hf_perm, hf_graft⟩ := hasPathBij_of_perm h
  exact insertion_eq_of_pathBij f hf_perm hf_graft Ts

/-- `List.Forall₂ Perm` lifts to `List` equality after mapping by
    `UnorderedTree.mk` — used for the `Ts = []` base case of forest host
    invariance. -/
private theorem map_mk_eq_of_forall2_perm {F F' : List (RoseTree α)}
    (h : List.Forall₂ Perm F F') :
    F.map UnorderedTree.mk = F'.map UnorderedTree.mk := by
  induction h with
  | nil => rfl
  | cons hd_pe _ ih => simp [UnorderedTree.mk_eq_mk_iff.mpr hd_pe, ih]

/-- Forest host invariance: `Forall₂ Perm F F'` lifts to
    `mk`-equality of `insertionForest F Ts` and `insertionForest F' Ts`. -/
theorem insertionForest_perm_host
    (Ts : List (RoseTree α)) {F F' : List (RoseTree α)}
    (h : List.Forall₂ Perm F F') :
    (insertionForest F Ts).map (List.map UnorderedTree.mk) =
      (insertionForest F' Ts).map (List.map UnorderedTree.mk) := by
  induction h generalizing Ts with
  | nil => rfl
  | @cons T T' F_tail F'_tail hd_pe _ ih =>
    rw [insertionForest_cons, insertionForest_cons, Multiset.map_bind, Multiset.map_bind]
    refine Multiset.bind_congr fun p _ => ?_
    rw [Multiset.map_bind, Multiset.map_bind]
    simp only [Multiset.map_map, Function.comp, List.map_cons]
    let f_T : UnorderedTree α → Multiset (List (UnorderedTree α)) := fun mk_T_ins =>
      (insertionForest F_tail p.2).map (fun F_ins => mk_T_ins :: F_ins.map UnorderedTree.mk)
    let f_T' : UnorderedTree α → Multiset (List (UnorderedTree α)) := fun mk_T_ins =>
      (insertionForest F'_tail p.2).map (fun F_ins => mk_T_ins :: F_ins.map UnorderedTree.mk)
    change (insertion T _).bind (fun T_ins => f_T (UnorderedTree.mk T_ins)) =
      (insertion T' _).bind (fun T_ins => f_T' (UnorderedTree.mk T_ins))
    rw [← Multiset.bind_map, ← Multiset.bind_map, insertion_perm_host _ hd_pe]
    refine Multiset.bind_congr fun mk_T_ins _ => ?_
    show (insertionForest F_tail _).map (fun F_ins => mk_T_ins :: F_ins.map UnorderedTree.mk) =
      (insertionForest F'_tail _).map (fun F_ins => mk_T_ins :: F_ins.map UnorderedTree.mk)
    rw [show (fun F_ins : List (RoseTree α) => mk_T_ins :: F_ins.map UnorderedTree.mk) =
        ((fun L : List (UnorderedTree α) => mk_T_ins :: L) ∘ List.map UnorderedTree.mk) from rfl,
      ← Multiset.map_map, ← Multiset.map_map, ih]

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

/-! ### §8: Singleton-host insertion = single-tree insertion lifted to singleton lists

`insertionForest [T] gs = (insertion T gs).map (fun T' => [T'])` — when the
host has exactly one tree, the multi-graft is just the single-tree multi-graft
with each output wrapped in a singleton list. -/

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
