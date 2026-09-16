/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Algebra.RootedTree.PreLie.Insertion
import Linglib.Core.Algebra.RootedTree.PreLie.InsertionAddHost
import Linglib.Core.Data.List.Sublists

/-!
# Node-host decomposition of the multi-graft insertion

Grafting guests `gs` into the host `node a cs` decomposes by which guests land at the root
(prepended as new children, in guest order) and which land inside the child forest. The guest
split is mathlib's subset/complement enumeration `gs.sublists'.revzip`, so the decomposition
descends to `Multiset.powerset` through `Multiset.coe_revzip_sublists'`.

## Main results

* `bind_listChoices_filter`: the keystone. A sum over vertex choices from an alphabet `xs`, seen
  through the two buckets of a predicate on `xs`, is a sum over `gs.sublists'.revzip` of
  independent choices for each bucket.
* `insertionForest_cons`: the host-forest recursion in `revzip` form.
* `insertionForest_eq_map_listChoices`: `insertionForest` in vertex-choice form, the forest
  analogue of `insertion_def`.
* `insertion_node`: the node-host decomposition.

## References

* [foissy-typed-decorated-rooted-trees-2018]
* [foissy-introduction-hopf-algebras-trees]
-/

namespace RoseTree

namespace Pathed

open RoseTree

variable {α β γ δ : Type*}

/-! ### Guest splits as `sublists'.revzip` -/

/-- Enumerating Boolean masks over `gs` and reading off the two buckets enumerates
`gs.sublists'.revzip`. -/
theorem bind_listChoices_bool (gs : List β) (H : List β → List β → Multiset δ) :
    (listChoices [true, false] gs.length : Multiset (List Bool)).bind (fun m =>
        H ((gs.zip m).filterMap fun p => if p.2 then some p.1 else none)
          ((gs.zip m).filterMap fun p => if p.2 then none else some p.1)) =
      (gs.sublists'.revzip : Multiset (List β × List β)).bind fun p => H p.1 p.2 := by
  induction gs generalizing H with
  | nil => simp
  | cons g gs ih =>
    rw [List.length_cons, coe_listChoices_succ, Multiset.bind_assoc,
      show (([true, false] : List Bool) : Multiset Bool) = true ::ₘ {false} from rfl,
      Multiset.cons_bind, Multiset.singleton_bind, Multiset.bind_map, Multiset.bind_map,
      List.revzip_sublists'_cons, ← Multiset.coe_add, Multiset.add_bind, ← Multiset.map_coe,
      ← Multiset.map_coe, Multiset.bind_map, Multiset.bind_map]
    simp only [List.zip_cons_cons, List.filterMap_cons, Bool.false_eq_true, ite_true, ite_false,
      Prod.map_fst, Prod.map_snd, id_eq]
    rw [ih fun r s => H (g :: r) s, ih fun r s => H r (g :: s), add_comm]

/-- **Keystone.** A sum over length-`gs.length` choices from `xs`, viewed through the two
buckets of a predicate `P` on `xs`, is a sum over `gs.sublists'.revzip` of independent choices
from `xs.filter P` for the first bucket and from its complement for the second. -/
theorem bind_listChoices_filter (P : β → Prop) [DecidablePred P] (xs : List β) (gs : List γ)
    (G : List (β × γ) → List (β × γ) → Multiset δ) :
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

/-! ### The host-forest recursion and its closed form -/

/-- The host-forest recursion: the head host takes a sublist of the guests, the tail forest the
complement. -/
theorem insertionForest_cons (T : RoseTree α) (F gs : List (RoseTree α)) :
    insertionForest (T :: F) gs =
      (gs.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun p =>
        (insertion T p.1).bind fun T' => (insertionForest F p.2).map (T' :: ·) := by
  rw [insertionForest_cons_assignment]
  exact bind_listChoices_bool gs fun r s =>
    (insertion T r).bind fun T' => (insertionForest F s).map (T' :: ·)

/-- Zipping a mapped list and undoing the map on the first components. -/
private theorem map_zip_map_left {β' : Type*} {f : β → β'} {f' : β' → β}
    (h : ∀ x, f' (f x) = x) (l : List β) (r : List γ) :
    ((l.map f).zip r).map (Prod.map f' id) = l.zip r := by
  rw [List.zip_map_left, List.map_map]
  exact (List.map_congr_left fun ⟨x, y⟩ _ => by simp [h]).trans (List.map_id _)

/-- `insertionForest` in vertex-choice form: the forest analogue of `insertion_def`, summing
`multiGraftChildren` over assignments of guests to forest vertices. -/
theorem insertionForest_eq_map_listChoices (cs gs : List (RoseTree α)) :
    insertionForest cs gs =
      ((listChoices (verticesAux 0 cs) gs.length).map fun ch =>
        multiGraftChildren cs (ch.zip gs) : List (List (RoseTree α))) := by
  induction cs generalizing gs with
  | nil =>
    cases gs with
    | nil => rw [insertionForest_nil_nil]; rfl
    | cons g gs => rw [insertionForest_empty_host_nonempty_guests]; simp
  | cons c cs ih =>
    have hne : ∀ p ∈ verticesAux 0 (c :: cs), p ≠ [] := fun p hp => by
      obtain ⟨k, q, -, rfl⟩ := exists_cons_of_mem_verticesAux hp
      exact List.cons_ne_nil k q
    have hG : ∀ ch ∈ (listChoices (verticesAux 0 (c :: cs)) gs.length : Multiset (List Path)),
        ({multiGraftChildren (c :: cs) (ch.zip gs)} : Multiset (List (RoseTree α))) =
          {multiGraft c (((ch.zip gs).filter fun p => decide (p.1.head? = some 0)).map
              (Prod.map List.tail id)) ::
            multiGraftChildren cs (((ch.zip gs).filter fun p => decide (¬ p.1.head? = some 0)).map
              (Prod.map (List.modifyHead (· - 1)) id))} := by
      intro ch hch
      rw [multiGraftChildren_cons_cs, filterMap_headChildFilter, filterMap_tailChildFilter]
      exact fun p hp =>
        hne _ ((mem_listChoices.mp (Multiset.mem_coe.mp hch)).2 _ (List.of_mem_zip hp).1)
    have hfilter :
        (verticesAux 0 (c :: cs)).filter (fun q : Path => decide (q.head? = some 0)) =
            (vertices c).map (0 :: ·) ∧
          (verticesAux 0 (c :: cs)).filter (fun q : Path => decide (¬ q.head? = some 0)) =
            (verticesAux 0 cs).map (List.modifyHead (· + 1)) := by
      rw [verticesAux_cons, Nat.zero_add, verticesAux_eq_map_modifyHead 1 cs, List.filter_append,
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
    rw [← Multiset.map_coe, ← Multiset.bind_singleton, Multiset.bind_congr hG,
      bind_listChoices_filter (fun q : Path => q.head? = some 0) _ gs fun a b =>
        {multiGraft c (a.map (Prod.map List.tail id)) ::
          multiGraftChildren cs (b.map (Prod.map (List.modifyHead (· - 1)) id))},
      hfilter.1, hfilter.2, insertionForest_cons]
    refine Multiset.bind_congr fun p _ => ?_
    rw [insertion_def, ih, ← Multiset.map_coe, ← Multiset.map_coe, Multiset.bind_map,
      listChoices_map, listChoices_map, ← Multiset.map_coe, ← Multiset.map_coe,
      Multiset.bind_map]
    refine Multiset.bind_congr fun u _ => ?_
    rw [Multiset.bind_map, Multiset.map_map, ← Multiset.bind_singleton]
    refine Multiset.bind_congr fun w _ => ?_
    rw [map_zip_map_left fun _ => rfl, map_zip_map_left fun q => by cases q <;> simp]
    rfl

/-! ### The node-host decomposition -/

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
    List.map_snd_zip (by simp), insertionForest_eq_map_listChoices, ← Multiset.map_coe,
    Multiset.map_map, ← Multiset.bind_singleton]
  rfl

end Pathed

end RoseTree
