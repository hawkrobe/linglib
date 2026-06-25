/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Combinatorics.RootedTree.Nonplanar

/-!
# Computable decidable equality for `Planar` and `Nonplanar`

The single-carrier program (MCB §1.1–1.2, `scratch/mcb-single-carrier-spec.md`) needs the
syntactic-object carrier to support `decide` so that study-level predictions stay
kernel-checked. This file supplies the two `DecidableEq` instances that make that possible:

- `DecidableEq (Planar α)` — strict structural equality of ordered n-ary trees, via a
  `beq` decider proven correct (`deriving DecidableEq` does not apply to the nested-`List`
  inductive).
- `DecidableEq (Nonplanar α)` — equality of *nonplanar* trees, i.e. equality up to child
  reordering. Decided by `Planar.eqv` (match children as a multiset-under-`≈`), proven to
  characterize `PlanarEquiv`. **Both are computable and reduce in the kernel** — the P0 spike
  confirmed `by decide` closes `eqv`-equalities — so SOs on `Nonplanar` keep `decide` (the
  noncomputable `Nonplanar.node` is avoidable: build via `mk ∘ Planar.node`).
-/

namespace RootedTree.Planar

variable {α : Type*} [DecidableEq α]

/-! ### Strict structural equality: `DecidableEq (Planar α)` -/

mutual
/-- Structural boolean equality of planar trees (ordered children). -/
def beq : Planar α → Planar α → Bool
  | .node a cs, .node b ds => decide (a = b) && beqList cs ds
/-- Auxiliary: componentwise boolean equality of child lists. -/
def beqList : List (Planar α) → List (Planar α) → Bool
  | [], [] => true
  | c :: cs, d :: ds => beq c d && beqList cs ds
  | _, _ => false
end

mutual
theorem beq_iff_eq : ∀ (t s : Planar α), beq t s = true ↔ t = s
  | .node a cs, .node b ds => by
    rw [beq, Bool.and_eq_true, decide_eq_true_eq, beqList_iff_eq cs ds, Planar.node.injEq]
theorem beqList_iff_eq : ∀ (cs ds : List (Planar α)), beqList cs ds = true ↔ cs = ds
  | [], [] => by simp [beqList]
  | [], _ :: _ => by simp [beqList]
  | _ :: _, [] => by simp [beqList]
  | c :: cs, d :: ds => by
    rw [beqList, Bool.and_eq_true, beq_iff_eq c d, beqList_iff_eq cs ds, List.cons.injEq]
end

instance instDecidableEq : DecidableEq (Planar α) :=
  fun t s => decidable_of_iff (beq t s = true) (beq_iff_eq t s)

/-! ### Equality up to child reordering: deciding `PlanarEquiv` -/

mutual
/-- Decide whether two planar trees are **equal up to child reordering** (i.e.
    `PlanarEquiv` — represent the same `Nonplanar` tree): same root label, and the
    child lists match as multisets under `eqv` (each child of one matched to a distinct
    `eqv`-equal child of the other). Computable; needs only `DecidableEq α`. -/
def eqv : Planar α → Planar α → Bool
  | .node a cs, .node b ds => decide (a = b) && eqvMulti cs ds
/-- Auxiliary: match two child lists as multisets under `eqv`. Greedily pair each head of
    the left list with an `eqv`-equal element of the right, removing it. -/
def eqvMulti : List (Planar α) → List (Planar α) → Bool
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | c :: cs, ds =>
    match ds.findIdx? (fun d => eqv c d) with
    | some i => eqvMulti cs (ds.eraseIdx i)
    | none => false
end

/-! #### Correctness of `eqv` — internal machinery

`eqvMulti` greedily matches each left child to the first `eqv`-equal right child and erases
it. The matching succeeds iff the two child lists are equal as *multisets under `eqv`*,
which we package as `Match cs ds := ∃ ds', Forall₂ (eqv · ·) cs ds' ∧ ds'.Perm ds`. From
there: `eqv` is reflexive/symmetric/transitive and respects a single `PlanarStep`, giving
`PlanarEquiv → eqv`; and `Match` reads back through `planarEquiv_node_componentwise` +
`planarEquiv_root_perm`, giving `eqv → PlanarEquiv`. Symmetry and transitivity of `eqv`
are mutually entangled at the children level (the greedy `Match`-readback needs both), so
they are proven together by strong induction on a per-tree size bound. -/

/-- Unfolding lemma for `eqvMulti` on a `cons` left and non-empty right. -/
private theorem eqvMulti_cons_left (c : Planar α) (cs ds : List (Planar α)) (h : ds ≠ []) :
    eqvMulti (c :: cs) ds =
      match ds.findIdx? (fun d => eqv c d) with
      | some i => eqvMulti cs (ds.eraseIdx i)
      | none => false :=
  eqvMulti.eq_4 ds c cs (fun he => h he)

/-- `cs` and `ds` match as multisets under `eqv`: some reordering of `ds` is componentwise
    `eqv`-equal to `cs`. -/
private def Match (cs ds : List (Planar α)) : Prop :=
  ∃ ds', List.Forall₂ (fun c d => eqv c d = true) cs ds' ∧ ds'.Perm ds

/-- Soundness of the greedy matcher: `eqvMulti cs ds = true → Match cs ds`. -/
private theorem eqvMulti_to_match :
    ∀ (cs ds : List (Planar α)), eqvMulti cs ds = true → Match cs ds
  | [], [], _ => ⟨[], .nil, .refl _⟩
  | [], _ :: _, h => by rw [eqvMulti] at h; exact absurd h (by simp)
  | _ :: _, [], h => by rw [eqvMulti] at h; exact absurd h (by simp)
  | c :: cs, d :: ds, h => by
    rw [eqvMulti_cons_left c cs (d :: ds) (by simp)] at h
    cases hfind : (d :: ds).findIdx? (fun x => eqv c x) with
    | none => rw [hfind] at h; exact absurd h (by simp)
    | some i =>
      rw [hfind] at h
      rw [List.findIdx?_eq_some_iff_getElem] at hfind
      obtain ⟨hi, hpi, _⟩ := hfind
      obtain ⟨es', hf', hperm'⟩ := eqvMulti_to_match cs ((d :: ds).eraseIdx i) h
      refine ⟨(d :: ds)[i] :: es', List.Forall₂.cons hpi hf', ?_⟩
      exact (hperm'.cons _).trans (List.getElem_cons_eraseIdx_perm hi)

/-- Swap step for completeness: matching `c` to the greedily-found `d` and rebuilding the
    leftover match for `cs` against `(e :: es).erase d`. The reattachment of the floating
    `e` to `d`'s old partner uses symmetry and transitivity of `eqv` on the children
    (supplied through the bound predicate `P`). -/
private theorem forall₂_cons_erase_match {P : Planar α → Prop}
    (Ssymm : ∀ x y, P x → P y → eqv x y = true → eqv y x = true)
    (Strans : ∀ x y z, P x → P y → P z → eqv x y = true → eqv y z = true → eqv x z = true)
    {c e : Planar α} (hPc : P c) (hPe : P e) (hce : eqv c e = true)
    {cs es : List (Planar α)} (hPcs : ∀ x ∈ cs, P x) (hPes : ∀ x ∈ es, P x)
    (hcs : List.Forall₂ (fun c d => eqv c d = true) cs es) :
    ∀ {d : Planar α}, P d → eqv c d = true → d ∈ e :: es →
      ∃ X, List.Forall₂ (fun c d => eqv c d = true) cs X ∧ X.Perm ((e :: es).erase d) := by
  induction hcs with
  | nil =>
    intro d _ _ hd
    rw [List.mem_singleton] at hd
    exact ⟨[], List.Forall₂.nil, by rw [hd, List.erase_cons_head]⟩
  | @cons a b cs₀ es₀ hab hcs₀ ih =>
    intro d hPd hcd hd
    have hPa : P a := hPcs a List.mem_cons_self
    have hPb : P b := hPes b List.mem_cons_self
    have hPcs₀ : ∀ x ∈ cs₀, P x := fun x hx => hPcs x (List.mem_cons_of_mem _ hx)
    have hPes₀ : ∀ x ∈ es₀, P x := fun x hx => hPes x (List.mem_cons_of_mem _ hx)
    by_cases hde : d = e
    · exact ⟨b :: es₀, List.Forall₂.cons hab hcs₀, by rw [hde, List.erase_cons_head]⟩
    · have hdes : d ∈ b :: es₀ := (List.mem_cons.mp hd).resolve_left hde
      have hne : ¬ (e == d) = true := by simpa using (fun h => hde h.symm)
      rw [List.erase_cons_tail hne]
      by_cases hdb : d = b
      · have hcb : eqv c b = true := hdb ▸ hcd
        have hca : eqv c a = true := Strans c b a hPc hPb hPa hcb (Ssymm a b hPa hPb hab)
        have hae : eqv a e = true := Strans a c e hPa hPc hPe (Ssymm c a hPc hPa hca) hce
        exact ⟨e :: es₀, List.Forall₂.cons hae hcs₀, by rw [← hdb, List.erase_cons_head]⟩
      · have hd₀ : d ∈ es₀ := (List.mem_cons.mp hdes).resolve_left hdb
        have hbd : ¬ (b == d) = true := by simpa using (fun h => hdb h.symm)
        obtain ⟨X₀, hX₀f, hX₀p⟩ := ih hPcs₀ hPes₀ hPd hcd (List.mem_cons_of_mem _ hd₀)
        rw [List.erase_cons_tail hbd]
        refine ⟨b :: X₀, List.Forall₂.cons hab hX₀f, ?_⟩
        rw [List.erase_cons_tail hne] at hX₀p
        exact (hX₀p.cons b).trans (List.Perm.swap e b _)

/-- Completeness of the greedy matcher: `Match cs ds → eqvMulti cs ds = true`, given
    symmetry and transitivity of `eqv` on the children (via the bound predicate `P`). -/
private theorem match_to_eqvMulti {P : Planar α → Prop}
    (Ssymm : ∀ x y, P x → P y → eqv x y = true → eqv y x = true)
    (Strans : ∀ x y z, P x → P y → P z → eqv x y = true → eqv y z = true → eqv x z = true) :
    ∀ (cs ds : List (Planar α)), (∀ x ∈ cs, P x) → (∀ x ∈ ds, P x) →
      Match cs ds → eqvMulti cs ds = true
  | [], ds, _, _, ⟨ds', hf, hperm⟩ => by
    rw [List.forall₂_nil_left_iff.mp hf] at hperm
    rw [hperm.symm.eq_nil, eqvMulti]
  | c :: cs, ds, hPcs, hPds, ⟨ds', hf, hperm⟩ => by
    obtain ⟨e, es, hce, hf', rfl⟩ := List.forall₂_cons_left_iff.mp hf
    have hPc : P c := hPcs c List.mem_cons_self
    have hPcs' : ∀ x ∈ cs, P x := fun x hx => hPcs x (List.mem_cons_of_mem _ hx)
    have hPe : P e := hPds e (hperm.subset List.mem_cons_self)
    have hPes : ∀ x ∈ es, P x := fun x hx => hPds x (hperm.subset (List.mem_cons_of_mem _ hx))
    have heds : e ∈ ds := hperm.subset List.mem_cons_self
    have hfi : ds.findIdx? (fun x => eqv c x) = some (ds.findIdx (fun x => eqv c x)) :=
      List.findIdx?_eq_some_of_exists ⟨e, heds, hce⟩
    have hne : ds ≠ [] := by rintro rfl; simp at heds
    rw [eqvMulti_cons_left c cs ds hne, hfi]
    set i := ds.findIdx (fun x => eqv c x)
    rw [List.findIdx?_eq_some_iff_getElem] at hfi
    obtain ⟨hi, hpi, _⟩ := hfi
    set d := ds[i] with hd
    have hPd : P d := hPds d (List.getElem_mem hi)
    obtain ⟨X, hXf, hXp⟩ :=
      forall₂_cons_erase_match Ssymm Strans hPc hPe hce hPcs' hPes hf' hPd hpi
        (hperm.symm.subset (List.getElem_mem hi))
    apply match_to_eqvMulti Ssymm Strans cs (ds.eraseIdx i) hPcs'
      (fun x hx => hPds x ((List.eraseIdx_sublist ds i).subset hx))
    exact ⟨X, hXf, (hXp.trans (hperm.erase d)).trans (List.erase_getElem hi)⟩

/-- Composing two `eqv`-`Forall₂` matchings, using transitivity on the children. -/
private theorem forall₂_eqv_trans {P : Planar α → Prop}
    (Strans : ∀ x y z, P x → P y → P z → eqv x y = true → eqv y z = true → eqv x z = true) :
    ∀ {cs ds es : List (Planar α)}, (∀ x ∈ cs, P x) → (∀ x ∈ ds, P x) → (∀ x ∈ es, P x) →
      List.Forall₂ (fun c d => eqv c d = true) cs ds →
      List.Forall₂ (fun c d => eqv c d = true) ds es →
      List.Forall₂ (fun c d => eqv c d = true) cs es
  | _, _, _, _, _, _, List.Forall₂.nil, h2 => by cases h2; exact List.Forall₂.nil
  | c :: cs', _, _, hPc, hPd, hPe, List.Forall₂.cons hab hcs, h2 => by
    obtain ⟨b', es₀, hbb', hes₀, rfl⟩ := List.forall₂_cons_left_iff.mp h2
    refine List.Forall₂.cons (Strans _ _ _ (hPc _ List.mem_cons_self) (hPd _ List.mem_cons_self)
      (hPe _ List.mem_cons_self) hab hbb') ?_
    exact forall₂_eqv_trans Strans (fun x hx => hPc x (List.mem_cons_of_mem _ hx))
      (fun x hx => hPd x (List.mem_cons_of_mem _ hx))
      (fun x hx => hPe x (List.mem_cons_of_mem _ hx)) hcs hes₀

/-- `Match` is symmetric, given symmetry of `eqv` on the children. -/
private theorem match_symm {P : Planar α → Prop}
    (Ssymm : ∀ x y, P x → P y → eqv x y = true → eqv y x = true)
    {cs ds : List (Planar α)} (hPcs : ∀ x ∈ cs, P x) (hPds : ∀ x ∈ ds, P x)
    (h : Match cs ds) : Match ds cs := by
  obtain ⟨ds', hf, hperm⟩ := h
  have hPds' : ∀ x ∈ ds', P x := fun x hx => hPds x (hperm.subset hx)
  have hf' : List.Forall₂ (fun c d => eqv c d = true) ds' cs := by
    clear hperm
    induction hf with
    | nil => exact List.Forall₂.nil
    | @cons a b cs₀ ds₀ hab _ ih =>
      exact List.Forall₂.cons (Ssymm a b (hPcs a List.mem_cons_self) (hPds' b List.mem_cons_self) hab)
        (ih (fun x hx => hPcs x (List.mem_cons_of_mem _ hx))
            (fun x hx => hPds' x (List.mem_cons_of_mem _ hx)))
  obtain ⟨cs', h1, h2⟩ := List.perm_comp_forall₂ hperm.symm hf'
  exact ⟨cs', h1, h2⟩

/-- `Match` is transitive, given transitivity of `eqv` on the children. -/
private theorem match_trans {P : Planar α → Prop}
    (Strans : ∀ x y z, P x → P y → P z → eqv x y = true → eqv y z = true → eqv x z = true)
    {cs ds es : List (Planar α)} (hPcs : ∀ x ∈ cs, P x) (hPds : ∀ x ∈ ds, P x)
    (hPes : ∀ x ∈ es, P x) (h1 : Match cs ds) (h2 : Match ds es) : Match cs es := by
  obtain ⟨ds', hf1, hp1⟩ := h1
  obtain ⟨es', hf2, hp2⟩ := h2
  have hPds' : ∀ x ∈ ds', P x := fun x hx => hPds x (hp1.subset hx)
  obtain ⟨m, hm1, hm2⟩ := List.perm_comp_forall₂ hp1 hf2
  have hPm : ∀ x ∈ m, P x := fun x hx => (fun y hy => hPes y (hp2.subset hy)) x (hm2.subset hx)
  exact ⟨m, forall₂_eqv_trans Strans hPcs hPds' hPm hf1 hm1, hm2.trans hp2⟩

omit [DecidableEq α] in
/-- A child of a node is strictly smaller than the node (for the size induction). -/
private theorem sizeOf_child_lt {a : α} {cs : List (Planar α)} {c : Planar α} (hc : c ∈ cs) :
    sizeOf c < sizeOf (Planar.node a cs) := by
  have := List.sizeOf_lt_of_mem hc
  simp only [Planar.node.sizeOf_spec]; omega

omit [DecidableEq α] in
/-- Every tree has at least one vertex. -/
private theorem one_le_sizeOf (t : Planar α) : 1 ≤ sizeOf t := by
  cases t with
  | node a cs => simp only [Planar.node.sizeOf_spec]; omega

/-- `eqv` on two nodes unfolds to label equality and `eqvMulti` on children. -/
private theorem eqv_node {a b : α} {cs ds : List (Planar α)} :
    eqv (.node a cs) (.node b ds) = (decide (a = b) && eqvMulti cs ds) := by rw [eqv]

/-- Symmetry and transitivity of `eqv`, proven together by strong induction on a per-tree
    size bound: the `Match`-readback at a node needs both symmetry and transitivity on the
    (strictly smaller) children. -/
private theorem eqv_symm_trans :
    ∀ N, (∀ t s : Planar α, sizeOf t ≤ N → sizeOf s ≤ N →
            (eqv t s = true → eqv s t = true)) ∧
         (∀ t s u : Planar α, sizeOf t ≤ N → sizeOf s ≤ N → sizeOf u ≤ N →
            (eqv t s = true → eqv s u = true → eqv t u = true)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    refine ⟨?_, ?_⟩
    · rintro ⟨a, cs⟩ ⟨b, ds⟩ hst hss hts
      rw [eqv_node, Bool.and_eq_true, decide_eq_true_eq] at hts
      obtain ⟨hab, hmulti⟩ := hts
      have hNpos : 1 ≤ N := le_trans (one_le_sizeOf (Planar.node a cs)) hst
      have hcsN : ∀ x ∈ cs, sizeOf x ≤ N - 1 := fun x hx => by
        have := lt_of_lt_of_le (sizeOf_child_lt hx) hst; omega
      have hdsN : ∀ x ∈ ds, sizeOf x ≤ N - 1 := fun x hx => by
        have := lt_of_lt_of_le (sizeOf_child_lt hx) hss; omega
      have ihm := ih (N - 1) (by omega)
      have Psymm : ∀ x y, sizeOf x ≤ N - 1 → sizeOf y ≤ N - 1 →
          eqv x y = true → eqv y x = true := fun x y => ihm.1 x y
      have Ptrans : ∀ x y z, sizeOf x ≤ N - 1 → sizeOf y ≤ N - 1 → sizeOf z ≤ N - 1 →
          eqv x y = true → eqv y z = true → eqv x z = true := fun x y z => ihm.2 x y z
      rw [eqv_node, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hab.symm, ?_⟩
      have hMs : Match ds cs := match_symm Psymm hcsN hdsN (eqvMulti_to_match cs ds hmulti)
      exact match_to_eqvMulti Psymm Ptrans ds cs hdsN hcsN hMs
    · rintro ⟨a, cs⟩ ⟨b, ds⟩ ⟨c, es⟩ hst hss hsu hts hsu'
      rw [eqv_node, Bool.and_eq_true, decide_eq_true_eq] at hts
      obtain ⟨hab, hm1⟩ := hts
      rw [eqv_node, Bool.and_eq_true, decide_eq_true_eq] at hsu'
      obtain ⟨hbc, hm2⟩ := hsu'
      have hNpos : 1 ≤ N := le_trans (one_le_sizeOf (Planar.node a cs)) hst
      have hcsN : ∀ x ∈ cs, sizeOf x ≤ N - 1 := fun x hx => by
        have := lt_of_lt_of_le (sizeOf_child_lt hx) hst; omega
      have hdsN : ∀ x ∈ ds, sizeOf x ≤ N - 1 := fun x hx => by
        have := lt_of_lt_of_le (sizeOf_child_lt hx) hss; omega
      have hesN : ∀ x ∈ es, sizeOf x ≤ N - 1 := fun x hx => by
        have := lt_of_lt_of_le (sizeOf_child_lt hx) hsu; omega
      have ihm := ih (N - 1) (by omega)
      have Psymm : ∀ x y, sizeOf x ≤ N - 1 → sizeOf y ≤ N - 1 →
          eqv x y = true → eqv y x = true := fun x y => ihm.1 x y
      have Ptrans : ∀ x y z, sizeOf x ≤ N - 1 → sizeOf y ≤ N - 1 → sizeOf z ≤ N - 1 →
          eqv x y = true → eqv y z = true → eqv x z = true := fun x y z => ihm.2 x y z
      rw [eqv_node, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hab.trans hbc, ?_⟩
      have hM : Match cs es := match_trans Ptrans hcsN hdsN hesN
        (eqvMulti_to_match cs ds hm1) (eqvMulti_to_match ds es hm2)
      exact match_to_eqvMulti Psymm Ptrans cs es hcsN hesN hM

/-- Symmetry of `eqv`. -/
private theorem eqv_symm {t s : Planar α} (h : eqv t s = true) : eqv s t = true :=
  (eqv_symm_trans (max (sizeOf t) (sizeOf s))).1 t s (le_max_left _ _) (le_max_right _ _) h

/-- Transitivity of `eqv`. -/
private theorem eqv_trans {t s u : Planar α} (h1 : eqv t s = true) (h2 : eqv s u = true) :
    eqv t u = true :=
  (eqv_symm_trans (max (sizeOf t) (max (sizeOf s) (sizeOf u)))).2 t s u
    (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_trans (le_max_right _ _) (le_max_right _ _)) h1 h2

/-! Reflexivity of `eqv`, with its `eqvMulti` companion. -/
mutual
private theorem eqv_refl : ∀ (t : Planar α), eqv t t = true
  | .node a cs => by
    rw [eqv]
    simp only [Bool.and_eq_true, decide_true, true_and]
    exact eqvMulti_refl cs
private theorem eqvMulti_refl : ∀ (cs : List (Planar α)), eqvMulti cs cs = true
  | [] => by rw [eqvMulti]
  | c :: cs => by
    rw [eqvMulti_cons_left c cs (c :: cs) (by simp)]
    have h0 : (c :: cs).findIdx? (fun d => eqv c d) = some 0 := by
      rw [List.findIdx?_cons]; simp [eqv_refl c]
    rw [h0]
    simp only [List.eraseIdx_cons_zero]
    exact eqvMulti_refl cs
end

/-- `Match cs ds` reads back to `eqvMulti cs ds = true` (unbounded — symmetry and
    transitivity of `eqv` are now globally available). -/
private theorem eqvMulti_of_match {cs ds : List (Planar α)} (h : Match cs ds) :
    eqvMulti cs ds = true :=
  match_to_eqvMulti (P := fun _ => True)
    (fun _ _ _ _ hxy => eqv_symm hxy)
    (fun _ _ _ _ _ _ hxy hyz => eqv_trans hxy hyz)
    cs ds (fun _ _ => trivial) (fun _ _ => trivial) h

/-- `Forall₂ eqv` is reflexive on a list. -/
private theorem forall₂_eqv_refl (cs : List (Planar α)) :
    List.Forall₂ (fun c d => eqv c d = true) cs cs := by
  induction cs with
  | nil => exact List.Forall₂.nil
  | cons c cs ih => exact List.Forall₂.cons (eqv_refl c) ih

/-- `eqvMulti` accepts permutation-equal child lists. -/
private theorem eqvMulti_of_perm {cs ds : List (Planar α)} (hperm : cs.Perm ds) :
    eqvMulti cs ds = true :=
  eqvMulti_of_match ⟨cs, forall₂_eqv_refl cs, hperm⟩

/-- `eqv` respects a single `PlanarStep`. -/
private theorem eqv_step {t s : Planar α} (h : PlanarStep t s) : eqv t s = true := by
  induction h with
  | @swapAtRoot a l r pre post =>
    rw [eqv_node, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨rfl, eqvMulti_of_perm ((List.Perm.swap r l post).append_left pre)⟩
  | @recurse a pre old new post _ ih =>
    rw [eqv_node, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨rfl, eqvMulti_of_match
      ⟨pre ++ new :: post,
        List.rel_append (forall₂_eqv_refl pre) (List.Forall₂.cons ih (forall₂_eqv_refl post)),
        List.Perm.refl _⟩⟩

/-- (←) `PlanarEquiv → eqv`, by `EqvGen` induction. -/
private theorem planarEquiv_to_eqv {t s : Planar α} (h : PlanarEquiv t s) : eqv t s = true := by
  induction h with
  | rel _ _ hstep => exact eqv_step hstep
  | refl t => exact eqv_refl t
  | symm _ _ _ ih => exact eqv_symm ih
  | trans _ _ _ _ _ ih1 ih2 => exact eqv_trans ih1 ih2

/-! (→) `eqv → PlanarEquiv`, by structural induction (mutual with the child-list version). -/
mutual
private theorem eqv_to_planarEquiv : ∀ (t s : Planar α), eqv t s = true → PlanarEquiv t s
  | .node a cs, .node b ds, h => by
    rw [eqv_node, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hab, hmulti⟩ := h
    subst hab
    obtain ⟨ds', hf, hperm⟩ := eqvMulti_to_match cs ds hmulti
    exact (planarEquiv_node_componentwise
      (eqv_forall₂_to_planarEquiv cs ds' hf)).trans (planarEquiv_root_perm hperm)
private theorem eqv_forall₂_to_planarEquiv :
    ∀ (cs ds' : List (Planar α)),
      List.Forall₂ (fun c d => eqv c d = true) cs ds' → List.Forall₂ PlanarEquiv cs ds'
  | [], [], _ => List.Forall₂.nil
  | c :: cs, d :: ds', h => by
    obtain ⟨hcd, hrest⟩ := List.forall₂_cons.mp h
    exact List.Forall₂.cons (eqv_to_planarEquiv c d hcd)
      (eqv_forall₂_to_planarEquiv cs ds' hrest)
end

/-- **Soundness/completeness of `eqv`**: it decides `PlanarEquiv` (the nonplanar quotient
    relation). The P0 spike confirmed the *computation* (`by decide` closes `eqv`
    equalities); this lemma is the formal characterization that makes
    `DecidableEq (Nonplanar α)` honest.

    Proof: (←) `PlanarEquiv → eqv` by `EqvGen` induction (`planarEquiv_to_eqv`), using that
    `eqv` is reflexive/symmetric/transitive and respects each `PlanarStep` (swap = child
    permutation, recurse = componentwise); (→) `eqv → PlanarEquiv` by structural induction
    (`eqv_to_planarEquiv`), reading the greedy match back through
    `planarEquiv_node_componentwise` + `planarEquiv_root_perm`. -/
theorem eqv_iff_planarEquiv : ∀ (t s : Planar α), eqv t s = true ↔ PlanarEquiv t s :=
  fun t s => ⟨eqv_to_planarEquiv t s, planarEquiv_to_eqv⟩

end RootedTree.Planar

namespace RootedTree.Nonplanar

variable {α : Type*} [DecidableEq α]

/-- Equality of nonplanar trees (= equality up to child reordering) is decidable and
    **computable**: decided by `Planar.eqv` on representatives, which reduces in the kernel,
    so concrete `Nonplanar` equalities `decide`. This is the keystone that lets the
    syntactic-object carrier move onto `Nonplanar` without losing `decide`. -/
instance instDecidableEq : DecidableEq (Nonplanar α) := fun t s =>
  Quotient.recOnSubsingleton₂ t s fun a b =>
    decidable_of_iff (Planar.eqv a b = true)
      (by rw [Planar.eqv_iff_planarEquiv]; exact Nonplanar.mk_eq_mk_iff.symm)

end RootedTree.Nonplanar
