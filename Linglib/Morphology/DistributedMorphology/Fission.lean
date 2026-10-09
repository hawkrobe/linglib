module

public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Multiset.AddSub

/-!
# Fission

Fission lets one syntactic node be realized in several adjacent positions of exponence. A
Vocabulary Item inserted at the node discharges only the features it spells out, and the remaining
features fission off to a subsidiary position where insertion continues. Here this is strict
scansion: the Vocabulary is scanned once, top to bottom, and an item is inserted when one of the
node's matrices bears every feature of its site, discharging one occurrence of each; scansion halts
at the bottom of the list, so no item is inserted twice.

An item's site is a set of features, as applicability and specificity already treat it, while a
matrix is a multiset, so that a feature borne twice is two repetitions in Marcolli, Chomsky and
Berwick's sense and two items may discharge it one at a time. Lists represent both for
computation, and the theorems are stated in the free commutative monoid `Multiset F`, where
discharge is truncated subtraction and scansion a greedy decomposition of the node. A node may
bear several matrices, one per argument it agrees with, as the Yucatec Agr3 agrees with both
subject and object, and an item draws on one of them.

## Main definitions

* `discharge`: remove one occurrence of each feature of an item's site from the first matrix
  bearing them all.
* `scan`, `insertions`, `residue`, `scansion`: the items a node's matrices receive under strict
  scansion with local Fission, the matrices left over, and the items' exponents.

## Main results

* `sum_insertions_add_residue`: in the free commutative monoid on the features, the inserted
  items' sites and the residue sum to the node.
* `countP_insertions_le`, `pairwise_disjoint_insertions`: a feature is exponed at most as often as
  the node bears it, and on a node without repetitions the inserted items' sites are disjoint.
* `head?_scansion_singleton`: on a Vocabulary ordered by specificity, the first insertion at a
  single matrix is the Subset Principle's winner.

## References

* [R. Noyer, *Features, positions and affixes in autonomous morphological
  structure*][noyer-1992]
* [M. Halle, *Distributed Morphology: Impoverishment and Fission*][halle-1997]
* [A. González Poot and M. McGinnis, *Local versus long-distance Fission in
  Distributed Morphology*][gonzalez-poot-mcginnis-2006]
* [M. Marcolli, N. Chomsky and R. C. Berwick, *Mathematical Structure of Syntactic
  Merge*][marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace DistributedMorphology

open Morphology.Exponence

variable {F E : Type*} [DecidableEq F]

/-- Discharging an item removes one occurrence of each feature of its site from the first of the
matrices bearing them all, in the environment `env` (whose focus is ignored), and fails when no
matrix does. -/
def discharge (i : VocabularyItem F E) (env : Neighborhood (List F)) :
    List (List F) → Option (List (List F))
  | [] => none
  | m :: ms =>
    if i.site ⊆ ({ env with focus := m } : Neighborhood (List F)) then
      some (m.diff i.site.focus.dedup :: ms)
    else (discharge i env ms).map (m :: ·)

/-- Strict scansion with local Fission at a node bearing the matrices `ms` in the environment
`env` yields the items inserted, in Vocabulary order, and the matrices left over. -/
def scan : List (VocabularyItem F E) → Neighborhood (List F) → List (List F) →
    List (VocabularyItem F E) × List (List F)
  | [], _, ms => ([], ms)
  | i :: rest, env, ms =>
    match discharge i env ms with
    | some ms' => ((i :: (scan rest env ms').1), (scan rest env ms').2)
    | none => scan rest env ms

/-- `insertions` lists the items scansion inserts. -/
def insertions (items : List (VocabularyItem F E)) (env : Neighborhood (List F))
    (ms : List (List F)) : List (VocabularyItem F E) :=
  (scan items env ms).1

/-- `residue` lists the matrices scansion leaves, the features no inserted item discharged. -/
def residue (items : List (VocabularyItem F E)) (env : Neighborhood (List F))
    (ms : List (List F)) : List (List F) :=
  (scan items env ms).2

/-- A node bearing the matrices `ms` in the environment `env` receives these exponents. -/
def scansion (items : List (VocabularyItem F E)) (env : Neighborhood (List F))
    (ms : List (List F)) : List E :=
  (insertions items env ms).map (·.exponent)

variable {items rest : List (VocabularyItem F E)} {env : Neighborhood (List F)}
  {i : VocabularyItem F E} {ms ms' : List (List F)}

@[simp] theorem discharge_nil (i : VocabularyItem F E) : discharge i env [] = none := rfl

@[simp] theorem scan_nil (env : Neighborhood (List F)) (ms : List (List F)) :
    scan ([] : List (VocabularyItem F E)) env ms = ([], ms) := rfl

theorem scan_cons_of_discharge_eq_some (h : discharge i env ms = some ms') :
    scan (i :: rest) env ms =
      (i :: insertions rest env ms', residue rest env ms') := by
  simp [scan, h, insertions, residue]

theorem scan_cons_of_discharge_eq_none (h : discharge i env ms = none) :
    scan (i :: rest) env ms = scan rest env ms := by
  simp [scan, h]

/-- Discharge subtracts the item's site, a set of features, from the node's multiset. -/
theorem val_add_discharge : ∀ {ms ms' : List (List F)}, discharge i env ms = some ms' →
    i.site.focus.toFinset.val + ms'.flatten = (ms.flatten : Multiset F)
  | [], _, h => by simp at h
  | m :: ms, ms', h => by
    unfold discharge at h
    split_ifs at h with hs
    · cases h
      have hle : i.site.focus.toFinset.val ≤ (m : Multiset F) :=
        (Multiset.le_iff_subset i.site.focus.toFinset.nodup).mpr fun f hf ↦
          Multiset.mem_coe.mpr (Neighborhood.focus_subset_focus hs (List.mem_toFinset.mp hf))
      rw [List.flatten_cons, List.flatten_cons, ← Multiset.coe_add, ← Multiset.coe_add,
        ← Multiset.coe_sub, ← List.toFinset_val, ← Multiset.add_assoc,
        Multiset.add_comm i.site.focus.toFinset.val, Multiset.sub_add_cancel hle]
    · obtain ⟨ms'', h'', rfl⟩ := Option.map_eq_some_iff.mp h
      rw [List.flatten_cons, List.flatten_cons, ← Multiset.coe_add, ← Multiset.coe_add,
        ← Multiset.add_assoc, Multiset.add_comm i.site.focus.toFinset.val, Multiset.add_assoc,
        val_add_discharge h'']

/-- **Conservation.** In the free commutative monoid on the features, the inserted items' sites
and the residue sum to the node. -/
theorem sum_insertions_add_residue : ∀ (items : List (VocabularyItem F E)) (ms : List (List F)),
    ((insertions items env ms).map (·.site.focus.toFinset.val)).sum + (residue items env ms).flatten
      = (ms.flatten : Multiset F)
  | [], _ => by simp [insertions, residue]
  | i :: rest, ms => by
    cases h : discharge i env ms with
    | none =>
      simpa [insertions, residue, scan_cons_of_discharge_eq_none h] using
        sum_insertions_add_residue rest ms
    | some ms' =>
      rw [insertions, residue, scan_cons_of_discharge_eq_some h]
      dsimp only
      rw [List.map_cons, List.sum_cons, Multiset.add_assoc, sum_insertions_add_residue rest ms',
        val_add_discharge h]

/-- A node with no matrix receives nothing. -/
@[simp] theorem insertions_nil_right :
    ∀ items : List (VocabularyItem F E), insertions items env [] = []
  | [] => rfl
  | i :: rest => by
    rw [insertions, scan_cons_of_discharge_eq_none (discharge_nil i)]
    exact insertions_nil_right rest

@[simp] theorem scansion_nil : scansion items env [] = [] := by simp [scansion]

/-- Each item is inserted at most once, in Vocabulary order. -/
theorem insertions_sublist : ∀ (items : List (VocabularyItem F E)) (ms : List (List F)),
    (insertions items env ms).Sublist items
  | [], _ => .slnil
  | i :: rest, ms => by
    cases h : discharge i env ms with
    | none =>
      rw [insertions, scan_cons_of_discharge_eq_none h]
      exact (insertions_sublist rest ms).cons _
    | some ms' =>
      rw [insertions, scan_cons_of_discharge_eq_some h]
      exact (insertions_sublist rest ms').cons_cons _

theorem scansion_sublist (ms : List (List F)) :
    (scansion items env ms).Sublist (items.map (·.exponent)) :=
  (insertions_sublist items ms).map _

theorem length_scansion_le (ms : List (List F)) :
    (scansion items env ms).length ≤ items.length := by
  simpa using (scansion_sublist (items := items) (env := env) ms).length_le

private theorem count_sum_val (f : F) (l : List (VocabularyItem F E)) :
    ((l.map fun i : VocabularyItem F E ↦ i.site.focus.toFinset.val).sum).count f =
      l.countP (f ∈ ·.site.focus) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.sum_cons, Multiset.count_add, ih,
      Multiset.count_eq_of_nodup i.site.focus.toFinset.nodup, List.countP_cons]
    simp [Nat.add_comm]

/-- **No multiple exponence.** The inserted items realizing a feature number at most the node's
occurrences of it. -/
theorem countP_insertions_le (f : F) (items : List (VocabularyItem F E)) (ms : List (List F)) :
    (insertions items env ms).countP (f ∈ ·.site.focus) ≤ ms.flatten.count f := by
  rw [← count_sum_val, ← Multiset.coe_count, ← sum_insertions_add_residue items ms]
  exact Multiset.count_le_of_le f (Multiset.le_add_right _ _)

private theorem pairwise_disjoint_of_countP_le_one : ∀ {l : List (VocabularyItem F E)},
    (∀ f, l.countP (f ∈ ·.site.focus) ≤ 1) →
      l.Pairwise fun i j ↦ i.site.focus.Disjoint j.site.focus
  | [], _ => .nil
  | i :: l, h => by
    refine .cons (fun j hj f hi hj' ↦ ?_)
      (pairwise_disjoint_of_countP_le_one fun f ↦ (List.countP_cons ▸ h f).trans' (by simp))
    have : 0 < l.countP (f ∈ ·.site.focus) := List.countP_pos_iff.mpr ⟨j, hj, by simpa using hj'⟩
    have := h f
    simp only [List.countP_cons, hi, decide_true, ite_true] at this
    omega

/-- On a node without repetitions the inserted items' sites are disjoint, so the items partition
the features they discharge. -/
theorem pairwise_disjoint_insertions (h : ms.flatten.Nodup) :
    (insertions items env ms).Pairwise fun i j ↦ i.site.focus.Disjoint j.site.focus :=
  pairwise_disjoint_of_countP_le_one fun f ↦
    (countP_insertions_le f items ms).trans (List.nodup_iff_count_le_one.mp h f)

/-- At a single matrix, an item discharges iff it applies there. -/
theorem discharge_singleton (i : VocabularyItem F E) (m : List F) :
    discharge i env [m] =
      if i.site ⊆ ({ env with focus := m } : Neighborhood (List F))
        then some [m.diff i.site.focus.dedup] else none := by
  simp [discharge]

/-- On a Vocabulary ordered by decreasing specificity, the first insertion at
a single matrix is the Subset Principle's winner: scansion agrees with
Elsewhere competition where both apply. -/
theorem head?_scansion_singleton (m : List F)
    (hsorted : items.Pairwise fun i j => j.specificity ≤ i.specificity) :
    (scansion items env [m]).head? =
      (winner? items ({ env with focus := m } : Neighborhood (List F))).map (·.exponent) := by
  induction items with
  | nil => simp [scansion, insertions, winner?, selectBy, applicable]
  | cons i rest ih =>
    rw [List.pairwise_cons] at hsorted
    simp only [scansion, insertions, scan, discharge_singleton]
    by_cases h : i.site ⊆ ({ env with focus := m } : Neighborhood (List F))
    · rw [ite_eq_left h]
      simp only [winner?, selectBy, applicable, List.filter_cons,
        decide_eq_true (show Applies i _ from h), ite_true]
      rw [List.argmax_cons]
      rcases hc : List.argmax VocabularyItem.specificity
        (rest.filter fun r =>
          decide (Applies r ({ env with focus := m } : Neighborhood (List F)))) with _ | c
      · rfl
      · have hle : c.specificity ≤ i.specificity :=
          hsorted.1 c (List.mem_of_mem_filter (List.argmax_mem hc))
        simp [not_lt.mpr hle]
    · rw [ite_eq_right h]
      have := ih hsorted.2
      simpa [scansion, insertions, winner?, selectBy, applicable, List.filter_cons,
        decide_eq_false (show ¬ Applies i _ from h)] using this

end DistributedMorphology
