module

public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Perm.Subperm

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
Berwick's sense and two items may discharge it one at a time. Scansion is then a greedy decomposition in the free
commutative monoid on the features. A node may bear several matrices, one per argument it agrees
with, as the Yucatec Agr3 agrees with both subject and object, and an item draws on one of them.

## Main definitions

* `discharge`: remove one occurrence of each feature of an item's site from the first matrix
  bearing them all.
* `scan`, `insertions`, `residue`, `scansion`: the items a node's matrices receive under strict
  scansion with local Fission, the matrices left over, and the items' exponents.

## Main results

* `perm_insertions_residue`: the inserted items' features and the residue make up the node.
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
open scoped List

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

/-- Discharge draws one occurrence of each feature of the item's site from the node. -/
theorem perm_discharge : ∀ {ms ms' : List (List F)}, discharge i env ms = some ms' →
    i.site.focus.dedup ++ ms'.flatten ~ ms.flatten
  | [], _, h => by simp at h
  | m :: ms, ms', h => by
    unfold discharge at h
    split_ifs at h with hs
    · cases h
      have hm : i.site.focus.dedup <+~ m := (List.nodup_dedup _).subperm fun _ hf ↦
        Neighborhood.focus_subset_focus hs (List.mem_dedup.mp hf)
      rw [List.flatten_cons, List.flatten_cons, ← List.append_assoc]
      exact (List.subperm_append_diff_self_of_count_le fun x _ ↦ hm.count_le x).append_right _
    · obtain ⟨ms'', h'', rfl⟩ := Option.map_eq_some_iff.mp h
      rw [List.flatten_cons, List.flatten_cons]
      exact (List.perm_append_comm_assoc _ _ _).trans ((perm_discharge h'').append_left m)

/-- **Conservation.** The inserted items' features, one occurrence of each feature of a site, and
the residue are a permutation of the node's features. -/
theorem perm_insertions_residue : ∀ (items : List (VocabularyItem F E)) (ms : List (List F)),
    (insertions items env ms).flatMap (·.site.focus.dedup) ++ (residue items env ms).flatten ~
      ms.flatten
  | [], _ => .rfl
  | i :: rest, ms => by
    cases h : discharge i env ms with
    | none =>
      simpa [insertions, residue, scan_cons_of_discharge_eq_none h] using
        perm_insertions_residue rest ms
    | some ms' =>
      simp only [insertions, residue, scan_cons_of_discharge_eq_some h, List.flatMap_cons,
        List.append_assoc]
      exact ((perm_insertions_residue rest ms').append_left _).trans (perm_discharge h)

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

private theorem count_flatMap_dedup (f : F) (l : List (VocabularyItem F E)) :
    (l.flatMap (·.site.focus.dedup)).count f = l.countP (f ∈ ·.site.focus) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.flatMap_cons, List.count_append, List.count_dedup, ih,
      List.countP_cons, decide_eq_true_eq, Nat.add_comm]

/-- **No multiple exponence.** The inserted items realizing a feature number at most the node's
occurrences of it. -/
theorem countP_insertions_le (f : F) (items : List (VocabularyItem F E)) (ms : List (List F)) :
    (insertions items env ms).countP (f ∈ ·.site.focus) ≤ ms.flatten.count f := by
  rw [← count_flatMap_dedup, ← ((perm_insertions_residue items ms).count_eq f), List.count_append]
  exact Nat.le_add_right _ _

/-- On a node without repetitions the inserted items' sites are disjoint, so the items partition
the features they discharge. -/
theorem pairwise_disjoint_insertions (h : ms.flatten.Nodup) :
    (insertions items env ms).Pairwise fun i j ↦ i.site.focus.Disjoint j.site.focus :=
  (List.nodup_flatMap.mp ((perm_insertions_residue (env := env) items ms).nodup_iff.mpr
    h).of_append_left).2.imp fun hd _ ha hb ↦ hd (List.mem_dedup.mpr ha) (List.mem_dedup.mpr hb)

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
