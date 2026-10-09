module

public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Mathlib.Data.Finset.Disjoint
public import Mathlib.Data.Multiset.Bind

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

* `bind_insertions_add_residue`: in the free commutative monoid on the features, the inserted
  items' sites and the residue sum to the node.
* `bind_insertions_le`, `pairwise_disjoint_insertions`: the inserted items' sites fit inside the
  node, and on a node without repetitions they are disjoint.
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
    | some ms' => (scan rest env ms').map (i :: ·) id
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
    scan (i :: rest) env ms = (i :: insertions rest env ms', residue rest env ms') := by
  simp only [scan, h]; rfl

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
      have hle : i.site.focus.toFinset.val ≤ (m : Multiset F) := Finset.val_le_iff_val_subset.mpr
        fun f hf ↦ by simpa using Neighborhood.focus_subset_focus hs (by simpa using hf)
      rw [List.flatten_cons, List.flatten_cons, ← Multiset.coe_add, ← Multiset.coe_add,
        ← Multiset.coe_sub, ← List.toFinset_val, ← Multiset.add_assoc,
        Multiset.add_comm i.site.focus.toFinset.val, Multiset.sub_add_cancel hle]
    · obtain ⟨ms'', h'', rfl⟩ := Option.map_eq_some_iff.mp h
      rw [List.flatten_cons, List.flatten_cons, ← Multiset.coe_add, ← Multiset.coe_add,
        ← Multiset.add_assoc, Multiset.add_comm i.site.focus.toFinset.val, Multiset.add_assoc,
        val_add_discharge h'']

/-- **Conservation.** In the free commutative monoid on the features, the inserted items' sites
and the residue sum to the node. -/
theorem bind_insertions_add_residue : ∀ (items : List (VocabularyItem F E)) (ms : List (List F)),
    (insertions items env ms : Multiset (VocabularyItem F E)).bind (·.site.focus.toFinset.val) +
      ((residue items env ms).flatten : Multiset F) = ms.flatten
  | [], _ => by simp [insertions, residue]
  | i :: rest, ms => by
    cases h : discharge i env ms with
    | none =>
      simpa [insertions, residue, scan_cons_of_discharge_eq_none h] using
        bind_insertions_add_residue rest ms
    | some ms' =>
      rw [insertions, residue, scan_cons_of_discharge_eq_some h]
      dsimp only
      rw [← Multiset.cons_coe, Multiset.cons_bind, Multiset.add_assoc,
        bind_insertions_add_residue rest ms', val_add_discharge h]

/-- **No multiple exponence.** The inserted items' sites fit inside the node, so no feature is
discharged more often than the node bears it. -/
theorem bind_insertions_le (items : List (VocabularyItem F E)) (ms : List (List F)) :
    (insertions items env ms : Multiset (VocabularyItem F E)).bind (·.site.focus.toFinset.val) ≤
      (ms.flatten : Multiset F) :=
  bind_insertions_add_residue items ms ▸ Multiset.le_add_right _ _

/-- On a node without repetitions the inserted items' sites are disjoint, so the items partition
the features they discharge. -/
theorem pairwise_disjoint_insertions (h : ms.flatten.Nodup) :
    (insertions items env ms).Pairwise fun i j ↦ i.site.focus.Disjoint j.site.focus := by
  have := Multiset.nodup_of_le (bind_insertions_le (env := env) items ms) (Multiset.coe_nodup.mpr h)
  rw [Multiset.nodup_bind, Multiset.pairwise_coe_iff_pairwise] at this
  exact this.2.imp (List.disjoint_toFinset_iff_disjoint.mp <| Finset.disjoint_val.mp ·)

/-- A node with no matrix receives nothing. -/
@[simp] theorem insertions_nil_right :
    ∀ items : List (VocabularyItem F E), insertions items env [] = []
  | [] => rfl
  | _ :: rest => insertions_nil_right rest

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
