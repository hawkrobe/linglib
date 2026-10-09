module

public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Mathlib.Data.List.Count

/-!
# Fission

Fission lets one syntactic node be realized in several adjacent positions
of exponence: a Vocabulary Item inserted at the node discharges only the
features it spells out, and the remaining features fission off to a
subsidiary position where insertion continues. The procedure here is strict
scansion: the Vocabulary is scanned once, top to bottom; an item whose site
one of the node's feature matrices contains is inserted and its features are
discharged from that matrix; the residue stays available to the items
below, and scansion halts at the bottom of the list — so no item is
inserted twice, with no stipulation about elsewhere items.

A node may bear several matrices, one per argument it agrees with (the
Yucatec Agr3 agrees with both the ergative subject and the nominative
object), and the matrices are kept apart: an item's features must all come
from one of them. Features carry multiplicity (`List.diff`), so two
arguments' shared features are discharged one at a time.

## Main definitions

* `discharge`: remove an item's features from the first matrix containing
  its site.
* `insertions`, `scansion`: the items a node's matrices receive under strict
  scansion with local Fission, and their exponents.

## Main results

* `insertions_sublist`: the items are a subsequence of the Vocabulary — each
  at most once, in list order.
* `countP_insertions_le`: a feature is discharged at most as often as the
  node bears it, so Fission never expones one feature twice.
* `head?_scansion_singleton`: on a Vocabulary ordered by specificity, the
  first insertion at a single matrix is the Subset Principle's winner.

## References

* [R. Noyer, *Features, positions and affixes in autonomous morphological
  structure*][noyer-1992]
* [M. Halle, *Distributed Morphology: Impoverishment and Fission*][halle-1997]
* [A. González Poot and M. McGinnis, *Local versus long-distance Fission in
  Distributed Morphology*][gonzalez-poot-mcginnis-2006]
-/

@[expose] public section

namespace DistributedMorphology

open Morphology.Exponence

variable {F E : Type*} [DecidableEq F]

/-- Discharge the item's features from the first of the matrices containing
its site, in the environment `env` (whose focus is ignored); `none` when no
matrix does. -/
def discharge (i : VocabularyItem F E) (env : Neighborhood (List F)) :
    List (List F) → Option (List (List F))
  | [] => none
  | m :: ms =>
    if i.site ⊆ ({ env with focus := m } : Neighborhood (List F)) then
      some (m.diff i.site.focus :: ms)
    else (discharge i env ms).map (m :: ·)

/-- Strict scansion with local Fission inserts these items, in Vocabulary order,
at a node bearing the matrices `ms` in the environment `env`. -/
def insertions : List (VocabularyItem F E) → Neighborhood (List F) → List (List F) →
    List (VocabularyItem F E)
  | [], _, _ => []
  | i :: rest, env, ms =>
    match discharge i env ms with
    | some ms' => i :: insertions rest env ms'
    | none => insertions rest env ms

/-- A node bearing the matrices `ms` in the environment `env` receives these
exponents. -/
def scansion (items : List (VocabularyItem F E)) (env : Neighborhood (List F))
    (ms : List (List F)) : List E :=
  (insertions items env ms).map (·.exponent)

variable {items : List (VocabularyItem F E)} {env : Neighborhood (List F)}

@[simp] theorem discharge_nil (i : VocabularyItem F E) : discharge i env [] = none := rfl

/-- A node with no matrix receives nothing. -/
@[simp] theorem insertions_nil_right :
    ∀ items : List (VocabularyItem F E), insertions items env [] = []
  | [] => rfl
  | _ :: rest => by simp [insertions, insertions_nil_right rest]

@[simp] theorem scansion_nil : scansion items env [] = [] := by simp [scansion]

/-- Each item is inserted at most once, in Vocabulary order. -/
theorem insertions_sublist :
    ∀ (items : List (VocabularyItem F E)) (ms : List (List F)),
      (insertions items env ms).Sublist items
  | [], _ => .slnil
  | i :: rest, ms => by
    simp only [insertions]
    split
    · exact (insertions_sublist rest _).cons_cons _
    · exact (insertions_sublist rest ms).cons _

theorem scansion_sublist (ms : List (List F)) :
    (scansion items env ms).Sublist (items.map (·.exponent)) :=
  (insertions_sublist items ms).map _

theorem length_scansion_le (ms : List (List F)) :
    (scansion items env ms).length ≤ items.length := by
  simpa using (scansion_sublist (items := items) (env := env) ms).length_le

/-- Discharge removes one occurrence of each feature of the item's focus from
the matrix it draws on. -/
theorem sum_count_discharge_add_le {i : VocabularyItem F E} (f : F) :
    ∀ {ms ms' : List (List F)}, discharge i env ms = some ms' →
      (ms'.map (·.count f)).sum + (if f ∈ i.site.focus then 1 else 0) ≤
        (ms.map (·.count f)).sum
  | [], _, h => by simp at h
  | m :: ms, ms', h => by
    unfold discharge at h
    split_ifs at h with hs
    · cases h
      have hm : i.site.focus ⊆ m := Neighborhood.focus_subset_focus hs
      simp only [List.map_cons, List.sum_cons, List.count_diff]
      split_ifs with hf
      · have := List.count_pos_iff.mpr (hm hf)
        have := List.count_pos_iff.mpr hf
        omega
      · omega
    · obtain ⟨ms'', h'', rfl⟩ := Option.map_eq_some_iff.mp h
      have := sum_count_discharge_add_le f h''
      simp only [List.map_cons, List.sum_cons]
      omega

/-- **No multiple exponence.** The inserted items realizing a feature number at
most the node's occurrences of it, since each discharges one. -/
theorem countP_insertions_le (f : F) :
    ∀ (items : List (VocabularyItem F E)) (ms : List (List F)),
      (insertions items env ms).countP (f ∈ ·.site.focus) ≤ (ms.map (·.count f)).sum
  | [], _ => by simp [insertions]
  | i :: rest, ms => by
    simp only [insertions]
    split
    · next ms' h =>
      have := sum_count_discharge_add_le f h
      have := countP_insertions_le f rest ms'
      rw [List.countP_cons]
      split_ifs at * <;> simp_all <;> omega
    · exact countP_insertions_le f rest ms

/-- At a single matrix, an item discharges iff it applies there. -/
theorem discharge_singleton (i : VocabularyItem F E) (m : List F) :
    discharge i env [m] =
      if i.site ⊆ ({ env with focus := m } : Neighborhood (List F))
        then some [m.diff i.site.focus] else none := by
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
    simp only [scansion, insertions, discharge_singleton]
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
      simpa [scansion, winner?, selectBy, applicable, List.filter_cons,
        decide_eq_false (show ¬ Applies i _ from h)] using this

end DistributedMorphology
