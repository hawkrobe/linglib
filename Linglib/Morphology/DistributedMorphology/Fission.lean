import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic

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
* `scansion`: the exponents a node's matrices receive under strict
  scansion with local Fission.

## Main results

* `scansion_sublist`: the exponents are a subsequence of the Vocabulary's
  — each item at most once, in list order.
* `scansion_nil`: a node with no matrix receives nothing.
* `head?_scansion_singleton`: on a Vocabulary ordered by specificity, the
  first insertion at a single matrix is the Subset Principle's winner.

## References

* [R. Noyer, *Features, positions and affixes in autonomous morphological
  structure*][noyer-1992]
* [M. Halle, *Distributed Morphology: Impoverishment and Fission*][halle-1997]
* [A. González Poot and M. McGinnis, *Local versus long-distance Fission in
  Distributed Morphology*][gonzalez-poot-mcginnis-2006]
-/

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

/-- Strict scansion with local Fission: the exponents received by a node
bearing the matrices `ms` in the environment `env`. -/
def scansion (items : List (VocabularyItem F E)) (env : Neighborhood (List F)) :
    List (List F) → List E
  | ms => go items ms
where
  /-- Scan the remaining items against the remaining matrices. -/
  go : List (VocabularyItem F E) → List (List F) → List E
    | [], _ => []
    | i :: rest, ms =>
      match discharge i env ms with
      | some ms' => i.exponent :: go rest ms'
      | none => go rest ms

variable {items : List (VocabularyItem F E)} {env : Neighborhood (List F)}

@[simp] theorem discharge_nil (i : VocabularyItem F E) : discharge i env [] = none := rfl

theorem scansion_go_nil : ∀ items : List (VocabularyItem F E), scansion.go env items [] = []
  | [] => rfl
  | _ :: rest => by simp [scansion.go, scansion_go_nil rest]

/-- A node with no matrix receives nothing. -/
@[simp] theorem scansion_nil : scansion items env [] = [] := scansion_go_nil items

/-- Each item is inserted at most once, in Vocabulary order. -/
theorem scansion_go_sublist :
    ∀ (items : List (VocabularyItem F E)) (ms : List (List F)),
      (scansion.go env items ms).Sublist (items.map (·.exponent))
  | [], _ => List.Sublist.refl _
  | i :: rest, ms => by
    simp only [scansion.go, List.map_cons]
    split
    · exact (scansion_go_sublist rest _).cons_cons _
    · exact (scansion_go_sublist rest ms).cons _

theorem scansion_sublist (ms : List (List F)) :
    (scansion items env ms).Sublist (items.map (·.exponent)) :=
  scansion_go_sublist items ms

theorem length_scansion_le (ms : List (List F)) :
    (scansion items env ms).length ≤ items.length := by
  simpa using (scansion_sublist (items := items) (env := env) ms).length_le

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
  | nil => simp [scansion, scansion.go, winner?, selectBy, applicable]
  | cons i rest ih =>
    rw [List.pairwise_cons] at hsorted
    simp only [scansion, scansion.go, discharge_singleton]
    by_cases h : i.site ⊆ ({ env with focus := m } : Neighborhood (List F))
    · rw [if_pos h]
      simp only [List.head?_cons, winner?, selectBy, applicable, List.filter_cons,
        decide_eq_true (show Applies i _ from h), if_true]
      rw [List.argmax_cons]
      rcases hc : List.argmax VocabularyItem.specificity
        (rest.filter fun r =>
          decide (Applies r ({ env with focus := m } : Neighborhood (List F)))) with _ | c
      · rfl
      · have hle : c.specificity ≤ i.specificity :=
          hsorted.1 c (List.mem_of_mem_filter (List.argmax_mem hc))
        simp [not_lt.mpr hle]
    · rw [if_neg h]
      have := ih hsorted.2
      simpa [scansion, winner?, selectBy, applicable, List.filter_cons,
        decide_eq_false (show ¬ Applies i _ from h)] using this

end DistributedMorphology
