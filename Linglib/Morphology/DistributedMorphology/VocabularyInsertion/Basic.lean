import Mathlib.Data.Finset.Card
import Linglib.Morphology.DistributedMorphology.Basic
import Linglib.Morphology.Exponence.Select
import Linglib.Morphology.Realization

/-!
# Vocabulary insertion

Vocabulary Insertion is the operation that supplies syntactic terminals with
phonological exponents in Distributed Morphology: the Vocabulary Items of
List 2 compete for insertion at each terminal, and the Subset Principle of
[halle-marantz-1993] picks the item whose feature specification is the
largest subset of the terminal's bundle. This file specializes the shared
exponence engine (`Morphology.Exponence.selectBy`) to that competition.

## Main definitions

* `VocabularyItem F E`: a feature specification with an exponent, applicable
  at a bundle containing every specified feature.
* `VocabularyItem.specificity`: the number of distinct specified features.
* `winner?`, `subsetPrinciple`: the Subset Principle's winning item and its
  exponent.
* `vocabularyInsert`: selection over `VocabItem`s, whose applicability is an
  opaque predicate and whose rank is stipulated.

## Main results

* `VocabularyItem.le_iff`: the engine's specificity order on vocabulary items
  is reverse feature inclusion, so `specificity` is strictly antitone and
  `winner?_isElsewhereWinner` needs no faithfulness hypothesis.
* `winner?_retreat`: deleting features from the target can only make the
  winner less specific — retreat to the general case.
* `vocabularyInsert_isElsewhereWinner`: under `SpecificityFaithful`, the
  opaque engine also selects an Elsewhere winner.

## Implementation notes

A `VocabItem` carries an arbitrary decidable context predicate, an optional
root restriction (the root-conditioned allomorphy that [bobaljik-2000]'s
root-out insertion makes available inward), and a stipulated rank; with
opaque predicates the derived specificity order is not computable, so
`SpecificityFaithful` is the obligation the stipulation incurs. Over
`VocabularyItem`s no such obligation arises.

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
* [J. D. Bobaljik, *The ins and outs of contextual allomorphy*][bobaljik-2000]
-/

namespace DistributedMorphology

open Morphology.Exponence

/-! ### Vocabulary items -/

/-- A Vocabulary Item: a feature specification paired with an exponent,
applicable at any bundle containing every specified feature. -/
structure VocabularyItem (F E : Type*) where
  /-- The features the item spells out. -/
  features : List F
  /-- The exponent the item inserts. -/
  exponent : E
  deriving DecidableEq, Repr

namespace VocabularyItem

variable {F E : Type*} [DecidableEq F] {i j : VocabularyItem F E} {t : List F}

instance : Rule (VocabularyItem F E) (List F) E := ⟨exponent, fun i t => i.features ⊆ t⟩

instance : DecidableRel (Applies : VocabularyItem F E → List F → Prop) :=
  fun i t => decidable_of_iff (∀ f ∈ i.features, f ∈ t) Iff.rfl

instance : Preorder (VocabularyItem F E) := toPreorder

theorem applies_iff : Applies i t ↔ i.features ⊆ t := Iff.rfl

/-- An item with no features applies at every bundle. -/
theorem elsewhere_applies (e : E) (t : List F) : Applies (⟨[], e⟩ : VocabularyItem F E) t :=
  List.nil_subset _

theorem le_iff_applies : i ≤ j ↔ ∀ ⦃t : List F⦄, i.features ⊆ t → j.features ⊆ t := Iff.rfl

/-- The engine's specificity order is reverse feature inclusion. -/
theorem le_iff : i ≤ j ↔ j.features ⊆ i.features :=
  ⟨fun h => le_iff_applies.mp h (List.Subset.refl _),
    fun h => le_iff_applies.mpr fun _ ht => List.Subset.trans h ht⟩

/-- The number of distinct features an item specifies — the Subset
Principle's specificity score. -/
def specificity (i : VocabularyItem F E) : ℕ := i.features.toFinset.card

theorem toFinset_subset_toFinset :
    i.features.toFinset ⊆ j.features.toFinset ↔ i.features ⊆ j.features :=
  Multiset.toFinset_subset.trans Multiset.coe_subset

theorem specificity_strictAnti : StrictAnti (specificity : VocabularyItem F E → ℕ) :=
  fun _ _ h => Finset.card_lt_card <| Finset.ssubset_def.mpr
    ⟨toFinset_subset_toFinset.mpr (le_iff.mp h.le),
      fun hc => (lt_iff_le_not_ge.mp h).2 (le_iff.mpr (toFinset_subset_toFinset.mp hc))⟩

end VocabularyItem

/-! ### The Subset Principle -/

section SubsetPrinciple

variable {F E : Type*} [DecidableEq F] {items : List (VocabularyItem F E)} {t t' : List F}
  {i i' : VocabularyItem F E} {e : E}

/-- The Subset Principle's winning item: the applicable item of greatest
`specificity` (the earliest, under ties). -/
def winner? (items : List (VocabularyItem F E)) (t : List F) : Option (VocabularyItem F E) :=
  selectBy VocabularyItem.specificity items t

/-- The **Subset Principle** ([halle-marantz-1993]): the exponent of the most
specific item whose features the target bears; `none` iff no item applies. -/
def subsetPrinciple (items : List (VocabularyItem F E)) (t : List F) : Option E :=
  realize VocabularyItem.specificity items t

theorem winner?_mem (h : winner? items t = some i) : i ∈ applicable items t :=
  List.argmax_mem h

theorem winner?_spec (h : winner? items t = some i) : i ∈ items ∧ i.features ⊆ t :=
  mem_applicable.mp (winner?_mem h)

/-- The Subset Principle's exponent comes from an applicable item — the
selection never draws on features the node does not bear. -/
theorem subsetPrinciple_winner_mem (h : subsetPrinciple items t = some e) :
    ∃ i ∈ items, i.exponent = e ∧ i.features ⊆ t := by
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨i, (winner?_spec hi).1, rfl, (winner?_spec hi).2⟩

theorem winner?_isSome_iff : (winner? items t).isSome ↔ applicable items t ≠ [] := by
  rw [Option.isSome_iff_ne_none]; exact not_congr selectBy_eq_none_iff

theorem winner?_max (h : winner? items t = some i) :
    ∀ j ∈ applicable items t, j.specificity ≤ i.specificity :=
  fun _ hj => List.le_of_mem_argmax hj h

/-- The winner is an Elsewhere winner of the shared core — with no
faithfulness hypothesis, since `VocabularyItem.specificity` is strictly
antitone outright. -/
theorem winner?_isElsewhereWinner (h : winner? items t = some i) : IsElsewhereWinner items t i :=
  selectBy_isElsewhereWinner (VocabularyItem.specificity_strictAnti.strictAntiOn _) h

theorem subsetPrinciple_realizes (h : subsetPrinciple items t = some e) : Realizes items t e :=
  realize_realizes (VocabularyItem.specificity_strictAnti.strictAntiOn _) h

/-- Applicability is monotone in the target bundle. -/
theorem applicable_mono (hsub : t' ⊆ t) : applicable items t' ⊆ applicable items t :=
  fun _ hi => mem_applicable.mpr
    ⟨(mem_applicable.mp hi).1, List.Subset.trans (mem_applicable.mp hi).2 hsub⟩

/-- **Retreat to the general case**: shrinking the target — deleting features
by Impoverishment — can only make the winner weakly less specific, which is
why impoverishment yields syncretism with a more general exponent rather than
a different specific one ([halle-marantz-1993], [arregi-nevins-2012]). -/
theorem winner?_retreat (hsub : t' ⊆ t) (h' : winner? items t' = some i') :
    ∃ i, winner? items t = some i ∧ i'.specificity ≤ i.specificity := by
  have hmem := applicable_mono hsub (winner?_mem h')
  obtain ⟨i, hi⟩ :=
    Option.isSome_iff_exists.mp (winner?_isSome_iff.mpr (List.ne_nil_of_mem hmem))
  exact ⟨i, hi, winner?_max hi _ hmem⟩

end SubsetPrinciple

/-! ### Opaque-context items -/

section VocabItem

variable {Ctx Root : Type*} {rules : List (VocabItem Ctx Root)} {ctx : Ctx} {root : Root}
  {e : String}

/-- Insert a Vocabulary Item at a terminal node: the exponent of the
highest-`specificity` matching rule (ties go to the earlier rule), `none` if
no rule matches — the **Elsewhere Condition** of [halle-marantz-1993]. -/
def vocabularyInsert (rules : List (VocabItem Ctx Root)) (ctx : Ctx) (root : Root) :
    Option String :=
  realize VocabItem.specificity rules (ctx, root)

/-- Insertion over rules with no root restriction. -/
def vocabularyInsertSimple (rules : List (VocabItem Ctx Unit)) (ctx : Ctx) : Option String :=
  vocabularyInsert rules ctx ()

/-- The stipulated `specificity` rank is **faithful** when it refines the
engine's specificity order: a strictly more specific item always outranks. -/
def SpecificityFaithful (rules : List (VocabItem Ctx Root)) : Prop :=
  ∀ a ∈ rules, ∀ b ∈ rules, a ≤ b → ¬ b ≤ a → b.specificity < a.specificity

/-- Under a faithful rank, `vocabularyInsert` selects an Elsewhere winner. -/
theorem vocabularyInsert_isElsewhereWinner (h : vocabularyInsert rules ctx root = some e)
    (hf : SpecificityFaithful rules) :
    ∃ vi ∈ rules, vi.exponent = e ∧ IsElsewhereWinner rules (ctx, root) vi := by
  obtain ⟨vi, hvi, hve⟩ := Option.map_eq_some_iff.mp h
  exact ⟨vi, selectBy_mem hvi, hve, selectBy_isElsewhereWinner
    (λ a ha b hb hab => hf a (mem_applicable.mp ha).1 b (mem_applicable.mp hb).1
      (lt_iff_le_not_ge.mp hab).1 (lt_iff_le_not_ge.mp hab).2) hvi⟩

/-- Vocabulary Insertion as a `Realization`: roots as indices, contexts as
contexts, `none` as non-licensing. -/
def VocabItem.toRealization (rules : List (VocabItem Ctx Root)) :
    Morphology.Realization Root Ctx String :=
  ⟨fun r c => match vocabularyInsert rules c r with
    | some f => {f}
    | none => ∅⟩

theorem VocabItem.toRealization_isUnivalent (rules : List (VocabItem Ctx Root)) :
    (toRealization rules).IsUnivalent :=
  fun r c => by
    simp only [toRealization]
    cases vocabularyInsert rules c r <;> simp

end VocabItem

end DistributedMorphology
