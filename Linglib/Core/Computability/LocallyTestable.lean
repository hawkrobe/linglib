/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.Definite
public import Linglib.Core.Computability.StarFree
public import Linglib.Core.Data.List.Factors
public import Mathlib.Data.Fintype.Powerset

/-!
# Locally testable languages

A language is *locally `k`-testable* when membership of a word depends only on its prefix and
suffix of length `k - 1` and on the set of its factors of length `k`. These are the locally
testable events of McNaughton and Papert.

## Main definitions

* `List.localProfile k w`: the prefix and suffix of `w` of length `k - 1` and the set of its
  factors of length `k`.
* `Language.IsLocallyTestable`: membership in the language factors through `List.localProfile k`.

## Main results

* `List.localProfile_append_congr`: words with the same local profiles have concatenations with
  the same local profile.
* `Language.IsLocallyTestable.isStarFree`: over a finite alphabet, locally testable languages are
  star-free.
* `Language.IsLocallyTestable.leftQuotient`, `Language.IsLocallyTestable.rightQuotient`,
  `Language.IsLocallyTestable.preimage_map`: closure under quotients and under inverse images of
  letter-to-letter maps.
* `Language.isStarFree_setOf_infix`: the words containing a given factor form a star-free
  language, over any alphabet.

## Implementation notes

The prefix and suffix have length `k - 1`, the width of the boundary padding that a strictly
`k`-local grammar reads, so that a strictly `k`-local language is locally `k`-testable at the
same `k`.

## References

* [mcnaughton-papert-1971]
* [pin-mfa]
-/

@[expose] public section

namespace List

variable {α β : Type*} {k : ℕ} {u u' v v' : List α}

/-- The prefix and suffix of `w` of length `k - 1`, and the set of its factors of length `k`. -/
def localProfile (k : ℕ) (w : List α) : List α × List α × Set (List α) :=
  (Edge.left.takeAt (k - 1) w, Edge.right.takeAt (k - 1) w, {f | f ∈ w.kFactors k})

/-- Words with the same local profiles have concatenations with the same local profile, since a
factor across the seam lies in the suffix of one word followed by the prefix of the other. -/
theorem localProfile_append_congr (hu : u.localProfile k = u'.localProfile k)
    (hv : v.localProfile k = v'.localProfile k) :
    (u ++ v).localProfile k = (u' ++ v').localProfile k := by
  simp only [localProfile, Prod.mk.injEq, Set.ext_iff, Set.mem_ofPred_eq] at hu hv ⊢
  obtain ⟨hul, hur, huf⟩ := hu
  obtain ⟨hvl, hvr, hvf⟩ := hv
  refine ⟨(Edge.takeAt_append_congr _ hul _).trans (Edge.takeAt_append_congr_right _ hvl _),
    (Edge.takeAt_append_congr _ hur _).trans (Edge.takeAt_append_congr_right _ hvr _), fun f ↦ ?_⟩
  grind [mem_kFactors_append, Edge.takeAt_left, Edge.takeAt_right]

/-- Mapping a function over a word maps it over the local profile. -/
theorem localProfile_map (g : α → β) (w : List α) :
    (w.map g).localProfile k =
      Prod.map (map g) (Prod.map (map g) (Set.image (map g))) (w.localProfile k) := by
  ext <;> simp [localProfile, Edge.takeAt_map]

/-- `k + 1` copies of a word have the same local profile as `k` copies, since a factor of length
`k` reaches across at most `k` consecutive copies. -/
theorem localProfile_flatten_replicate_succ (k : ℕ) (w : List α) :
    (replicate (k + 1) w).flatten.localProfile k = (replicate k w).flatten.localProfile k := by
  rcases eq_or_ne w [] with rfl | hw
  · simp
  obtain _ | n := k
  · simp [localProfile, Set.ext_iff, mem_kFactors]
  have hlen (m : ℕ) : m ≤ (replicate m w).flatten.length := by
    simpa using Nat.le_mul_of_pos_right m (length_pos_iff.mpr hw)
  have hl (m : ℕ) : (replicate (m + 1) w).flatten = (replicate m w).flatten ++ w := by
    rw [replicate_succ', flatten_append, flatten_singleton]
  have hr (m : ℕ) : (replicate (m + 1) w).flatten = w ++ (replicate m w).flatten := by
    rw [replicate_succ, flatten_cons]
  simp only [localProfile, Nat.add_sub_cancel, Prod.mk.injEq, Edge.takeAt_left, Edge.takeAt_right,
    Set.ext_iff, Set.mem_ofPred_eq]
  refine ⟨?_, ?_, fun f ↦ ?_⟩
  · rw [hl, take_append_of_le_length ((Nat.le_succ n).trans (hlen _))]
  · rw [hr, rtake_append_of_le_length ((Nat.le_succ n).trans (hlen _))]
  · rw [hl, mem_kFactors_append, Nat.add_sub_cancel]
    refine or_iff_left_of_imp ?_
    rintro (hf | hf) <;> rw [mem_kFactors] at hf ⊢ <;> refine ⟨hf.1.trans ?_, hf.2⟩
    · exact hr n ▸ (prefix_append _ _).isInfix
    · rw [hr n, rtake_append_of_le_length (hlen n), ← hr n, hl n]
      exact infix_append_iff.mpr (.inr (.inr ⟨_, _, rfl, rtake_suffix _ _, take_prefix _ _⟩))

/-- Over a finite alphabet `List.localProfile k` takes finitely many values. -/
theorem finite_range_localProfile [Finite α] (k : ℕ) :
    (Set.range (localProfile (α := α) k)).Finite :=
  ((Edge.finite_range_takeAt .left (k - 1)).prod <| (Edge.finite_range_takeAt .right (k - 1)).prod
    (List.finite_length_eq α k).finite_subsets).subset <| Set.range_subset_iff.2 fun w ↦
      ⟨⟨w, rfl⟩, ⟨w, rfl⟩, fun _ hf ↦ (mem_kFactors.mp hf).2⟩

end List

namespace Language

variable {α β : Type*} {L M : Language α} {k : ℕ}

/-- A language is *locally `k`-testable* when membership factors through the prefix and suffix of
length `k - 1` and the set of factors of length `k`. -/
def IsLocallyTestable (L : Language α) (k : ℕ) : Prop :=
  Function.FactorsThrough (· ∈ L) (List.localProfile k)

theorem IsLocallyTestable.compl (h : L.IsLocallyTestable k) : Lᶜ.IsLocallyTestable k :=
  fun _ _ e ↦ congrArg Not (h e)

theorem IsLocallyTestable.inter (hL : L.IsLocallyTestable k) (hM : M.IsLocallyTestable k) :
    (L ⊓ M).IsLocallyTestable k :=
  fun _ _ e ↦ congrArg₂ And (hL e) (hM e)

theorem IsLocallyTestable.union (hL : L.IsLocallyTestable k) (hM : M.IsLocallyTestable k) :
    (L ⊔ M).IsLocallyTestable k :=
  fun _ _ e ↦ congrArg₂ Or (hL e) (hM e)

/-- The words whose set of factors of length `k` lies in a given family form a locally
`k`-testable language. -/
theorem isLocallyTestable_setOf_kFactors (k : ℕ) (P : Set (Set (List α))) :
    IsLocallyTestable {w | {f | f ∈ w.kFactors k} ∈ P} k :=
  fun _ _ e ↦ congrArg (fun p ↦ p.2.2 ∈ P) e

/-- A generalized `(k - 1)`-definite language is locally `k`-testable. -/
theorem IsGeneralizedDefinite.toIsLocallyTestable (h : L.IsGeneralizedDefinite (k - 1)) :
    L.IsLocallyTestable k :=
  fun _ _ e ↦ propext <|
    isGeneralizedDefinite_iff_edges.mp h (congrArg Prod.fst e) (congrArg (·.2.1) e)

theorem IsLocallyTestable.leftQuotient (h : L.IsLocallyTestable k) (u : List α) :
    (L.leftQuotient u).IsLocallyTestable k :=
  fun _ _ e ↦ h (List.localProfile_append_congr rfl e)

theorem IsLocallyTestable.rightQuotient (h : L.IsLocallyTestable k) (u : List α) :
    (L.rightQuotient u).IsLocallyTestable k :=
  fun _ _ e ↦ h (List.localProfile_append_congr e rfl)

/-- Locally testable languages are closed under inverse images of letter-to-letter maps. -/
theorem IsLocallyTestable.preimage_map {L : Language β} (h : L.IsLocallyTestable k) (g : α → β) :
    IsLocallyTestable {w : List α | w.map g ∈ L} k :=
  fun _ _ e ↦ h (by rw [List.localProfile_map, List.localProfile_map, e])

/-- Over a finite alphabet locally testable languages are star-free. -/
theorem IsLocallyTestable.isStarFree [Finite α] (h : L.IsLocallyTestable k) : L.IsStarFree :=
  .of_factorsThrough h (fun _ _ _ _ ↦ List.localProfile_append_congr)
    (List.finite_range_localProfile k) (List.localProfile_flatten_replicate_succ k)

/-! ### Containing a factor -/

/-- The words containing `c` as a factor form a locally testable language. -/
theorem isLocallyTestable_setOf_infix (c : List α) :
    IsLocallyTestable {w | c <:+: w} c.length := by
  simpa [List.mem_kFactors] using isLocallyTestable_setOf_kFactors c.length {S | c ∈ S}

/-- The positions of `c` that hold the letter `a`. Recording them for each letter of a word
collapses any alphabet onto a finite one without losing the occurrences of `c`. -/
private def occ (c : List α) (a : α) : Set (Fin c.length) := {i | c[i] = a}

private theorem eq_of_map_occ_eq {c m : List α} (h : m.map (occ c) = c.map (occ c)) : m = c := by
  refine List.ext_getElem (by simpa using congrArg List.length h) fun i h₁ h₂ ↦ ?_
  have hi : occ c m[i] = occ c c[i] := by simpa [h₁, h₂] using congrArg (·[i]?) h
  exact ((Set.ext_iff.mp hi ⟨i, h₂⟩).mpr rfl).symm

private theorem infix_iff_map_occ (c x : List α) :
    c <:+: x ↔ c.map (occ c) <:+: x.map (occ c) := by
  refine ⟨fun h ↦ h.map _, fun ⟨s, t, hst⟩ ↦ ?_⟩
  obtain ⟨l, q, rfl, hl, -⟩ := List.map_eq_append_iff.mp hst.symm
  obtain ⟨p, m, rfl, -, hm⟩ := List.map_eq_append_iff.mp hl
  exact eq_of_map_occ_eq hm ▸ ⟨p, q, rfl⟩

/-- The words containing `c` as a factor form a star-free language over any alphabet, finite or
not. -/
theorem isStarFree_setOf_infix (c : List α) : IsStarFree {w | c <:+: w} := by
  convert (isLocallyTestable_setOf_infix (c.map (occ c))).isStarFree.comap
    (FreeMonoid.map (occ c)) using 1
  ext w
  exact infix_iff_map_occ c w

end Language
