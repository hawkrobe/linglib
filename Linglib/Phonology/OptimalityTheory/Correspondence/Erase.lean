import Linglib.Phonology.OptimalityTheory.Correspondence

/-!
# Deletion and insertion of one segment

This file defines the two elementary unfaithful mappings of Correspondence Theory. The deletion
of the segment at a position relates a string to the string without it, every other segment
corresponding to itself. The insertion of a segment at a position is the converse.

The violation profile of each is a theorem. A deletion violates MAX once and DEP never, and it
violates a positional MAX exactly when the deleted position is one the constraint protects. An
insertion violates DEP once and MAX never.

## Main definitions

* `Correspondence.deletion`, `Correspondence.eraseIdx`: the deletion of the segment at a
  position, with and without changes to the other segments.
* `Correspondence.insertIdx`: the insertion of a segment at a position.

## Main results

* `Correspondence.maxViol_deletion`, `depViol_deletion`, `maxViolAt_deletion`: the profile of
  a deletion.
* `Correspondence.depViol_insertIdx`, `maxViol_insertIdx`, `depViolAt_insertIdx`: the profile
  of an insertion.

## References

* [mccarthy-prince-1995]
-/

namespace OptimalityTheory.Correspondence

variable {α : Type*}

/-- `skip m n i` is the order-preserving relation between `Fin m` and `Fin n` that skips
position `i` of the first, relating `a` to `b` when `a` is `b` below `i` and `b + 1` from `i`
on. -/
def skip (m n i : ℕ) : Finset (Fin m × Fin n) :=
  Finset.univ.filter fun p ↦ (p.1 : ℕ) = if (p.2 : ℕ) < i then (p.2 : ℕ) else p.2 + 1

@[simp] theorem mem_skip {m n i : ℕ} {p : Fin m × Fin n} :
    p ∈ skip m n i ↔ (p.1 : ℕ) = if (p.2 : ℕ) < i then (p.2 : ℕ) else p.2 + 1 := by
  simp [skip]

/-- With one position fewer on the right, the positions of the left related to some position of
the right are those other than `i`. -/
theorem mem_image_fst_skip {m n i : ℕ} (hm : m = n + 1) (hi : i < m) {a : Fin m} :
    a ∈ (skip m n i).image Prod.fst ↔ (a : ℕ) ≠ i := by
  subst hm
  constructor
  · intro h
    obtain ⟨⟨a', b⟩, hp, rfl⟩ := Finset.mem_image.1 h
    rw [mem_skip] at hp
    dsimp only at hp ⊢
    split_ifs at hp <;> omega
  · intro ha
    by_cases h : (a : ℕ) < i
    · exact Finset.mem_image.2 ⟨(a, ⟨a, by omega⟩), mem_skip.2 (by simp [h]), rfl⟩
    · exact Finset.mem_image.2 ⟨(a, ⟨a - 1, by omega⟩), mem_skip.2 (by
        dsimp only; split_ifs <;> omega), rfl⟩

/-- With one position fewer on the right, every position of the right is related to some
position of the left. -/
theorem image_snd_skip {m n i : ℕ} (hm : m = n + 1) :
    (skip m n i).image Prod.snd = Finset.univ := by
  subst hm
  refine Finset.eq_univ_iff_forall.2 fun b ↦ ?_
  by_cases h : (b : ℕ) < i
  · exact Finset.mem_image.2 ⟨(⟨b, by omega⟩, b), mem_skip.2 (by simp [h]), rfl⟩
  · exact Finset.mem_image.2 ⟨(⟨b + 1, by omega⟩, b), mem_skip.2 (by simp [h]), rfl⟩

/-- `deletion s t i` relates `s` to a string `t` one segment shorter by skipping position `i` of
`s`, every other position of `s` corresponding to the position of `t` in the same order. The
segments of `t` need not be those of `s`, so a deletion may come with changes elsewhere. -/
def deletion (s t : List α) (i : ℕ) : Correspondence BinaryRole α where
  form
    | .lhs => s
    | .rhs => t
  edge
    | .lhs, .rhs => skip _ _ i
    | .rhs, .lhs => (skip _ _ i).image Prod.swap
    | .lhs, .lhs => diagonal _ _
    | .rhs, .rhs => diagonal _ _

/-- `eraseIdx s i` is the deletion of the segment at position `i` of `s` with every other
segment unchanged. -/
def eraseIdx (s : List α) (i : ℕ) : Correspondence BinaryRole α := deletion s (s.eraseIdx i) i

/-- `insertIdx s i a` is the insertion of the segment `a` at position `i` of `s`, the converse
of the deletion of position `i` from the longer string. -/
def insertIdx (s : List α) (i : ℕ) (a : α) : Correspondence BinaryRole α where
  form
    | .lhs => s
    | .rhs => s.insertIdx i a
  edge
    | .lhs, .rhs => (skip _ _ i).image Prod.swap
    | .rhs, .lhs => skip _ _ i
    | .lhs, .lhs => diagonal _ _
    | .rhs, .rhs => diagonal _ _

variable (s t : List α) (i : ℕ) (a : α)

@[simp] theorem deletion_form_lhs : (deletion s t i).form .lhs = s := rfl

@[simp] theorem deletion_form_rhs : (deletion s t i).form .rhs = t := rfl

@[simp] theorem eraseIdx_form_lhs : (eraseIdx s i).form .lhs = s := rfl

@[simp] theorem eraseIdx_form_rhs : (eraseIdx s i).form .rhs = s.eraseIdx i := rfl

@[simp] theorem insertIdx_form_lhs : (insertIdx s i a).form .lhs = s := rfl

@[simp] theorem insertIdx_form_rhs : (insertIdx s i a).form .rhs = s.insertIdx i a := rfl

/-! ### The profile of a deletion -/

private theorem image_fst_image_swap {m n : ℕ} (S : Finset (Fin m × Fin n)) :
    (S.image Prod.swap).image Prod.fst = S.image Prod.snd := by
  rw [Finset.image_image]; rfl

private theorem image_snd_image_swap {m n : ℕ} (S : Finset (Fin m × Fin n)) :
    (S.image Prod.swap).image Prod.snd = S.image Prod.fst := by
  rw [Finset.image_image]; rfl

private theorem card_filter_sdiff {m n i : ℕ} (hm : m = n + 1) (hi : i < m) (P : ℕ → Prop)
    [DecidablePred P] :
    ((Finset.univ.filter fun a : Fin m ↦ P a) \ (skip m n i).image Prod.fst).card =
      if P i then 1 else 0 := by
  have : (Finset.univ.filter fun a : Fin m ↦ P a) \ (skip m n i).image Prod.fst =
      if P i then {⟨i, hi⟩} else ∅ := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_image_fst_skip hm hi, ne_eq, not_not]
    split_ifs with hP
    · rw [Finset.mem_singleton, Fin.ext_iff]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ hP, h⟩⟩
    · simp only [Finset.notMem_empty, iff_false, not_and]
      exact fun h h' ↦ hP (h' ▸ h)
  rw [this]; split_ifs <;> rfl

variable {s t i}

/-- A deletion violates a positional MAX exactly when the deleted position is protected. -/
theorem maxViolAt_deletion (hlen : s.length = t.length + 1) (hi : i < s.length) (P : ℕ → Prop)
    [DecidablePred P] : (deletion s t i).maxViolAt P .lhs .rhs = if P i then 1 else 0 :=
  card_filter_sdiff hlen hi P

/-- A deletion violates MAX once. -/
theorem maxViol_deletion (hlen : s.length = t.length + 1) (hi : i < s.length) :
    (deletion s t i).maxViol .lhs .rhs = 1 := by
  rw [← maxViolAt_true, maxViolAt_deletion hlen hi, ite_eq_left trivial]

/-- A deletion does not violate DEP. -/
theorem depViol_deletion (hlen : s.length = t.length + 1) :
    (deletion s t i).depViol .lhs .rhs = 0 := by
  rw [depViol_eq_zero_iff]
  exact (image_snd_skip hlen).ge

private theorem length_eq_length_eraseIdx_add_one (hi : i < s.length) :
    s.length = (s.eraseIdx i).length + 1 := by
  simp [List.length_eraseIdx, hi]; omega

theorem maxViolAt_eraseIdx (hi : i < s.length) (P : ℕ → Prop) [DecidablePred P] :
    (eraseIdx s i).maxViolAt P .lhs .rhs = if P i then 1 else 0 :=
  maxViolAt_deletion (length_eq_length_eraseIdx_add_one hi) hi P

theorem maxViol_eraseIdx (hi : i < s.length) : (eraseIdx s i).maxViol .lhs .rhs = 1 :=
  maxViol_deletion (length_eq_length_eraseIdx_add_one hi) hi

theorem depViol_eraseIdx (hi : i < s.length) : (eraseIdx s i).depViol .lhs .rhs = 0 :=
  depViol_deletion (length_eq_length_eraseIdx_add_one hi)

/-! ### The profile of an insertion -/

/-- An insertion violates a positional DEP exactly when the inserted position is one the
constraint covers. -/
theorem depViolAt_insertIdx (hi : i ≤ s.length) (P : ℕ → Prop) [DecidablePred P] :
    (insertIdx s i a).depViolAt P .lhs .rhs = if P i then 1 else 0 := by
  have hlen : (s.insertIdx i a).length = s.length + 1 := List.length_insertIdx_of_le_length hi a
  rw [depViolAt]
  show ((Finset.univ.filter fun j : Fin (s.insertIdx i a).length ↦ P j) \
    ((skip _ _ i).image Prod.swap).image Prod.snd).card = _
  rw [image_snd_image_swap]
  exact card_filter_sdiff hlen (by omega) P

/-- An insertion violates DEP once. -/
theorem depViol_insertIdx (hi : i ≤ s.length) : (insertIdx s i a).depViol .lhs .rhs = 1 := by
  rw [← depViolAt_true, depViolAt_insertIdx a hi, ite_eq_left trivial]

/-- An insertion does not violate MAX. -/
theorem maxViol_insertIdx (hi : i ≤ s.length) : (insertIdx s i a).maxViol .lhs .rhs = 0 := by
  rw [maxViol_eq_zero_iff]
  show Finset.univ ⊆ ((skip _ _ i).image Prod.swap).image Prod.fst
  rw [image_fst_image_swap]
  exact (image_snd_skip (List.length_insertIdx_of_le_length hi a)).ge

end OptimalityTheory.Correspondence
