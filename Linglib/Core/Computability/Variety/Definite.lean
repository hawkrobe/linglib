/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.Variety.Definite`.
-/
import Linglib.Core.Computability.Definite
import Linglib.Core.Computability.Variety.SemigroupLangs

/-!
# Definite languages and the pseudovarieties **D** and **K**

The Eilenberg correspondence sends the pseudovariety **D** of definite semigroups to the definite
languages, and **K** to the reverse-definite ones ([eilenberg-1976] Ch. VIII, [pin-mfa]). This file
proves the language-to-algebra half of both: such a language over a finite alphabet is regular, its
syntactic semigroup lies in the pseudovariety, and hence the language lies in the pseudovariety's
`langs`.

Everything rests on one combinatorial fact — *screening*: a `k`-definite language cannot see
anything prepended to a word of length `≥ k`, because the prepended block falls outside the
length-`k` window (`List.rtake_append_append_of_le_length`). Idempotence supplies words of
unbounded length in a given class, which is what turns the language statement into the semigroup
equation `s * e = e`. The reverse-definite case mirrors this through the left edge.

## Main results

* `Language.IsDefinite.syntacticEquiv_append_left` and
  `Language.IsReverseDefinite.syntacticEquiv_append_right`: screening at each edge.
* `Language.IsDefinite.isRegular`, `Language.IsReverseDefinite.isRegular`: over a finite alphabet
  the edge projection bounds the syntactic monoid, so the language is regular.
* `Language.IsDefinite.langs_definiteVariety`,
  `Language.IsReverseDefinite.langs_reverseDefiniteVariety`: membership in the language varieties
  of **D** and **K**.

The converse inclusions, and the joint two-edge class **LI**, are not yet formalised.
-/

namespace Language

variable {α : Type*} {L : Language α} {k : ℕ}

/-! ### Screening

A block of length `≥ k` hides everything to its left from the length-`k` window. -/

private theorem rtake_append_middle {u : List α} (hu : k ≤ u.length) (t x y : List α) :
    (x ++ (t ++ u) ++ y).rtake k = (x ++ u ++ y).rtake k := by
  rw [List.rtake_append_append_of_le_length x (t ++ u) y
      (by simp only [List.length_append]; omega),
    List.rtake_append_append_of_le_length t u y hu,
    List.rtake_append_append_of_le_length x u y hu]

/-- **Screening.** A `k`-definite language is blind to a prefix prepended to a word of length
`≥ k`: the length-`k` window never reaches past `u`. -/
theorem IsDefinite.syntacticEquiv_append_left (h : L.IsDefinite k) {u : List α}
    (hu : k ≤ u.length) (t : List α) : L.SyntacticEquiv (t ++ u) u :=
  fun x y => iff_of_eq (h (rtake_append_middle hu t x y))

/-- Words sharing their length-`k` suffix are `L`-equivalent — definiteness restated as a bound on
the syntactic congruence. -/
theorem IsDefinite.syntacticEquiv_of_rtake_eq (h : L.IsDefinite k) {u v : List α}
    (huv : u.rtake k = v.rtake k) : L.SyntacticEquiv u v := by
  have hlen : min k u.length = min k v.length := by
    simpa only [List.length_rtake] using congrArg List.length huv
  rcases le_or_gt k u.length with hu | hu
  · have key : ∀ w : List α, k ≤ w.length → L.SyntacticEquiv w (w.rtake k) := fun w hw => by
      conv_lhs => rw [← List.rdrop_append_rtake w k]
      exact h.syntacticEquiv_append_left (by rw [List.length_rtake]; omega) _
    exact ((key u hu).trans (huv ▸ .refl _)).trans (key v (by omega)).symm
  · rw [List.rtake_of_length_le hu.le, List.rtake_of_length_le (by omega)] at huv
    exact huv ▸ .refl _

/-! ### Regularity

The length-`k` suffix is a section of the syntactic projection, so the syntactic monoid is no
bigger than the set of words of length `≤ k`. -/

/-- **A definite language over a finite alphabet is regular**: every syntactic class contains a
word of length `≤ k`, namely the length-`k` suffix of any of its members, and there are finitely
many such words. -/
theorem IsDefinite.isRegular [Finite α] (h : L.IsDefinite k) : L.IsRegular := by
  haveI : Finite {w : List α // w.length ≤ k} := (List.finite_length_le α k).to_subtype
  refine isRegular_of_finite_syntacticMonoid (Finite.of_surjective
    (fun w : {w : List α // w.length ≤ k} => L.syntacticClass w.1) fun m => ?_)
  obtain ⟨u, rfl⟩ := L.syntacticClass_surjective m
  have hidem : (u.rtake k).rtake k = u.rtake k := by rw [List.rtake_rtake, min_self]
  exact ⟨⟨u.rtake k, by rw [List.length_rtake]; omega⟩,
    L.syntacticClass_eq_iff.2 (h.syntacticEquiv_of_rtake_eq hidem)⟩

/-! ### The syntactic semigroup lies in **D** -/

/-- An idempotent class contains words of every length: concatenating `w` with a long member of
its own class stays in the class and grows. -/
private theorem exists_length_le_syntacticEquiv {w : List α} (hw : w ≠ [])
    (hidem : L.SyntacticEquiv (w ++ w) w) (n : ℕ) :
    ∃ m : List α, n ≤ m.length ∧ L.SyntacticEquiv m w := by
  induction n with
  | zero => exact ⟨w, Nat.zero_le _, .refl _⟩
  | succ n ih =>
    obtain ⟨m, hm, hmw⟩ := ih
    refine ⟨w ++ m, ?_,
      SyntacticEquiv.trans (SyntacticEquiv.append (SyntacticEquiv.refl w) hmw) hidem⟩
    have : 0 < w.length := List.length_pos_iff.2 hw
    simp only [List.length_append]; omega

/-- **The syntactic semigroup of a definite language is definite**: `s * e = e` for idempotent `e`.
Idempotence lets `e` be represented by an arbitrarily long word, and screening then makes the left
factor invisible. -/
theorem IsDefinite.isDefinite_syntacticSemigroup (h : L.IsDefinite k) :
    Semigroup.IsDefinite L.syntacticSemigroup := by
  intro e he s
  obtain ⟨u, rfl⟩ := L.toSyntacticSemigroup_surjective e
  obtain ⟨t, rfl⟩ := L.toSyntacticSemigroup_surjective s
  have hidem : L.syntacticSemigroupCon (u * u) u :=
    L.toSyntacticSemigroup_eq_iff.1 (by rw [map_mul]; exact he)
  obtain ⟨m, hm, hmu⟩ := exists_length_le_syntacticEquiv u.toList_ne_nil hidem k
  rw [← map_mul]
  exact L.toSyntacticSemigroup_eq_iff.2
    (SyntacticEquiv.trans (SyntacticEquiv.append (SyntacticEquiv.refl t.toList) hmu.symm)
      ((h.syntacticEquiv_append_left hm t.toList).trans hmu))

/-- **The language half of `D`**: a definite language over a finite alphabet lies in the language
variety of the pseudovariety **D**. -/
theorem IsDefinite.langs_definiteVariety [Finite α] (h : L.IsDefinite k) :
    Semigroup.definiteVariety.langs L :=
  ⟨h.isRegular, h.isDefinite_syntacticSemigroup⟩

/-! ### The dual: reverse-definite languages and **K**

Everything mirrors through the left edge. The screening lemma is cheaper here, since
`List.take_append_of_le_length` already says a long enough prefix ignores what follows. -/

private theorem take_append_middle {u : List α} (hu : k ≤ u.length) (t x y : List α) :
    (x ++ (u ++ t) ++ y).take k = (x ++ u ++ y).take k := by
  have h₁ : k ≤ (x ++ u).length := by simp only [List.length_append]; omega
  rw [List.take_append_of_le_length (by simp only [List.length_append]; omega),
    ← List.append_assoc, List.take_append_of_le_length h₁,
    List.take_append_of_le_length h₁]

/-- **Screening, left edge.** A reverse-`k`-definite language is blind to a suffix appended to a
word of length `≥ k`. -/
theorem IsReverseDefinite.syntacticEquiv_append_right (h : L.IsReverseDefinite k) {u : List α}
    (hu : k ≤ u.length) (t : List α) : L.SyntacticEquiv (u ++ t) u :=
  fun x y => iff_of_eq (h (take_append_middle hu t x y))

/-- Words sharing their length-`k` prefix are `L`-equivalent. -/
theorem IsReverseDefinite.syntacticEquiv_of_take_eq (h : L.IsReverseDefinite k) {u v : List α}
    (huv : u.take k = v.take k) : L.SyntacticEquiv u v := by
  have hlen : min k u.length = min k v.length := by
    simpa only [List.length_take] using congrArg List.length huv
  rcases le_or_gt k u.length with hu | hu
  · have key : ∀ w : List α, k ≤ w.length → L.SyntacticEquiv w (w.take k) := fun w hw => by
      conv_lhs => rw [← List.take_append_drop k w]
      exact h.syntacticEquiv_append_right (by rw [List.length_take]; omega) _
    exact ((key u hu).trans (huv ▸ .refl _)).trans (key v (by omega)).symm
  · rw [List.take_of_length_le hu.le, List.take_of_length_le (by omega)] at huv
    exact huv ▸ .refl _

/-- **A reverse-definite language over a finite alphabet is regular** — the length-`k` prefix
picks a bounded representative from each syntactic class. -/
theorem IsReverseDefinite.isRegular [Finite α] (h : L.IsReverseDefinite k) : L.IsRegular := by
  haveI : Finite {w : List α // w.length ≤ k} := (List.finite_length_le α k).to_subtype
  refine isRegular_of_finite_syntacticMonoid (Finite.of_surjective
    (fun w : {w : List α // w.length ≤ k} => L.syntacticClass w.1) fun m => ?_)
  obtain ⟨u, rfl⟩ := L.syntacticClass_surjective m
  have hidem : (u.take k).take k = u.take k := by rw [List.take_take, min_self]
  exact ⟨⟨u.take k, by rw [List.length_take]; omega⟩,
    L.syntacticClass_eq_iff.2 (h.syntacticEquiv_of_take_eq hidem)⟩

/-- **The syntactic semigroup of a reverse-definite language is reverse definite**: `e * s = e`
for idempotent `e`. -/
theorem IsReverseDefinite.isReverseDefinite_syntacticSemigroup (h : L.IsReverseDefinite k) :
    Semigroup.IsReverseDefinite L.syntacticSemigroup := by
  intro e he s
  obtain ⟨u, rfl⟩ := L.toSyntacticSemigroup_surjective e
  obtain ⟨t, rfl⟩ := L.toSyntacticSemigroup_surjective s
  have hidem : L.syntacticSemigroupCon (u * u) u :=
    L.toSyntacticSemigroup_eq_iff.1 (by rw [map_mul]; exact he)
  obtain ⟨m, hm, hmu⟩ := exists_length_le_syntacticEquiv u.toList_ne_nil hidem k
  rw [← map_mul]
  exact L.toSyntacticSemigroup_eq_iff.2
    (SyntacticEquiv.trans (SyntacticEquiv.append hmu.symm (SyntacticEquiv.refl t.toList))
      ((h.syntacticEquiv_append_right hm t.toList).trans hmu))

/-- **The language half of `K`**: a reverse-definite language over a finite alphabet lies in the
language variety of the pseudovariety **K**. -/
theorem IsReverseDefinite.langs_reverseDefiniteVariety [Finite α] (h : L.IsReverseDefinite k) :
    Semigroup.reverseDefiniteVariety.langs L :=
  ⟨h.isRegular, h.isReverseDefinite_syntacticSemigroup⟩

end Language
