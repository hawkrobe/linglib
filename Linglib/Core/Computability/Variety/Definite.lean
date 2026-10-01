/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.Variety.Definite`.
-/
module

public import Linglib.Core.Algebra.Group.Idempotent
public import Linglib.Core.Computability.Definite
public import Linglib.Core.Computability.Variety.SemigroupLangs

/-!
# Definite languages and the pseudovarieties **D**, **K** and **LI**

This file proves the Eilenberg correspondences for the definite languages and their relatives.
Over a finite alphabet, the definite, reverse definite and generalized definite languages are
exactly the regular languages whose syntactic semigroup lies in the pseudovariety **D**, **K** and
**LI** respectively, and the finite or cofinite languages are those whose syntactic semigroup lies
in both **D** and **K**. Both directions pass through a window characterization in the syntactic
monoid: `L` is `k`-definite exactly when the class of every word of length at least `k` is a right
zero, and similarly for the other two classes.

## Main results

* `Language.isDefinite_iff_forall_isRightZero_syntacticClass` and its two mirrors: the windows.
* `Language.isDefinite_natCard_of_isDefinite_syntacticSemigroup` and its two mirrors: a syntactic
  semigroup `S` in the pseudovariety bounds the window by `|S|`.
* `Language.langs_definiteVariety_iff`, `Language.langs_reverseDefiniteVariety_iff`,
  `Language.langs_locallyTrivialVariety_iff`: the Eilenberg correspondences.
* `Language.isFiniteOrCofinite_iff_syntacticSemigroup`: the finite or cofinite languages.

## Implementation notes

The bound `|S|` and the route through long products follow Chapter XIV of [pin-mfa]. The window
conditions range over words of length at least `k` rather than over the whole syntactic monoid,
because the pseudovarieties are varieties of semigroups and do not see the empty word.

## References

* [perles-rabin-shamir-1963]
* [eilenberg-1976]
* [pin-mfa]
-/

@[expose] public section

namespace Language

open FreeSemigroup

variable {α : Type*} {L : Language α} {k : ℕ}

/-! ### Window characterizations -/

/-- A language is regular when syntactic equivalence is implied by equality under a map with
finite range, since the syntactic monoid is then covered by the classes of chosen preimages. -/
private theorem isRegular_of_syntacticEquiv {β : Type*} (g : List α → β)
    (hg : (Set.range g).Finite) (h : ∀ u v, g u = g v → L.SyntacticEquiv u v) : L.IsRegular := by
  have := hg.to_subtype
  refine IsRegular.of_finite_syntacticMonoid <| Finite.of_surjective
    (fun b : Set.range g ↦ L.syntacticClass b.2.choose) fun m ↦ ?_
  obtain ⟨u, rfl⟩ := L.syntacticClass_surjective m
  exact ⟨⟨g u, u, rfl⟩, syntacticClass_eq_iff.2 (h _ _ (Exists.choose_spec (p := (g · = g u)) _))⟩

private theorem rtake_append_middle {u : List α} (hu : k ≤ u.length) (t x y : List α) :
    (x ++ (t ++ u) ++ y).rtake k = (x ++ u ++ y).rtake k := by
  rw [List.rtake_append_append_of_le_length x (t ++ u) y
      (by simp only [List.length_append]; omega),
    List.rtake_append_append_of_le_length t u y hu,
    List.rtake_append_append_of_le_length x u y hu]

private theorem take_append_middle {u : List α} (hu : k ≤ u.length) (t x y : List α) :
    (x ++ (u ++ t) ++ y).take k = (x ++ u ++ y).take k := by
  have h₁ : k ≤ (x ++ u).length := by simp only [List.length_append]; omega
  rw [List.take_append_of_le_length (by simp only [List.length_append]; omega),
    ← List.append_assoc, List.take_append_of_le_length h₁,
    List.take_append_of_le_length h₁]

/-! #### Definite languages -/

/-- A `k`-definite language is blind to a prefix prepended to a word of length at least `k`, since
the length-`k` window never reaches past the word. -/
theorem IsDefinite.syntacticEquiv_append_left (h : L.IsDefinite k) {u : List α}
    (hu : k ≤ u.length) (t : List α) : L.SyntacticEquiv (t ++ u) u :=
  fun x y ↦ iff_of_eq (h (rtake_append_middle hu t x y))

theorem IsDefinite.isRightZero_syntacticClass (h : L.IsDefinite k) {u : List α}
    (hu : k ≤ u.length) : IsRightZero (L.syntacticClass u) := fun m ↦ by
  obtain ⟨t, rfl⟩ := L.syntacticClass_surjective m
  rw [← syntacticClass_append, syntacticClass_eq_iff]
  exact h.syntacticEquiv_append_left hu t

/-- A language is `k`-definite exactly when the syntactic class of every word of length at least
`k` is a right zero of the syntactic monoid. -/
theorem isDefinite_iff_forall_isRightZero_syntacticClass :
    L.IsDefinite k ↔ ∀ u : List α, k ≤ u.length → IsRightZero (L.syntacticClass u) := by
  refine ⟨fun h _ ↦ h.isRightZero_syntacticClass, fun h ↦ isDefinite_iff_mem_takeAt.2 fun w ↦ ?_⟩
  rcases le_or_gt k w.length with hw | hw
  · refine mem_iff_of_syntacticClass_eq ?_
    conv_lhs => rw [← List.rdrop_append_rtake k w]
    rw [syntacticClass_append, Edge.takeAt_right,
      h _ (by rw [List.length_rtake]; omega)]
  · rw [Edge.takeAt_right, List.rtake_of_length_le hw.le]

/-- Words sharing their length-`k` suffix are equivalent for a `k`-definite language. -/
theorem IsDefinite.syntacticEquiv_of_rtake_eq (h : L.IsDefinite k) {u v : List α}
    (huv : u.rtake k = v.rtake k) : L.SyntacticEquiv u v := by
  have hlen : min k u.length = min k v.length := by
    simpa only [List.length_rtake] using congrArg List.length huv
  rcases le_or_gt k u.length with hu | hu
  · have key : ∀ w : List α, k ≤ w.length → L.SyntacticEquiv w (w.rtake k) := fun w hw ↦ by
      conv_lhs => rw [← List.rdrop_append_rtake k w]
      exact h.syntacticEquiv_append_left (by rw [List.length_rtake]; omega) _
    exact ((key u hu).trans (huv ▸ .refl _)).trans (key v (by omega)).symm
  · rw [List.rtake_of_length_le hu.le, List.rtake_of_length_le (by omega)] at huv
    exact huv ▸ .refl _

/-- A definite language over a finite alphabet is regular. -/
theorem IsDefinite.isRegular [Finite α] (h : L.IsDefinite k) : L.IsRegular :=
  isRegular_of_syntacticEquiv (·.rtake k)
    ((List.finite_length_le α k).subset (Set.range_subset_iff.2 fun w ↦ by simp))
    fun _ _ ↦ h.syntacticEquiv_of_rtake_eq

/-! #### Reverse definite languages -/

/-- A reverse `k`-definite language is blind to a suffix appended to a word of length at
least `k`. -/
theorem IsReverseDefinite.syntacticEquiv_append_right (h : L.IsReverseDefinite k) {u : List α}
    (hu : k ≤ u.length) (t : List α) : L.SyntacticEquiv (u ++ t) u :=
  fun x y ↦ iff_of_eq (h (take_append_middle hu t x y))

theorem IsReverseDefinite.isLeftZero_syntacticClass (h : L.IsReverseDefinite k) {u : List α}
    (hu : k ≤ u.length) : IsLeftZero (L.syntacticClass u) := fun m ↦ by
  obtain ⟨t, rfl⟩ := L.syntacticClass_surjective m
  rw [← syntacticClass_append, syntacticClass_eq_iff]
  exact h.syntacticEquiv_append_right hu t

/-- A language is reverse `k`-definite exactly when the syntactic class of every word of length at
least `k` is a left zero of the syntactic monoid. -/
theorem isReverseDefinite_iff_forall_isLeftZero_syntacticClass :
    L.IsReverseDefinite k ↔ ∀ u : List α, k ≤ u.length → IsLeftZero (L.syntacticClass u) := by
  refine ⟨fun h _ ↦ h.isLeftZero_syntacticClass,
    fun h ↦ isReverseDefinite_iff_mem_takeAt.2 fun w ↦ ?_⟩
  rcases le_or_gt k w.length with hw | hw
  · refine mem_iff_of_syntacticClass_eq ?_
    conv_lhs => rw [← List.take_append_drop k w]
    rw [syntacticClass_append, Edge.takeAt_left, h _ (by rw [List.length_take]; omega)]
  · rw [Edge.takeAt_left, List.take_of_length_le hw.le]

/-- Words sharing their length-`k` prefix are equivalent for a reverse `k`-definite language. -/
theorem IsReverseDefinite.syntacticEquiv_of_take_eq (h : L.IsReverseDefinite k) {u v : List α}
    (huv : u.take k = v.take k) : L.SyntacticEquiv u v := by
  have hlen : min k u.length = min k v.length := by
    simpa only [List.length_take] using congrArg List.length huv
  rcases le_or_gt k u.length with hu | hu
  · have key : ∀ w : List α, k ≤ w.length → L.SyntacticEquiv w (w.take k) := fun w hw ↦ by
      conv_lhs => rw [← List.take_append_drop k w]
      exact h.syntacticEquiv_append_right (by rw [List.length_take]; omega) _
    exact ((key u hu).trans (huv ▸ .refl _)).trans (key v (by omega)).symm
  · rw [List.take_of_length_le hu.le, List.take_of_length_le (by omega)] at huv
    exact huv ▸ .refl _

/-- A reverse definite language over a finite alphabet is regular. -/
theorem IsReverseDefinite.isRegular [Finite α] (h : L.IsReverseDefinite k) : L.IsRegular :=
  isRegular_of_syntacticEquiv (·.take k)
    ((List.finite_length_le α k).subset (Set.range_subset_iff.2 fun w ↦ by simp))
    fun _ _ ↦ h.syntacticEquiv_of_take_eq

/-! #### Generalized definite languages -/

/-- A generalized `k`-definite language is blind to anything placed between two copies of a word
of length at least `k`. -/
theorem IsGeneralizedDefinite.syntacticEquiv_append_append (h : L.IsGeneralizedDefinite k)
    {u : List α} (hu : k ≤ u.length) (t : List α) : L.SyntacticEquiv (u ++ t ++ u) u :=
  fun x y ↦ isGeneralizedDefinite_iff_edges.1 h
    (by rw [Edge.takeAt_left, Edge.takeAt_left, List.append_assoc u t u]
        exact take_append_middle hu _ x y)
    (rtake_append_middle hu _ x y)

theorem IsGeneralizedDefinite.syntacticClass_mul_mul_self (h : L.IsGeneralizedDefinite k)
    {u : List α} (hu : k ≤ u.length) (s : L.SyntacticMonoid) :
    L.syntacticClass u * s * L.syntacticClass u = L.syntacticClass u := by
  obtain ⟨t, rfl⟩ := L.syntacticClass_surjective s
  rw [← syntacticClass_append, ← syntacticClass_append, syntacticClass_eq_iff]
  exact h.syntacticEquiv_append_append hu t

/-- A language is generalized `k`-definite exactly when the syntactic class of every word of length
at least `k` absorbs anything placed between two copies of it. -/
theorem isGeneralizedDefinite_iff_forall_syntacticClass_mul_mul_self :
    L.IsGeneralizedDefinite k ↔ ∀ u : List α, k ≤ u.length → ∀ s,
      L.syntacticClass u * s * L.syntacticClass u = L.syntacticClass u := by
  refine ⟨fun h _ ↦ h.syntacticClass_mul_mul_self, fun h ↦ ?_⟩
  refine isGeneralizedDefinite_iff_edges.2 fun a b hpre hsuf ↦ mem_iff_of_syntacticClass_eq ?_
  rw [Edge.takeAt_left, Edge.takeAt_left] at hpre
  rw [Edge.takeAt_right, Edge.takeAt_right] at hsuf
  have hlen : min k a.length = min k b.length := by
    simpa only [List.length_take] using congrArg List.length hpre
  rcases le_or_gt k a.length with ha | ha
  · -- `[a] = [a] * [b] = [b]`: the shared prefix absorbs `[a]` on the left, the shared suffix
    -- absorbs `[b]` on the right.
    have hp := h (a.take k) (by rw [List.length_take]; omega)
    have hq := h (a.rtake k) (by rw [List.length_rtake]; omega)
    have ha₁ := List.take_append_drop k a
    have hb₁ : a.take k ++ b.drop k = b := hpre ▸ List.take_append_drop k b
    have ha₂ := List.rdrop_append_rtake k a
    have hb₂ : b.rdrop k ++ a.rtake k = b := hsuf ▸ List.rdrop_append_rtake k b
    have e₁ : L.syntacticClass a * L.syntacticClass b = L.syntacticClass b := by
      conv_lhs => rw [← ha₁, ← hb₁]
      rw [syntacticClass_append, syntacticClass_append, ← mul_assoc, hp, ← syntacticClass_append,
        hb₁]
    have e₂ : L.syntacticClass a * L.syntacticClass b = L.syntacticClass a := by
      conv_lhs => rw [← ha₂, ← hb₂]
      rw [syntacticClass_append, syntacticClass_append, mul_assoc,
        ← mul_assoc (L.syntacticClass (a.rtake k)), hq, ← syntacticClass_append, ha₂]
    exact e₂.symm.trans e₁
  · rw [List.take_of_length_le ha.le, List.take_of_length_le (by omega)] at hpre
    rw [hpre]

/-- Words sharing their length-`k` prefix and suffix are equivalent for a generalized `k`-definite
language. -/
theorem IsGeneralizedDefinite.syntacticEquiv_of_take_eq_of_rtake_eq
    (h : L.IsGeneralizedDefinite k) {u v : List α} (h₁ : u.take k = v.take k)
    (h₂ : u.rtake k = v.rtake k) : L.SyntacticEquiv u v := fun x y ↦ by
  have hlen : min k u.length = min k v.length := by
    simpa only [List.length_take] using congrArg List.length h₁
  rcases le_or_gt k u.length with hu | hu
  · have hv : k ≤ v.length := by omega
    refine isGeneralizedDefinite_iff_edges.1 h ?_ ?_
    · rw [Edge.takeAt_left, Edge.takeAt_left, ← List.take_append_drop k u,
        ← List.take_append_drop k v, ← h₁, take_append_middle (by simp [hu]),
        take_append_middle (by simp [hu])]
    · rw [Edge.takeAt_right, Edge.takeAt_right, ← List.rdrop_append_rtake k u,
        ← List.rdrop_append_rtake k v, ← h₂, rtake_append_middle (by simp [hu]),
        rtake_append_middle (by simp [hu])]
  · rw [List.take_of_length_le hu.le, List.take_of_length_le (by omega)] at h₁
    rw [h₁]

/-- A generalized definite language over a finite alphabet is regular. -/
theorem IsGeneralizedDefinite.isRegular [Finite α] (h : L.IsGeneralizedDefinite k) :
    L.IsRegular :=
  isRegular_of_syntacticEquiv (fun w ↦ (w.take k, w.rtake k))
    (((List.finite_length_le α k).prod (List.finite_length_le α k)).subset
      (Set.range_subset_iff.2 fun w ↦ by simp))
    fun _ _ huv ↦ h.syntacticEquiv_of_take_eq_of_rtake_eq (congrArg Prod.fst huv)
      (congrArg Prod.snd huv)

/-! ### The syntactic semigroup -/

theorem syntacticSemigroupToMonoid_mk (a : α) (l : List α) :
    L.syntacticSemigroupToMonoid (L.toSyntacticSemigroup ⟨a, l⟩) = L.syntacticClass (a :: l) := by
  rw [syntacticSemigroupToMonoid_apply, toFreeMonoid_mk_eq_cons]; rfl

/-- An element of the syntactic monoid is a right zero once it absorbs the image of the syntactic
semigroup, since everything else is the identity. -/
theorem isRightZero_iff_forall_syntacticSemigroupToMonoid_mul {x : L.SyntacticMonoid} :
    IsRightZero x ↔ ∀ s, L.syntacticSemigroupToMonoid s * x = x := by
  refine ⟨fun h s ↦ h _, fun h m ↦ ?_⟩
  rcases L.eq_one_or_mem_range_syntacticSemigroupToMonoid m with rfl | ⟨s, rfl⟩
  exacts [one_mul x, h s]

theorem isLeftZero_iff_forall_mul_syntacticSemigroupToMonoid {x : L.SyntacticMonoid} :
    IsLeftZero x ↔ ∀ s, x * L.syntacticSemigroupToMonoid s = x := by
  refine ⟨fun h s ↦ h _, fun h m ↦ ?_⟩
  rcases L.eq_one_or_mem_range_syntacticSemigroupToMonoid m with rfl | ⟨s, rfl⟩
  exacts [mul_one x, h s]

/-! #### From the language to the semigroup -/

/-- The syntactic semigroup of a definite language is definite. -/
theorem IsDefinite.isDefinite_syntacticSemigroup (h : L.IsDefinite k) :
    Semigroup.IsDefinite L.SyntacticSemigroup :=
  .of_mul_map_eq L.toSyntacticSemigroup_surjective fun w hw s ↦
    L.syntacticSemigroupToMonoid_injective <| by
      obtain ⟨a, l⟩ := w
      rw [map_mul, syntacticSemigroupToMonoid_mk]
      exact h.isRightZero_syntacticClass hw _

/-- The syntactic semigroup of a reverse definite language is reverse definite. -/
theorem IsReverseDefinite.isReverseDefinite_syntacticSemigroup (h : L.IsReverseDefinite k) :
    Semigroup.IsReverseDefinite L.SyntacticSemigroup :=
  .of_map_mul_eq L.toSyntacticSemigroup_surjective fun w hw s ↦
    L.syntacticSemigroupToMonoid_injective <| by
      obtain ⟨a, l⟩ := w
      rw [map_mul, syntacticSemigroupToMonoid_mk]
      exact h.isLeftZero_syntacticClass hw _

/-- The syntactic semigroup of a generalized definite language is locally trivial. -/
theorem IsGeneralizedDefinite.isLocallyTrivial_syntacticSemigroup
    (h : L.IsGeneralizedDefinite k) : Semigroup.IsLocallyTrivial L.SyntacticSemigroup :=
  .of_map_mul_map_eq L.toSyntacticSemigroup_surjective fun w hw s ↦
    L.syntacticSemigroupToMonoid_injective <| by
      obtain ⟨a, l⟩ := w
      rw [map_mul, map_mul, syntacticSemigroupToMonoid_mk]
      exact h.syntacticClass_mul_mul_self hw _

/-! #### From the semigroup to the language -/

section Converse

variable [Finite L.SyntacticSemigroup]

/-- The empty word has length at least `|S|` only when the syntactic semigroup is empty. -/
private theorem isEmpty_of_natCard_le_length_nil
    (hu : Nat.card L.SyntacticSemigroup ≤ ([] : List α).length) : IsEmpty L.SyntacticSemigroup :=
  not_nonempty_iff.1 fun _ ↦ (Nat.card_pos (α := L.SyntacticSemigroup)).not_ge hu

/-- A language with a definite syntactic semigroup `S` is `|S|`-definite. -/
theorem isDefinite_natCard_of_isDefinite_syntacticSemigroup
    (h : Semigroup.IsDefinite L.SyntacticSemigroup) :
    L.IsDefinite (Nat.card L.SyntacticSemigroup) := by
  refine isDefinite_iff_forall_isRightZero_syntacticClass.2 fun u hu ↦ ?_
  rw [isRightZero_iff_forall_syntacticSemigroupToMonoid_mul]
  rcases u with _ | ⟨a, l⟩
  · exact (isEmpty_of_natCard_le_length_nil hu).elim
  · intro s
    rw [← syntacticSemigroupToMonoid_mk, ← map_mul, h.mul_map_eq _ (w := ⟨a, l⟩) hu]

/-- A language with a reverse definite syntactic semigroup `S` is reverse `|S|`-definite. -/
theorem isReverseDefinite_natCard_of_isReverseDefinite_syntacticSemigroup
    (h : Semigroup.IsReverseDefinite L.SyntacticSemigroup) :
    L.IsReverseDefinite (Nat.card L.SyntacticSemigroup) := by
  refine isReverseDefinite_iff_forall_isLeftZero_syntacticClass.2 fun u hu ↦ ?_
  rw [isLeftZero_iff_forall_mul_syntacticSemigroupToMonoid]
  rcases u with _ | ⟨a, l⟩
  · exact (isEmpty_of_natCard_le_length_nil hu).elim
  · intro s
    rw [← syntacticSemigroupToMonoid_mk, ← map_mul, h.map_mul_eq _ (w := ⟨a, l⟩) hu]

/-- A language with a locally trivial syntactic semigroup `S` is generalized `|S|`-definite. -/
theorem isGeneralizedDefinite_natCard_of_isLocallyTrivial_syntacticSemigroup
    (h : Semigroup.IsLocallyTrivial L.SyntacticSemigroup) :
    L.IsGeneralizedDefinite (Nat.card L.SyntacticSemigroup) := by
  refine isGeneralizedDefinite_iff_forall_syntacticClass_mul_mul_self.2 fun u hu m ↦ ?_
  rcases u with _ | ⟨a, l⟩
  · rcases L.eq_one_or_mem_range_syntacticSemigroupToMonoid m with rfl | ⟨s, rfl⟩
    exacts [by simp, (isEmpty_of_natCard_le_length_nil hu).elim s]
  · replace hu : Nat.card _ ≤ (⟨a, l⟩ : FreeSemigroup α).length := hu
    rw [← syntacticSemigroupToMonoid_mk]
    rcases L.eq_one_or_mem_range_syntacticSemigroupToMonoid m with rfl | ⟨s, rfl⟩
    · rw [mul_one, ← map_mul, (h.isIdempotentElem_map _ hu).eq]
    · rw [← map_mul, ← map_mul, h.map_mul_map_eq _ hu]

theorem isDefinite_syntacticSemigroup_iff :
    Semigroup.IsDefinite L.SyntacticSemigroup ↔ ∃ k, L.IsDefinite k :=
  ⟨fun h ↦ ⟨_, isDefinite_natCard_of_isDefinite_syntacticSemigroup h⟩,
    fun ⟨_, h⟩ ↦ h.isDefinite_syntacticSemigroup⟩

theorem isReverseDefinite_syntacticSemigroup_iff :
    Semigroup.IsReverseDefinite L.SyntacticSemigroup ↔ ∃ k, L.IsReverseDefinite k :=
  ⟨fun h ↦ ⟨_, isReverseDefinite_natCard_of_isReverseDefinite_syntacticSemigroup h⟩,
    fun ⟨_, h⟩ ↦ h.isReverseDefinite_syntacticSemigroup⟩

theorem isLocallyTrivial_syntacticSemigroup_iff :
    Semigroup.IsLocallyTrivial L.SyntacticSemigroup ↔ ∃ k, L.IsGeneralizedDefinite k :=
  ⟨fun h ↦ ⟨_, isGeneralizedDefinite_natCard_of_isLocallyTrivial_syntacticSemigroup h⟩,
    fun ⟨_, h⟩ ↦ h.isLocallyTrivial_syntacticSemigroup⟩

/-- Over a finite alphabet, a language with a finite syntactic semigroup is finite or cofinite
exactly when its syntactic semigroup is both definite and reverse definite. -/
theorem isFiniteOrCofinite_iff_syntacticSemigroup [Finite α] :
    L.IsFiniteOrCofinite ↔ Semigroup.IsDefinite L.SyntacticSemigroup ∧
      Semigroup.IsReverseDefinite L.SyntacticSemigroup := by
  rw [isDefinite_syntacticSemigroup_iff, isReverseDefinite_syntacticSemigroup_iff,
    isFiniteOrCofinite_iff_exists_isDefinite_and_isReverseDefinite]

end Converse

/-! ### The Eilenberg correspondences -/

/-- A definite language over a finite alphabet lies in the language variety of **D**. -/
theorem IsDefinite.langs [Finite α] (h : L.IsDefinite k) : Semigroup.definiteVariety.langs L :=
  ⟨h.isRegular.finite_syntacticSemigroup, h.isDefinite_syntacticSemigroup⟩

/-- A reverse definite language over a finite alphabet lies in the language variety of **K**. -/
theorem IsReverseDefinite.langs [Finite α] (h : L.IsReverseDefinite k) :
    Semigroup.reverseDefiniteVariety.langs L :=
  ⟨h.isRegular.finite_syntacticSemigroup, h.isReverseDefinite_syntacticSemigroup⟩

/-- A generalized definite language over a finite alphabet lies in the language variety
of **LI**. -/
theorem IsGeneralizedDefinite.langs [Finite α] (h : L.IsGeneralizedDefinite k) :
    Semigroup.locallyTrivialVariety.langs L :=
  ⟨h.isRegular.finite_syntacticSemigroup, h.isLocallyTrivial_syntacticSemigroup⟩

/-- The language variety of **D** consists of the definite languages. -/
theorem langs_definiteVariety_iff [Finite α] :
    Semigroup.definiteVariety.langs L ↔ ∃ k, L.IsDefinite k :=
  ⟨fun h ↦ have := h.1; isDefinite_syntacticSemigroup_iff.1 h.2,
    fun ⟨_, h⟩ ↦ h.langs⟩

/-- The language variety of **K** consists of the reverse definite languages. -/
theorem langs_reverseDefiniteVariety_iff [Finite α] :
    Semigroup.reverseDefiniteVariety.langs L ↔ ∃ k, L.IsReverseDefinite k :=
  ⟨fun h ↦ have := h.1; isReverseDefinite_syntacticSemigroup_iff.1 h.2,
    fun ⟨_, h⟩ ↦ h.langs⟩

/-- The language variety of **LI** consists of the generalized definite languages. -/
theorem langs_locallyTrivialVariety_iff [Finite α] :
    Semigroup.locallyTrivialVariety.langs L ↔ ∃ k, L.IsGeneralizedDefinite k :=
  ⟨fun h ↦ have := h.1; isLocallyTrivial_syntacticSemigroup_iff.1 h.2,
    fun ⟨_, h⟩ ↦ h.langs⟩

end Language
