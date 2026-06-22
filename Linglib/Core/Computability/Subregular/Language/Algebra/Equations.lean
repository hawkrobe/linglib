/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Logic.Function.Basic
import Linglib.Core.Algebra.Group.Idempotent
import Linglib.Core.Computability.SyntacticMonoid
import Linglib.Core.Computability.Subregular.Language.Definite
import Linglib.Core.Data.List.DropRight

/-!
# Equational characterizations of the definite subregular classes

[lambert-2026] characterizes base classes of subregular languages by equations on
the syntactic semigroup. This file gives the finite-`k` forms for the **definite**
(`𝒟`), **reverse-definite** (`𝒦`), and **generalized definite** (`ℒℐ`) classes; the
classical ω-power forms in `Pin.lean` are derived from them.

## Main definitions

* `Language.kDefiniteEquation`, `Language.kReverseDefiniteEquation`,
  `Language.kGeneralizedDefiniteEquation` — for every syntactic-monoid element `s`
  and length-`k` word `αs`, prepending, appending, resp. sandwiching `s` around the
  class of `αs` fixes it (`s * [αs] = [αs]`, `[αs] * s = [αs]`, `[αs] * s * [αs] = [αs]`),
  where `[αs]` is `L.syntacticClass αs`.

## Main results

* `Language.isDefinite_iff_satisfies_kDefiniteEquation`,
  `Language.isReverseDefinite_iff_satisfies_kReverseDefiniteEquation`,
  `Language.isGeneralizedDefinite_iff_satisfies_kGeneralizedDefiniteEquation`
  ([lambert-2026]) — each class equals the languages whose
  syntactic monoid satisfies the corresponding equation.

## Implementation notes

The `xᵢ` range over length-`k` **letter sequences** (`αs : List α`), not arbitrary
monoid elements: the latter is strictly weaker, ignoring `L`-trivial letters (e.g.
`(a|b)*` over `{a, b, c}` would spuriously qualify). [lambert-2026] works in the
syntactic *semigroup* (no empty word); we keep mathlib's `Con (FreeMonoid α)` monoid
and recover the characterization through this letter-sequence quantification.
-/

open Subregular

namespace Language

variable {α : Type*} (L : Language α) (k : ℕ)

/-! ### The equations -/

/-- The definite (`𝒟`) equation: every length-`k` word's class is a right zero
(`∀ s, s * [αs] = [αs]`). -/
def kDefiniteEquation : Prop :=
  ∀ αs : List α, αs.length = k → IsRightZero (L.syntacticClass αs)

/-- The reverse-definite (`𝒦`) equation: every length-`k` word's class is a left zero
(`∀ s, [αs] * s = [αs]`). -/
def kReverseDefiniteEquation : Prop :=
  ∀ αs : List α, αs.length = k → IsLeftZero (L.syntacticClass αs)

/-- The generalized-definite (`ℒℐ`) equation: `[αs] * s * [αs] = [αs]` (`|αs| = k`). -/
def kGeneralizedDefiniteEquation : Prop :=
  ∀ (s : L.syntacticMonoid) (αs : List α), αs.length = k →
    L.syntacticClass αs * s * L.syntacticClass αs = L.syntacticClass αs

variable {L} {k}

/-! ### Definite (`𝒟`) -/

/-- Under the `𝒟` equation, prepending any prefix to a length-`k` word fixes its class. -/
private lemma syntacticClass_of_kDefiniteEquation
    (h : kDefiniteEquation L k) (w αs : List α) (hαs_len : αs.length = k) :
    L.syntacticClass (w ++ αs) = L.syntacticClass αs := by
  rw [syntacticClass_append]; exact h αs hαs_len (L.syntacticClass w)

/-- Forward: a `k`-definite language satisfies the `𝒟` equation. -/
theorem IsDefinite.satisfies_kDefiniteEquation (hL : L.IsDefinite k) :
    kDefiniteEquation L k := by
  intro αs hαs_len s
  obtain ⟨w, rfl⟩ := L.syntacticClass_surjective s
  rw [← syntacticClass_append, syntacticClass_eq_iff]
  intro x y
  refine iff_of_eq (hL ?_)
  have h : k ≤ (αs ++ y).length := by rw [List.length_append]; omega
  rw [show x ++ (w ++ αs) ++ y = (x ++ w) ++ (αs ++ y) by simp [List.append_assoc],
      show x ++ αs ++ y = x ++ (αs ++ y) by simp [List.append_assoc],
      Edge.takeAt_right_append_of_le_length _ _ h, Edge.takeAt_right_append_of_le_length _ _ h]

/-- Under the `𝒟` equation a word and its length-`k` suffix share a syntactic class
("the class is memoryless past the `k`-suffix") — the pivot for the reverse direction. -/
private lemma syntacticClass_eq_takeAt (h : kDefiniteEquation L k) (w : List α) :
    L.syntacticClass w = L.syntacticClass (Edge.right.takeAt k w) := by
  by_cases hw : w.length ≤ k
  · rw [Edge.takeAt_of_length_le _ hw]
  · have hlen : (Edge.right.takeAt k w).length = k := by rw [Edge.length_takeAt]; omega
    have base := syntacticClass_of_kDefiniteEquation h
      (w.take (w.length - k)) (Edge.right.takeAt k w) hlen
    have decomp : w = w.take (w.length - k) ++ Edge.right.takeAt k w :=
      (List.rdrop_append_rtake w k).symm
    rwa [← decomp] at base

/-- Reverse: the `𝒟` equation forces `k`-definiteness. -/
theorem isDefinite_of_satisfies_kDefiniteEquation (h : kDefiniteEquation L k) :
    L.IsDefinite k :=
  isDefinite_iff_mem_takeAt.mpr fun w =>
    mem_iff_of_syntacticClass_eq (syntacticClass_eq_takeAt h w)

/-- `k`-definite ↔ the `𝒟` equation. -/
theorem isDefinite_iff_satisfies_kDefiniteEquation :
    L.IsDefinite k ↔ kDefiniteEquation L k :=
  ⟨IsDefinite.satisfies_kDefiniteEquation, isDefinite_of_satisfies_kDefiniteEquation⟩

/-! ### Reverse-definite (`𝒦`) — by reverse duality -/

/-- Reverse duality, element form: a class is a right zero in `L.reverse` iff the
reversed-word class is a left zero in `L`. -/
private lemma isRightZero_reverse_syntacticClass {αs : List α} :
    IsRightZero (L.reverse.syntacticClass αs) ↔ IsLeftZero (L.syntacticClass αs.reverse) := by
  constructor
  · intro h a
    obtain ⟨v, rfl⟩ := L.syntacticClass_surjective a
    rw [← syntacticClass_append]
    have hb := h (L.reverse.syntacticClass v.reverse)
    rw [← syntacticClass_append, syntacticClass_reverse_eq_iff, List.reverse_append,
      List.reverse_reverse] at hb
    exact hb
  · intro h a
    obtain ⟨v, rfl⟩ := L.reverse.syntacticClass_surjective a
    rw [← syntacticClass_append, syntacticClass_reverse_eq_iff, List.reverse_append]
    have hb := h (L.syntacticClass v.reverse)
    rw [← syntacticClass_append] at hb
    exact hb

/-- The `𝒦` equation for `L` is the `𝒟` equation for `L.reverse`. -/
theorem kReverseDefiniteEquation_iff_reverse :
    kReverseDefiniteEquation L k ↔ kDefiniteEquation L.reverse k := by
  refine ⟨fun h αs hlen => ?_, fun h αs hlen => ?_⟩
  · rw [isRightZero_reverse_syntacticClass]; exact h αs.reverse (by simpa using hlen)
  · have := h αs.reverse (by simpa using hlen)
    rw [isRightZero_reverse_syntacticClass, List.reverse_reverse] at this; exact this

/-- reverse-`k`-definite ↔ the `𝒦` equation (reverse duality with `𝒟`). -/
theorem isReverseDefinite_iff_satisfies_kReverseDefiniteEquation :
    L.IsReverseDefinite k ↔ kReverseDefiniteEquation L k := by
  rw [isReverseDefinite_iff_isDefinite_reverse, isDefinite_iff_satisfies_kDefiniteEquation,
    kReverseDefiniteEquation_iff_reverse]

/-- Forward: a reverse-`k`-definite language satisfies the `𝒦` equation. -/
theorem IsReverseDefinite.satisfies_kReverseDefiniteEquation (hL : L.IsReverseDefinite k) :
    kReverseDefiniteEquation L k :=
  isReverseDefinite_iff_satisfies_kReverseDefiniteEquation.mp hL

/-- Reverse: the `𝒦` equation forces reverse-`k`-definiteness. -/
theorem isReverseDefinite_of_satisfies_kReverseDefiniteEquation
    (h : kReverseDefiniteEquation L k) : L.IsReverseDefinite k :=
  isReverseDefinite_iff_satisfies_kReverseDefiniteEquation.mpr h

/-! ### Generalized definite (`ℒℐ`) -/

/-! #### Lifting the LI equation to a syntactic-class equality -/

/-- Under the `ℒℐ` equation, sandwiching a word inside a length-`k` word fixes its class. -/
lemma syntacticClass_of_kGeneralizedDefiniteEquation
    (h : Language.kGeneralizedDefiniteEquation L k)
    (αs w : List α) (hαs_len : αs.length = k) :
    L.syntacticClass (αs ++ w ++ αs) = L.syntacticClass αs := by
  rw [syntacticClass_append, syntacticClass_append]
  exact h (L.syntacticClass w) αs hαs_len

/-! #### Forward direction -/

/-- Forward: a generalized-`k`-definite language satisfies the `ℒℐ` equation. -/
theorem IsGeneralizedDefinite.satisfies_kGeneralizedDefiniteEquation
    (hL : L.IsGeneralizedDefinite k) :
    Language.kGeneralizedDefiniteEquation L k := by
  intro s αs hαs_len
  obtain ⟨w, rfl⟩ := L.syntacticClass_surjective s
  rw [← syntacticClass_append, ← syntacticClass_append, syntacticClass_eq_iff]
  intro x y
  apply isGeneralizedDefinite_iff_edges.mp hL
  · -- takeAt_left k matches: both have x ++ αs as prefix.
    show (x ++ (αs ++ w ++ αs) ++ y).take k = (x ++ αs ++ y).take k
    rw [show x ++ (αs ++ w ++ αs) ++ y = (x ++ αs) ++ (w ++ αs ++ y) by
          simp [List.append_assoc],
        show x ++ αs ++ y = (x ++ αs) ++ y by simp [List.append_assoc]]
    have h_xαs_len : k ≤ (x ++ αs).length := by rw [List.length_append]; omega
    rw [List.take_append_of_le_length h_xαs_len, List.take_append_of_le_length h_xαs_len]
  · -- takeAt_right k matches: both end with αs ++ y.
    show Edge.right.takeAt k (x ++ (αs ++ w ++ αs) ++ y) =
         Edge.right.takeAt k (x ++ αs ++ y)
    rw [show x ++ (αs ++ w ++ αs) ++ y = (x ++ αs ++ w) ++ (αs ++ y) by
          simp [List.append_assoc],
        show x ++ αs ++ y = x ++ (αs ++ y) by simp [List.append_assoc]]
    have h_αsy_len : k ≤ (αs ++ y).length := by rw [List.length_append]; omega
    rw [Edge.takeAt_right_append_of_le_length (x ++ αs ++ w) (αs ++ y) h_αsy_len,
        Edge.takeAt_right_append_of_le_length x (αs ++ y) h_αsy_len]

/-! #### Reverse direction -/

/-- Reverse: the `ℒℐ` equation forces generalized-`k`-definiteness. -/
theorem isGeneralizedDefinite_of_satisfies_kGeneralizedDefiniteEquation
    (h : Language.kGeneralizedDefiniteEquation L k) :
    L.IsGeneralizedDefinite k := by
  refine isGeneralizedDefinite_iff_edges.mpr ?_
  intro w₁ w₂ hpre hsuf
  by_cases hw₁_long : k ≤ w₁.length
  · -- Both `|wᵢ| ≥ k`: the matching length-`k` prefix forces `|w₂| ≥ k` too,
    -- since otherwise `Edge.left.takeAt k w₂` would be shorter than `k`.
    have h_pre_len_w₁ : (Edge.left.takeAt k w₁).length = k := by
      rw [Edge.length_takeAt]; omega
    have hw₂_long : k ≤ w₂.length := by
      have h_pre_len_w₂ : (Edge.left.takeAt k w₂).length = k := by
        rw [← hpre]; exact h_pre_len_w₁
      rw [Edge.length_takeAt] at h_pre_len_w₂; omega
    -- Set up αs, βs, b_i, c_i and the two decompositions of each wᵢ.
    set αs := Edge.left.takeAt k w₁
    set βs := Edge.right.takeAt k w₁
    have hαs_len : αs.length = k := h_pre_len_w₁
    have hβs_len : βs.length = k := by
      show (w₁.drop (w₁.length - k)).length = k
      rw [List.length_drop]; omega
    set b₁ := w₁.drop k
    set b₂ := w₂.drop k
    set c₁ := w₁.take (w₁.length - k)
    set c₂ := w₂.take (w₂.length - k)
    -- αs-decompositions: wᵢ = αs ++ bᵢ.
    have hw₁_αs : w₁ = αs ++ b₁ := by
      show w₁ = w₁.take k ++ w₁.drop k
      exact (List.take_append_drop _ _).symm
    have hw₂_αs : w₂ = αs ++ b₂ := by
      have : Edge.left.takeAt k w₂ = αs := hpre.symm
      have h_w₂_take : w₂.take k = αs := this
      show w₂ = αs ++ w₂.drop k
      rw [← h_w₂_take]; exact (List.take_append_drop _ _).symm
    -- βs-decompositions: wᵢ = cᵢ ++ βs.
    have hw₁_βs : w₁ = c₁ ++ βs := by
      show w₁ = w₁.take (w₁.length - k) ++ w₁.drop (w₁.length - k)
      exact (List.take_append_drop _ _).symm
    have hw₂_βs : w₂ = c₂ ++ βs := by
      have : Edge.right.takeAt k w₂ = βs := hsuf.symm
      have h_w₂_drop : w₂.drop (w₂.length - k) = βs := this
      show w₂ = w₂.take (w₂.length - k) ++ βs
      rw [← h_w₂_drop]; exact (List.take_append_drop _ _).symm
    -- Way 1: αs-sandwich gives `[w₁ ++ w₂] = [w₂]`, by absorbing
    -- the `αs ++ b₁ ++ αs` block into `αs`.
    have h_αs_eq : L.syntacticClass (w₁ ++ w₂) = L.syntacticClass w₂ := by
      conv_lhs => rw [hw₁_αs, hw₂_αs,
        show (αs ++ b₁) ++ (αs ++ b₂) = (αs ++ b₁ ++ αs) ++ b₂ by
          simp [List.append_assoc]]
      rw [syntacticClass_append, syntacticClass_of_kGeneralizedDefiniteEquation h αs b₁ hαs_len,
        ← syntacticClass_append, ← hw₂_αs]
    -- Way 2: βs-sandwich gives `[w₁ ++ w₂] = [w₁]`, by absorbing
    -- the `βs ++ c₂ ++ βs` block into `βs`.
    have h_βs_eq : L.syntacticClass (w₁ ++ w₂) = L.syntacticClass w₁ := by
      conv_lhs => rw [hw₁_βs, hw₂_βs,
        show (c₁ ++ βs) ++ (c₂ ++ βs) = c₁ ++ (βs ++ c₂ ++ βs) by
          simp [List.append_assoc]]
      rw [syntacticClass_append, syntacticClass_of_kGeneralizedDefiniteEquation h βs c₂ hβs_len,
        ← syntacticClass_append, ← hw₁_βs]
    -- Combine: `[w₁] = [w₂]`, hence `w₁ ≡_L w₂`.
    exact mem_iff_of_syntacticClass_eq (h_βs_eq.symm.trans h_αs_eq)
  · -- Short case: `|w₁| < k`. Then `Edge.left.takeAt k w₁ = w₁`, so
    -- the prefix equality yields `w₁ = Edge.left.takeAt k w₂`, which
    -- forces `|w₂| ≤ k` (otherwise the takeAt has length `k > |w₁|`).
    push Not at hw₁_long
    have h_w₁_pre : Edge.left.takeAt k w₁ = w₁ :=
      Edge.takeAt_of_length_le _ (le_of_lt hw₁_long)
    rw [h_w₁_pre] at hpre
    -- Now hpre : w₁ = Edge.left.takeAt k w₂.
    by_cases hw₂_long : k ≤ w₂.length
    · -- Length-`k` takeAt of `w₂` has length `k > |w₁|`. Contradicts hpre.
      have h_pre_len : (Edge.left.takeAt k w₂).length = k := by
        rw [Edge.length_takeAt]; omega
      rw [← hpre] at h_pre_len
      omega
    · push Not at hw₂_long
      have h_w₂_pre : Edge.left.takeAt k w₂ = w₂ :=
        Edge.takeAt_of_length_le _ (le_of_lt hw₂_long)
      rw [h_w₂_pre] at hpre
      rw [hpre]

/-- generalized-`k`-definite ↔ the `ℒℐ` equation. -/
theorem isGeneralizedDefinite_iff_satisfies_kGeneralizedDefiniteEquation :
    L.IsGeneralizedDefinite k ↔
    Language.kGeneralizedDefiniteEquation L k :=
  ⟨IsGeneralizedDefinite.satisfies_kGeneralizedDefiniteEquation,
   isGeneralizedDefinite_of_satisfies_kGeneralizedDefiniteEquation⟩

end Language
