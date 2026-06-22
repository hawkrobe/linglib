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

/-- A class is a **right zero** iff prepending any word fixes it. -/
private lemma isRightZero_syntacticClass_iff {αs : List α} :
    IsRightZero (L.syntacticClass αs) ↔ ∀ v, L.syntacticClass (v ++ αs) = L.syntacticClass αs := by
  refine ⟨fun h v => by rw [syntacticClass_append]; exact h _, fun h a => ?_⟩
  obtain ⟨v, rfl⟩ := L.syntacticClass_surjective a; rw [← syntacticClass_append]; exact h v

/-- A class is a **left zero** iff appending any word fixes it. -/
private lemma isLeftZero_syntacticClass_iff {αs : List α} :
    IsLeftZero (L.syntacticClass αs) ↔ ∀ v, L.syntacticClass (αs ++ v) = L.syntacticClass αs := by
  refine ⟨fun h v => by rw [syntacticClass_append]; exact h _, fun h a => ?_⟩
  obtain ⟨v, rfl⟩ := L.syntacticClass_surjective a; rw [← syntacticClass_append]; exact h v

/-- Reverse duality, element form: a class is a right zero in `L.reverse` iff the
reversed-word class is a left zero in `L` (reindex the absorbed word by `reverse`). -/
private lemma isRightZero_reverse_syntacticClass {αs : List α} :
    IsRightZero (L.reverse.syntacticClass αs) ↔ IsLeftZero (L.syntacticClass αs.reverse) := by
  rw [isRightZero_syntacticClass_iff, isLeftZero_syntacticClass_iff]
  simp only [syntacticClass_reverse_eq_iff, List.reverse_append]
  exact ⟨fun h v => by simpa using h v.reverse, fun h v => by simpa using h v.reverse⟩

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

/-- Under the `ℒℐ` equation, sandwiching a word inside a length-`k` word fixes its class. -/
private lemma syntacticClass_of_kGeneralizedDefiniteEquation
    (h : kGeneralizedDefiniteEquation L k)
    (αs w : List α) (hαs_len : αs.length = k) :
    L.syntacticClass (αs ++ w ++ αs) = L.syntacticClass αs := by
  rw [syntacticClass_append, syntacticClass_append]
  exact h (L.syntacticClass w) αs hαs_len

/-- Forward: a generalized-`k`-definite language satisfies the `ℒℐ` equation. -/
theorem IsGeneralizedDefinite.satisfies_kGeneralizedDefiniteEquation
    (hL : L.IsGeneralizedDefinite k) :
    kGeneralizedDefiniteEquation L k := by
  intro s αs hαs_len
  obtain ⟨w, rfl⟩ := L.syntacticClass_surjective s
  rw [← syntacticClass_append, ← syntacticClass_append, syntacticClass_eq_iff]
  intro x y
  apply isGeneralizedDefinite_iff_edges.mp hL
  · -- left edge: both have `x ++ αs` as length-`k` prefix.
    have hp : k ≤ (x ++ αs).length := by rw [List.length_append]; omega
    rw [show x ++ (αs ++ w ++ αs) ++ y = (x ++ αs) ++ (w ++ αs ++ y) by simp [List.append_assoc],
        show x ++ αs ++ y = (x ++ αs) ++ y by simp [List.append_assoc],
        Edge.takeAt_left_append_of_le_length _ _ hp, Edge.takeAt_left_append_of_le_length _ _ hp]
  · -- right edge: both end with `αs ++ y` as length-`k` suffix.
    have hs : k ≤ (αs ++ y).length := by rw [List.length_append]; omega
    rw [show x ++ (αs ++ w ++ αs) ++ y = (x ++ αs ++ w) ++ (αs ++ y) by simp [List.append_assoc],
        show x ++ αs ++ y = x ++ (αs ++ y) by simp [List.append_assoc],
        Edge.takeAt_right_append_of_le_length _ _ hs, Edge.takeAt_right_append_of_le_length _ _ hs]

/-- Reverse: the `ℒℐ` equation forces generalized-`k`-definiteness. -/
theorem isGeneralizedDefinite_of_satisfies_kGeneralizedDefiniteEquation
    (h : kGeneralizedDefiniteEquation L k) :
    L.IsGeneralizedDefinite k := by
  refine isGeneralizedDefinite_iff_edges.mpr ?_
  intro w₁ w₂ hpre hsuf
  by_cases hw₁_long : k ≤ w₁.length
  · -- Both `|wᵢ| ≥ k`: the matching length-`k` prefix forces `|w₂| ≥ k` too.
    have hαs_len : (Edge.left.takeAt k w₁).length = k := by rw [Edge.length_takeAt]; omega
    have hw₂_long : k ≤ w₂.length := by
      have := hαs_len; rw [hpre, Edge.length_takeAt] at this; omega
    set αs := Edge.left.takeAt k w₁
    set βs := Edge.right.takeAt k w₁
    have hβs_len : βs.length = k := by
      show (w₁.drop (w₁.length - k)).length = k; rw [List.length_drop]; omega
    set b₁ := w₁.drop k; set b₂ := w₂.drop k
    set c₁ := w₁.take (w₁.length - k); set c₂ := w₂.take (w₂.length - k)
    -- `wᵢ = αs ++ bᵢ` (shared prefix) and `wᵢ = cᵢ ++ βs` (shared suffix).
    have hw₁_αs : w₁ = αs ++ b₁ := (List.take_append_drop k w₁).symm
    have hw₂_αs : w₂ = αs ++ b₂ := by rw [hpre]; exact (List.take_append_drop k w₂).symm
    have hw₁_βs : w₁ = c₁ ++ βs := (List.take_append_drop (w₁.length - k) w₁).symm
    have hw₂_βs : w₂ = c₂ ++ βs := by rw [hsuf]; exact (List.take_append_drop (w₂.length - k) w₂).symm
    -- Way 1: the αs-sandwich absorbs into `w₂`; Way 2: the βs-sandwich absorbs into `w₁`.
    have h_αs_eq : L.syntacticClass (w₁ ++ w₂) = L.syntacticClass w₂ := by
      conv_lhs => rw [hw₁_αs, hw₂_αs,
        show (αs ++ b₁) ++ (αs ++ b₂) = (αs ++ b₁ ++ αs) ++ b₂ by simp [List.append_assoc]]
      rw [syntacticClass_append, syntacticClass_of_kGeneralizedDefiniteEquation h αs b₁ hαs_len,
        ← syntacticClass_append, ← hw₂_αs]
    have h_βs_eq : L.syntacticClass (w₁ ++ w₂) = L.syntacticClass w₁ := by
      conv_lhs => rw [hw₁_βs, hw₂_βs,
        show (c₁ ++ βs) ++ (c₂ ++ βs) = c₁ ++ (βs ++ c₂ ++ βs) by simp [List.append_assoc]]
      rw [syntacticClass_append, syntacticClass_of_kGeneralizedDefiniteEquation h βs c₂ hβs_len,
        ← syntacticClass_append, ← hw₁_βs]
    exact mem_iff_of_syntacticClass_eq (h_βs_eq.symm.trans h_αs_eq)
  · -- Short case `|w₁| < k`: the prefix match collapses to `w₁ = w₂`.
    rw [Edge.takeAt_of_length_le _ (not_le.mp hw₁_long).le] at hpre
    by_cases hw₂_long : k ≤ w₂.length
    · have hlen : (Edge.left.takeAt k w₂).length = k := by rw [Edge.length_takeAt]; omega
      rw [← hpre] at hlen; omega
    · rw [Edge.takeAt_of_length_le _ (not_le.mp hw₂_long).le] at hpre; rw [hpre]

/-- generalized-`k`-definite ↔ the `ℒℐ` equation. -/
theorem isGeneralizedDefinite_iff_satisfies_kGeneralizedDefiniteEquation :
    L.IsGeneralizedDefinite k ↔ kGeneralizedDefiniteEquation L k :=
  ⟨IsGeneralizedDefinite.satisfies_kGeneralizedDefiniteEquation,
   isGeneralizedDefinite_of_satisfies_kGeneralizedDefiniteEquation⟩

end Language
