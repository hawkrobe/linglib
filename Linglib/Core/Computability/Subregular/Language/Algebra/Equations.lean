/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Logic.Function.Basic
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
  where `[αs]` is `L.toSyntacticMonoid (FreeMonoid.ofList αs)`.

## Main results

* `Language.isDefinite_iff_satisfies_kDefiniteEquation`,
  `Language.isReverseDefinite_iff_satisfies_kReverseDefiniteEquation`,
  `Language.isGeneralizedDefinite_iff_satisfies_kGeneralizedDefiniteEquation`
  ([lambert-2026], Props 53, 57, 58) — each class equals the languages whose
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

variable {α : Type*}

/-- **Lambert Prop 53 equation** (`𝒟`): `s * [αs] = [αs]` for any length-`k` word `αs`. -/
def kDefiniteEquation (L : Language α) (k : ℕ) : Prop :=
  ∀ (s : L.syntacticMonoid) (αs : List α), αs.length = k →
    s * L.syntacticClass αs = L.syntacticClass αs

/-- A membership predicate `(· ∈ L)` factors through `f` as soon as `f`
preserves membership pointwise. The shared reverse-direction engine for the
`Is*Definite` characterizations, which each reduce to a per-word
`w ∈ L ↔ edge w ∈ L`. -/
private lemma factorsThrough_of_mem_iff {L : Language α} {f : List α → List α}
    (key : ∀ w, w ∈ L ↔ f w ∈ L) : Function.FactorsThrough (· ∈ L) f :=
  fun a b hab => by simp only [key a, key b, hab]

/-! ### Helper lemmas on `Edge.right.takeAt` -/

/-- The right-`k`-suffix of `x ++ rest` equals the right-`k`-suffix of `rest`
whenever `rest.length ≥ k` — the `Edge.takeAt` view of
`List.rtake_append_of_le_length`. -/
lemma takeAt_right_append_left_absorb {α : Type*}
    (x rest : List α) {k : ℕ} (h : k ≤ rest.length) :
    Edge.right.takeAt k (x ++ rest) = Edge.right.takeAt k rest :=
  List.rtake_append_of_le_length x rest h

/-! ### Lifting the equation to a syntactic-class equality -/

/-- Under the `k`-definite equation, prepending any prefix to a length-`k` word
preserves its syntactic class — the algebraic heart of the reverse direction. -/
lemma syntacticClass_of_kDefiniteEquation {L : Language α} {k : ℕ}
    (h : Language.kDefiniteEquation L k)
    (w αs : List α) (hαs_len : αs.length = k) :
    L.syntacticClass (w ++ αs) = L.syntacticClass αs := by
  rw [syntacticClass_append]
  exact h (L.syntacticClass w) αs hαs_len

/-! ### Lambert Prop 53 — both directions -/

/-- **Lambert Prop 53 (forward direction)**: a `k`-definite language's
syntactic monoid satisfies the `k`-definite equation: prepending any
syntactic-monoid element `s` to a length-`k` letter sequence `αs`
preserves the syntactic class of `αs`. -/
theorem IsDefinite.satisfies_kDefiniteEquation
    {L : Language α} {k : ℕ} (hL : L.IsDefinite k) :
    Language.kDefiniteEquation L k := by
  intro s αs hαs_len
  obtain ⟨w, rfl⟩ := L.syntacticClass_surjective s
  rw [← syntacticClass_append, syntacticClass_eq_iff]
  intro x y
  refine iff_of_eq (hL ?_)
  rw [show x ++ (w ++ αs) ++ y = (x ++ w) ++ (αs ++ y) by simp [List.append_assoc],
      show x ++ αs ++ y = x ++ (αs ++ y) by simp [List.append_assoc]]
  have h_combined_len : k ≤ (αs ++ y).length := by rw [List.length_append]; omega
  rw [takeAt_right_append_left_absorb (x ++ w) (αs ++ y) h_combined_len,
      takeAt_right_append_left_absorb x (αs ++ y) h_combined_len]

/-- **Lambert Prop 53 (reverse direction)**: if a language's syntactic
monoid satisfies the `k`-definite equation, then the language is
`k`-definite.

Construction: `G.permitted := {Edge.right.takeAt k w | w ∈ L}`. The
trivial direction `L ⊆ G.lang` holds with witness `w' = w`. The
interesting direction `G.lang ⊆ L`: if `w ∈ G.lang`, there is some
`u ∈ L` with the same length-`k` right-suffix; case-split on
`u.length`, `w.length` vs `k`:

1. Both `u.length ≤ k`, `w.length ≤ k`: their `takeAt k`-suffixes are
   `u`, `w` themselves; equality forces `w = u ∈ L`.
2. `u.length ≤ k`, `w.length > k`: the suffix-length match forces
   `u.length = k`, so `u` is the length-`k` right-suffix of `w`. Apply
   the equation to get `[w] = [u]` in the syntactic monoid; saturation
   closes.
3. `u.length > k`, `w.length ≤ k`: symmetric to (2).
4. Both `u.length > k`, `w.length > k`: both decompose as
   `prefix ++ ks` for the shared length-`k` suffix `ks`. Apply
   equation to both, getting `[w] = [ks]` and `[u] = [ks]`; chain by
   transitivity, then saturation. -/
theorem isDefinite_of_satisfies_kDefiniteEquation
    {L : Language α} {k : ℕ}
    (h : Language.kDefiniteEquation L k) :
    L.IsDefinite k := by
  -- Membership equals membership of the length-`k` suffix: short words are their
  -- own suffix; long words are syntactically equivalent to it via the equation.
  have key : ∀ w : List α, w ∈ L ↔ Edge.right.takeAt k w ∈ L := by
    intro w
    by_cases hw : w.length ≤ k
    · rw [Edge.takeAt_of_length_le _ hw]
    · push Not at hw
      have hlen : (Edge.right.takeAt k w).length = k := by
        rw [Edge.length_takeAt]; omega
      have hcon : L.syntacticClass w = L.syntacticClass (Edge.right.takeAt k w) := by
        have base := syntacticClass_of_kDefiniteEquation h
          (w.take (w.length - k)) (Edge.right.takeAt k w) hlen
        have decomp : w = w.take (w.length - k) ++ Edge.right.takeAt k w :=
          (List.rdrop_append_rtake w k).symm
        rwa [← decomp] at base
      exact mem_iff_of_syntacticClass_eq hcon
  exact factorsThrough_of_mem_iff key

/-- **Lambert (2026) Prop 53**: a language is `k`-definite iff its
syntactic monoid satisfies the `k`-definite equation. Bidirectional
bundling of `IsDefinite.satisfies_kDefiniteEquation` and
`isDefinite_of_satisfies_kDefiniteEquation`. -/
theorem isDefinite_iff_satisfies_kDefiniteEquation
    {L : Language α} {k : ℕ} :
    L.IsDefinite k ↔ Language.kDefiniteEquation L k :=
  ⟨IsDefinite.satisfies_kDefiniteEquation,
   isDefinite_of_satisfies_kDefiniteEquation⟩

/-! ### Lambert Prop 57 — reverse-definite (mirror of D) -/

/-- **Lambert (2026) Prop 57 equation** for **reverse-definite**
languages (length-`k` letter-sequence, monoid form): for any element
`s` of the syntactic monoid and any length-`k` letter sequence `αs`,
**post**-multiplying `[αs]` by `s` preserves it. Mirror of
`kDefiniteEquation` with right-multiplication instead of left.

Lambert's notation: `𝒦_k = ⟦x₁ ⋯ xₖ s = x₁ ⋯ xₖ⟧` (paper Prop 57). -/
def kReverseDefiniteEquation (L : Language α) (k : ℕ) : Prop :=
  ∀ (s : L.syntacticMonoid) (αs : List α), αs.length = k →
    L.syntacticClass αs * s = L.syntacticClass αs

/-! #### Helper lemmas on `Edge.left.takeAt` (mirror of `Edge.right`) -/

/-- The left-`k`-prefix of `xs ++ y` equals the left-`k`-prefix of
`xs` whenever `xs.length ≥ k`. -/
private lemma takeAt_left_append_right_absorb {α : Type*}
    (xs y : List α) {k : ℕ} (h : k ≤ xs.length) :
    Edge.left.takeAt k (xs ++ y) = Edge.left.takeAt k xs := by
  show (xs ++ y).take k = xs.take k
  exact List.take_append_of_le_length h

/-! #### Lifting the K equation to a syntactic-class equality -/

/-- Under the reverse-`k`-definite equation, **appending** any suffix to a length-`k`
word preserves its syntactic class. Mirror of `syntacticClass_of_kDefiniteEquation`. -/
lemma syntacticClass_of_kReverseDefiniteEquation {L : Language α} {k : ℕ}
    (h : Language.kReverseDefiniteEquation L k)
    (αs w : List α) (hαs_len : αs.length = k) :
    L.syntacticClass (αs ++ w) = L.syntacticClass αs := by
  rw [syntacticClass_append]
  exact h (L.syntacticClass w) αs hαs_len

/-! #### Lambert Prop 57 — both directions -/

/-- **Lambert Prop 57 (forward direction)**: a reverse-`k`-definite
language's syntactic monoid satisfies the reverse-`k`-definite equation. -/
theorem IsReverseDefinite.satisfies_kReverseDefiniteEquation
    {L : Language α} {k : ℕ} (hL : L.IsReverseDefinite k) :
    Language.kReverseDefiniteEquation L k := by
  intro s αs hαs_len
  obtain ⟨w, rfl⟩ := L.syntacticClass_surjective s
  rw [← syntacticClass_append, syntacticClass_eq_iff]
  intro x y
  refine iff_of_eq (hL ?_)
  rw [show x ++ (αs ++ w) ++ y = (x ++ αs) ++ (w ++ y) by simp [List.append_assoc],
      show x ++ αs ++ y = (x ++ αs) ++ y by simp [List.append_assoc]]
  have h_combined_len : k ≤ (x ++ αs).length := by rw [List.length_append]; omega
  rw [takeAt_left_append_right_absorb (x ++ αs) (w ++ y) h_combined_len,
      takeAt_left_append_right_absorb (x ++ αs) y h_combined_len]

/-- **Lambert Prop 57 (reverse direction)**: if a language's syntactic
monoid satisfies the reverse-`k`-definite equation, then the language is
reverse-`k`-definite. Mirror of `isDefinite_of_satisfies_kDefiniteEquation`. -/
theorem isReverseDefinite_of_satisfies_kReverseDefiniteEquation
    {L : Language α} {k : ℕ}
    (h : Language.kReverseDefiniteEquation L k) :
    L.IsReverseDefinite k := by
  have key : ∀ w : List α, w ∈ L ↔ Edge.left.takeAt k w ∈ L := by
    intro w
    by_cases hw : w.length ≤ k
    · rw [Edge.takeAt_of_length_le _ hw]
    · push Not at hw
      have hlen : (Edge.left.takeAt k w).length = k := by
        rw [Edge.length_takeAt]; omega
      have hcon : L.syntacticClass w = L.syntacticClass (Edge.left.takeAt k w) := by
        have base := syntacticClass_of_kReverseDefiniteEquation h
          (Edge.left.takeAt k w) (w.drop k) hlen
        have decomp : w = Edge.left.takeAt k w ++ w.drop k :=
          (List.take_append_drop k w).symm
        rwa [← decomp] at base
      exact mem_iff_of_syntacticClass_eq hcon
  exact factorsThrough_of_mem_iff key

/-- **Lambert (2026) Prop 57**: a language is reverse-`k`-definite iff
its syntactic monoid satisfies the reverse-`k`-definite equation. -/
theorem isReverseDefinite_iff_satisfies_kReverseDefiniteEquation
    {L : Language α} {k : ℕ} :
    L.IsReverseDefinite k ↔ Language.kReverseDefiniteEquation L k :=
  ⟨IsReverseDefinite.satisfies_kReverseDefiniteEquation,
   isReverseDefinite_of_satisfies_kReverseDefiniteEquation⟩

/-! ### Lambert Prop 58 — generalized definite (sandwich form) -/

/-- **Lambert (2026) Prop 58 equation** for **generalized `k`-definite**
languages (length-`k` letter-sequence, sandwich monoid form): for any
`s` and any length-`k` letter sequence `αs`, sandwiching `s` between
two copies of `[αs]` absorbs `s`:
`[αs] · s · [αs] = [αs]`.

Lambert's notation: `ℒℐ_k = ⟦x₁ ⋯ xₖ s x₁ ⋯ xₖ = x₁ ⋯ xₖ⟧`
([lambert-2026] Prop 58; [straubing-1985]). The two `αs`
instances are bound to the **same** letter sequence; this is the
"simplified" form of the more general two-variable equation
`[αs · s · βs] = [αs · βs]` that [lambert-2026] remarks defines
the same class. -/
def kGeneralizedDefiniteEquation (L : Language α) (k : ℕ) : Prop :=
  ∀ (s : L.syntacticMonoid) (αs : List α), αs.length = k →
    L.syntacticClass αs * s * L.syntacticClass αs = L.syntacticClass αs


/-! #### Lifting the LI equation to a syntactic-class equality -/

/-- Under the LI equation, sandwiching any word `w` between two copies of a length-`k`
word `αs` preserves the syntactic class of `αs`. -/
lemma syntacticClass_of_kGeneralizedDefiniteEquation
    {L : Language α} {k : ℕ}
    (h : Language.kGeneralizedDefiniteEquation L k)
    (αs w : List α) (hαs_len : αs.length = k) :
    L.syntacticClass (αs ++ w ++ αs) = L.syntacticClass αs := by
  rw [syntacticClass_append, syntacticClass_append]
  exact h (L.syntacticClass w) αs hαs_len

/-! #### Lambert Prop 58 — forward direction -/

/-- **Lambert Prop 58 (forward direction)**: a generalized-`k`-definite
language's syntactic monoid satisfies the LI equation.

Proof: apply `IsGeneralizedDefinite` to the pair
`(x ++ αs ++ s ++ αs ++ y, x ++ αs ++ y)`. They share the
length-`k` left-prefix (both have `x ++ αs` as prefix) and the
length-`k` right-suffix (both have `αs ++ y` as suffix). -/
theorem IsGeneralizedDefinite.satisfies_kGeneralizedDefiniteEquation
    {L : Language α} {k : ℕ} (hL : L.IsGeneralizedDefinite k) :
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
    rw [takeAt_right_append_left_absorb (x ++ αs ++ w) (αs ++ y) h_αsy_len,
        takeAt_right_append_left_absorb x (αs ++ y) h_αsy_len]

/-! #### Lambert Prop 58 — reverse direction -/

/-- **Lambert Prop 58 (reverse direction)**: if a language's syntactic
monoid satisfies the LI equation, then `L` is generalized `k`-definite.

**Strategy** (double-sandwich on `[w₁ · w₂]`): for `w₁`, `w₂` of length
`≥ k` with shared length-`k` prefix `αs` and length-`k` suffix `βs`,
both decompose two ways: `wᵢ = αs ++ bᵢ = cᵢ ++ βs`. Then in the
syntactic monoid:

* `[w₁ · w₂] = [αs · b₁ · αs · b₂] = [αs · b₂] = [w₂]`
  (αs-sandwich applied with `s := [b₁]`)
* `[w₁ · w₂] = [c₁ · βs · c₂ · βs] = [c₁ · βs] = [w₁]`
  (βs-sandwich applied with `s := [c₂]`)

so `[w₁] = [w₂]` and hence `w₁ ≡_L w₂`. This single double-sandwich
move handles both the long case (`|wᵢ| ≥ 2k`, `αs` and `βs` disjoint)
and the overlap case (`k ≤ |wᵢ| < 2k`, `αs` and `βs` overlap in `wᵢ`)
uniformly — the algebra in `M_L` is identical because the absorption
acts on the `[bᵢ]`/`[cᵢ]` factors regardless of their length.

The short case (`|w₁| < k` or `|w₂| < k`) is forced trivial: equal
`takeAt_left k` requires equal lengths when one side is shorter than
`k`, so `w₁ = w₂` directly. -/
theorem isGeneralizedDefinite_of_satisfies_kGeneralizedDefiniteEquation
    {L : Language α} {k : ℕ}
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

/-- **Lambert (2026) Prop 58**: a language is generalized `k`-definite
iff its syntactic monoid satisfies the LI equation. -/
theorem isGeneralizedDefinite_iff_satisfies_kGeneralizedDefiniteEquation
    {L : Language α} {k : ℕ} :
    L.IsGeneralizedDefinite k ↔
    Language.kGeneralizedDefiniteEquation L k :=
  ⟨IsGeneralizedDefinite.satisfies_kGeneralizedDefiniteEquation,
   isGeneralizedDefinite_of_satisfies_kGeneralizedDefiniteEquation⟩

end Language
