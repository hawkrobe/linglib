/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Language
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.Order

/-!
# Definite Languages (D_k, RD_k, ℒℐ_k, 𝒩)

A language `L` is **`k`-definite** when membership is determined by the last `k`
symbols of the input [rogers-pullum-2011] [lambert-2022]: any two strings agreeing
on their length-`k` suffix are L-equivalent. Dually, **reverse `k`-definite** (RD_k)
looks at the length-`k` *prefix*.

## The foundation: membership factors through an edge projection

The deepest characterisation is **invariance**: `L` is `k`-definite iff membership
factors through the length-`k` suffix map — `Language.InvariantUnder (Edge.right.takeAt k)`.
The whole family is read off from `InvariantUnder`:

* `IsDefinite k` = invariant under the right (suffix) projection,
* `IsReverseDefinite k` = invariant under the left (prefix) projection,
* `IsGeneralizedDefinite k` (Lambert's ℒℐ_k) = invariant under the joint
  (prefix, suffix) projection.

No grammar is needed: `Function.factorsThrough_iff` already supplies the witness
`∃ e, (· ∈ L) = e ∘ f` — the `e` is precisely the permitted-suffix predicate.

## The headline: `𝒩 = 𝒟 ∩ 𝒦`

`IsFiniteOrCofinite` (Lambert's 𝒩) is the classical co/finite class. Over a finite
alphabet it equals "`k`-definite for some `k` **and** reverse-`k'`-definite for some
`k'`" — the language-level half of Pin's `𝒩 = 𝒟 ∩ 𝒦` theorem
(`isFiniteOrCofinite_iff_exists_isDefinite_and_isReverseDefinite`). The algebraic
counterpart, via Eilenberg's variety theorem, is developed separately; this file is
pure list combinatorics.
-/

namespace Subregular

variable {α : Type*}

/-! ### Edge projections -/

/-- Which edge of the string the definite test inspects. `right` gives classical
D_k (final substring); `left` gives RD_k (initial substring). -/
inductive Edge | left | right
  deriving DecidableEq, Repr

namespace Edge

/-- Take the length-`k` substring at this edge of `xs`. `right` returns the last
`k` symbols; `left` the first `k`. Strings shorter than `k` are returned in full. -/
def takeAt (e : Edge) (k : ℕ) (xs : List α) : List α :=
  match e with
  | .left  => xs.take k
  | .right => xs.drop (xs.length - k)

@[simp] lemma left_takeAt (k : ℕ) (xs : List α) : Edge.left.takeAt k xs = xs.take k := rfl

@[simp] lemma right_takeAt (k : ℕ) (xs : List α) :
    Edge.right.takeAt k xs = xs.drop (xs.length - k) := rfl

/-- An edge substring has length `min k xs.length`. -/
lemma length_takeAt (e : Edge) (k : ℕ) (xs : List α) :
    (e.takeAt k xs).length = min k xs.length := by
  cases e with
  | left => simpa [takeAt] using (List.length_take k xs)
  | right => simp only [takeAt, List.length_drop]; omega

/-- For a short string the edge substring is the whole string. -/
lemma takeAt_of_length_le (e : Edge) {k : ℕ} {xs : List α} (h : xs.length ≤ k) :
    e.takeAt k xs = xs := by
  cases e with
  | left => exact List.take_of_length_le h
  | right => simp only [takeAt]; rw [show xs.length - k = 0 by omega, List.drop_zero]

end Edge

/-! ### Edge-bridge identities

A long word can be bridged to one sharing its right `k`-suffix and a prescribed
left `k'`-prefix; these are the combinatorial core of `𝒩 = 𝒟 ∩ 𝒦`. -/

/-- Bridge two long words via `w' = w₂.take k' ++ w₁.drop (w₁.length - k)`: it shares
`w₁`'s length-`k` suffix. -/
private lemma takeAt_right_eq_of_bridge {k k' : ℕ} {w₁ w₂ : List α}
    (hw₁ : k ≤ w₁.length) (hw₂ : k' ≤ w₂.length) :
    Edge.right.takeAt k (w₂.take k' ++ w₁.drop (w₁.length - k)) =
    Edge.right.takeAt k w₁ := by
  show (w₂.take k' ++ w₁.drop (w₁.length - k)).drop
        ((w₂.take k' ++ w₁.drop (w₁.length - k)).length - k) =
       w₁.drop (w₁.length - k)
  have h_take_len : (w₂.take k').length = k' := by rw [List.length_take]; omega
  have h_drop_len : (w₁.drop (w₁.length - k)).length = k := by rw [List.length_drop]; omega
  have h_total : (w₂.take k' ++ w₁.drop (w₁.length - k)).length = k' + k := by
    rw [List.length_append, h_take_len, h_drop_len]
  have hlen_diff :
      (w₂.take k' ++ w₁.drop (w₁.length - k)).length - k = k' := by rw [h_total]; omega
  rw [hlen_diff]
  exact List.drop_left' h_take_len

/-- The same bridge shares `w₂`'s length-`k'` prefix. -/
private lemma takeAt_left_eq_of_bridge {k k' : ℕ} {w₁ w₂ : List α}
    (_hw₁ : k ≤ w₁.length) (hw₂ : k' ≤ w₂.length) :
    Edge.left.takeAt k' (w₂.take k' ++ w₁.drop (w₁.length - k)) =
    Edge.left.takeAt k' w₂ := by
  show (w₂.take k' ++ w₁.drop (w₁.length - k)).take k' = w₂.take k'
  have h_take_len : (w₂.take k').length = k' := by rw [List.length_take]; omega
  rw [List.take_append_of_le_length (by rw [h_take_len]), List.take_take]
  congr 1; omega

end Subregular

namespace Language

variable {α : Type*}

open Subregular

/-! ### The definite family -/

/-- A language is **`k`-definite** (right-edge): membership factors through the
length-`k` suffix. -/
def IsDefinite (L : Language α) (k : ℕ) : Prop :=
  L.InvariantUnder (Edge.right.takeAt k)

/-- A language is **reverse `k`-definite** (left-edge): membership factors through
the length-`k` prefix. -/
def IsReverseDefinite (L : Language α) (k : ℕ) : Prop :=
  L.InvariantUnder (Edge.left.takeAt k)

/-- A language is **generalized `k`-definite** (Lambert's ℒℐ_k): membership factors
through the joint length-`k` prefix and suffix [lambert-2026]. -/
def IsGeneralizedDefinite (L : Language α) (k : ℕ) : Prop :=
  L.InvariantUnder (fun w => (Edge.left.takeAt k w, Edge.right.takeAt k w))

/-- Generalized definiteness in two-hypothesis form: equal length-`k` prefix and
suffix give L-equivalence (unpacking the joint-projection invariance). -/
lemma isGeneralizedDefinite_iff_edges {k : ℕ} {L : Language α} :
    L.IsGeneralizedDefinite k ↔
      ∀ ⦃a b⦄, Edge.left.takeAt k a = Edge.left.takeAt k b →
        Edge.right.takeAt k a = Edge.right.takeAt k b → (a ∈ L ↔ b ∈ L) :=
  ⟨fun h _ _ hpre hsuf => h.iff (by rw [hpre, hsuf]),
   fun h => InvariantUnder.mk fun _ _ hpair =>
     h (congrArg Prod.fst hpair) (congrArg Prod.snd hpair)⟩

/-- A language is **finite-or-cofinite** (Lambert's 𝒩): `L` or its complement is
finite (equivalently `L.Finite ∨ L ∈ Filter.cofinite`). -/
def IsFiniteOrCofinite (L : Language α) : Prop :=
  L.Finite ∨ Lᶜ.Finite

/-- Constructive view: a language carved out by a permitted length-`k` suffix set
is `k`-definite (this is the `e` of `Function.factorsThrough_iff`). -/
theorem isDefinite_setOf_right (k : ℕ) (P : Set (List α)) :
    IsDefinite {w | Edge.right.takeAt k w ∈ P} k :=
  fun _ _ hab => congrArg (· ∈ P) hab

/-- Mirror for the left edge: a permitted length-`k` prefix set is reverse-definite. -/
theorem isReverseDefinite_setOf_left (k : ℕ) (P : Set (List α)) :
    IsReverseDefinite {w | Edge.left.takeAt k w ∈ P} k :=
  fun _ _ hab => congrArg (· ∈ P) hab

/-! ### Inclusions into ℒℐ_k -/

/-- **D_k ⊆ ℒℐ_k**: the suffix alone determines membership, so the joint
prefix-and-suffix test does too. -/
theorem IsDefinite.toIsGeneralizedDefinite {k : ℕ} {L : Language α}
    (h : L.IsDefinite k) : L.IsGeneralizedDefinite k :=
  InvariantUnder.mk fun _ _ hab => h.iff (congrArg Prod.snd hab)

/-- **RD_k ⊆ ℒℐ_k**: symmetric, via the prefix. -/
theorem IsReverseDefinite.toIsGeneralizedDefinite {k : ℕ} {L : Language α}
    (h : L.IsReverseDefinite k) : L.IsGeneralizedDefinite k :=
  InvariantUnder.mk fun _ _ hab => h.iff (congrArg Prod.fst hab)

/-! ### `𝒩 = 𝒟 ∩ 𝒦` -/

/-- A bounded language is `(N+1)`-definite at either edge: words longer than `N` are
out, and shorter words are their own length-`(N+1)` edge substring, so that substring
determines membership. -/
private theorem isDefinite_of_bounded_aux {L : Language α} {N : ℕ} (e : Edge)
    (h_bound : ∀ w ∈ L, w.length ≤ N) : L.InvariantUnder (e.takeAt (N + 1)) := by
  refine InvariantUnder.mk fun a b hab => ?_
  have hlen : min (N + 1) a.length = min (N + 1) b.length := by
    have := congrArg List.length hab
    rwa [Edge.length_takeAt, Edge.length_takeAt] at this
  by_cases ha : a.length ≤ N
  · have hb : b.length ≤ N := by omega
    rw [Edge.takeAt_of_length_le e (by omega), Edge.takeAt_of_length_le e (by omega)] at hab
    rw [hab]
  · have hb : ¬ b.length ≤ N := by omega
    exact ⟨fun h => absurd (h_bound a h) ha, fun h => absurd (h_bound b h) hb⟩

/-- A co-bounded language (complement bounded) is `(N+1)`-definite: invariance is
closed under complement, so this is `isDefinite_of_bounded_aux` applied to `Lᶜ`. -/
private theorem isDefinite_of_cobounded_aux {L : Language α} {N : ℕ} (e : Edge)
    (h_bound : ∀ w ∈ Lᶜ, w.length ≤ N) : L.InvariantUnder (e.takeAt (N + 1)) := by
  simpa using (isDefinite_of_bounded_aux e h_bound).compl

/-- A finite set of words has a length bound. -/
private theorem exists_length_bound_of_finite {S : Set (List α)}
    (h : S.Finite) : ∃ N, ∀ w ∈ S, w.length ≤ N := by
  classical
  obtain ⟨N, hN⟩ := (Set.Finite.image (·.length) h).exists_le
  exact ⟨N, fun w hw => hN _ ⟨w, hw, rfl⟩⟩

/-- **Forward direction of `𝒩 = 𝒟 ∩ 𝒦`**: a finite-or-cofinite language is both
`k`-definite and reverse-`k'`-definite for some `k`, `k'`. -/
theorem IsFiniteOrCofinite.exists_isDefinite_and_isReverseDefinite
    {L : Language α} (h : L.IsFiniteOrCofinite) :
    (∃ k, L.IsDefinite k) ∧ (∃ k', L.IsReverseDefinite k') := by
  rcases h with h | h
  · obtain ⟨N, hN⟩ := exists_length_bound_of_finite h
    exact ⟨⟨N + 1, isDefinite_of_bounded_aux .right hN⟩,
           ⟨N + 1, isDefinite_of_bounded_aux .left hN⟩⟩
  · obtain ⟨N, hN⟩ := exists_length_bound_of_finite h
    exact ⟨⟨N + 1, isDefinite_of_cobounded_aux .right hN⟩,
           ⟨N + 1, isDefinite_of_cobounded_aux .left hN⟩⟩

/-- **Reverse direction of `𝒩 = 𝒟 ∩ 𝒦` (finite alphabet)**: if `L` is both
`k`-definite and reverse-`k'`-definite, it is finite-or-cofinite. For words of
length `≥ k + k'` membership is constant (bridge argument), so either the long
words are all in `L` (`Lᶜ` bounded) or none are (`L` bounded). -/
theorem isFiniteOrCofinite_of_isDefinite_and_isReverseDefinite [Finite α]
    {L : Language α}
    (h : (∃ k, L.IsDefinite k) ∧ (∃ k', L.IsReverseDefinite k')) :
    L.IsFiniteOrCofinite := by
  classical
  obtain ⟨⟨k, hD⟩, ⟨k', hR⟩⟩ := h
  have constancy : ∀ w₁ w₂ : List α,
      k + k' ≤ w₁.length → k + k' ≤ w₂.length → (w₁ ∈ L ↔ w₂ ∈ L) := by
    intro w₁ w₂ hw₁ hw₂
    set w' := w₂.take k' ++ w₁.drop (w₁.length - k) with hw'_def
    have hk_le_w₁ : k ≤ w₁.length := by omega
    have hk'_le_w₂ : k' ≤ w₂.length := by omega
    have hw₁_iff_w' : w₁ ∈ L ↔ w' ∈ L :=
      hD.iff (takeAt_right_eq_of_bridge hk_le_w₁ hk'_le_w₂).symm
    have hw'_iff_w₂ : w' ∈ L ↔ w₂ ∈ L :=
      hR.iff (takeAt_left_eq_of_bridge hk_le_w₁ hk'_le_w₂)
    exact hw₁_iff_w'.trans hw'_iff_w₂
  have h_short_finite : Set.Finite {w : List α | w.length < k + k'} :=
    List.finite_length_lt α (k + k')
  by_cases h_witness : ∃ w₀, k + k' ≤ w₀.length ∧ w₀ ∈ L
  · right
    obtain ⟨w₀, hw₀_len, hw₀_L⟩ := h_witness
    apply Set.Finite.subset h_short_finite
    intro w hwLc
    show w.length < k + k'
    by_contra hge
    push_neg at hge
    exact hwLc ((constancy w w₀ hge hw₀_len).mpr hw₀_L)
  · left
    push_neg at h_witness
    apply Set.Finite.subset h_short_finite
    intro w hwL
    show w.length < k + k'
    by_contra hge
    push_neg at hge
    exact h_witness w hge hwL

/-- **Pin's `𝒩 = 𝒟 ∩ 𝒦` (finite alphabet)**: a language over a finite alphabet is
finite-or-cofinite iff it is `k`-definite for some `k` and reverse-`k'`-definite for
some `k'`. -/
theorem isFiniteOrCofinite_iff_exists_isDefinite_and_isReverseDefinite [Finite α]
    {L : Language α} :
    L.IsFiniteOrCofinite ↔
    (∃ k, L.IsDefinite k) ∧ (∃ k', L.IsReverseDefinite k') :=
  ⟨IsFiniteOrCofinite.exists_isDefinite_and_isReverseDefinite,
   isFiniteOrCofinite_of_isDefinite_and_isReverseDefinite⟩

end Language
