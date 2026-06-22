/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Computability.Language
import Mathlib.Logic.Function.Basic
import Linglib.Core.Data.List.DropRight
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Set.Finite.List

/-!
# Definite languages

A language `L` is **`k`-definite** when membership is decided by the last `k`
symbols of a word [rogers-pullum-2011] [lambert-2022]: any two words sharing their
length-`k` suffix are L-equivalent. **Reverse `k`-definite** (`RD_k`) is the dual
through the length-`k` prefix, and **generalized `k`-definite** (Lambert's `ℒℐ_k`)
tests prefix and suffix jointly [lambert-2026].

## Main definitions

* `Subregular.Edge` and `Subregular.Edge.takeAt` — a string edge and its length-`k`
  substring (`right` = suffix, `left` = prefix).
* `Language.IsDefinite`, `Language.IsReverseDefinite`, `Language.IsGeneralizedDefinite`
  — membership factoring through the suffix, prefix, and joint edge projections.
* `Language.IsFiniteOrCofinite` — Lambert's `𝒩`: `L` or its complement is finite.

## Main theorems

* `Language.IsDefinite.toIsGeneralizedDefinite` and
  `Language.IsReverseDefinite.toIsGeneralizedDefinite` — `D_k, RD_k ⊆ ℒℐ_k`.
* `Language.isFiniteOrCofinite_iff_exists_isDefinite_and_isReverseDefinite` — over a
  finite alphabet, `𝒩 = 𝒟 ∩ 𝒦` [pin-mfa]: a language is finite-or-cofinite iff it
  is definite and reverse-definite.
-/

namespace Subregular

variable {α : Type*}

/-! ### Edge projections -/

/-- Which edge of the string the definite test inspects. `right` gives classical
D_k (final substring); `left` gives RD_k (initial substring). -/
inductive Edge | left | right
  deriving DecidableEq, Repr

namespace Edge

variable (e : Edge) (k : ℕ) (xs : List α)

/-- Take the length-`k` substring at this edge of `xs`: `left` is the length-`k`
prefix `List.take`, `right` the length-`k` suffix `List.rtake`. Strings shorter
than `k` are returned in full. -/
def takeAt : List α :=
  match e with
  | .left  => xs.take k
  | .right => xs.rtake k

@[simp] lemma takeAt_left : Edge.left.takeAt k xs = xs.take k := rfl

@[simp] lemma takeAt_right : Edge.right.takeAt k xs = xs.rtake k := rfl

/-- An edge substring has length `min k xs.length`. -/
lemma length_takeAt : (e.takeAt k xs).length = min k xs.length := by
  cases e <;> simp

/-- For a short string the edge substring is the whole string. -/
lemma takeAt_of_length_le {k : ℕ} {xs : List α} (h : xs.length ≤ k) :
    e.takeAt k xs = xs := by
  cases e with
  | left => exact List.take_of_length_le h
  | right => exact List.rtake_of_length_le h

/-- The right-`k`-suffix of `x ++ rest` is that of `rest`, when `k ≤ rest.length`. -/
lemma takeAt_right_append_of_le_length {k : ℕ} (x rest : List α) (h : k ≤ rest.length) :
    Edge.right.takeAt k (x ++ rest) = Edge.right.takeAt k rest :=
  List.rtake_append_of_le_length x rest h

end Edge

/-! ### Edge-bridge identities

A long word can be bridged to one sharing its right `k`-suffix and a prescribed
left `k'`-prefix; these are the combinatorial core of `𝒩 = 𝒟 ∩ 𝒦`. -/

/-- Bridge two long words via `w' = w₂.take k' ++ w₁.rtake k`: it shares `w₁`'s
length-`k` suffix (the tail-take absorbs the prepended prefix). -/
private lemma takeAt_right_eq_of_bridge {k k' : ℕ} {w₁ w₂ : List α}
    (hw₁ : k ≤ w₁.length) (_hw₂ : k' ≤ w₂.length) :
    Edge.right.takeAt k (w₂.take k' ++ w₁.rtake k) = Edge.right.takeAt k w₁ := by
  have hk : k ≤ (w₁.rtake k).length := by rw [List.length_rtake]; omega
  rw [Edge.takeAt_right, Edge.takeAt_right, List.rtake_append_of_le_length _ _ hk,
    List.rtake_of_length_le (by rw [List.length_rtake]; omega)]

/-- The same bridge shares `w₂`'s length-`k'` prefix. -/
private lemma takeAt_left_eq_of_bridge {k k' : ℕ} {w₁ w₂ : List α}
    (_hw₁ : k ≤ w₁.length) (hw₂ : k' ≤ w₂.length) :
    Edge.left.takeAt k' (w₂.take k' ++ w₁.rtake k) = Edge.left.takeAt k' w₂ := by
  rw [Edge.takeAt_left, Edge.takeAt_left,
    List.take_append_of_le_length (by rw [List.length_take]; omega), List.take_take, min_self]

end Subregular

namespace Language

variable {α : Type*}

open Subregular

/-! ### The definite family -/

/-- A language is **`k`-definite** (right-edge): membership factors through the
length-`k` suffix. -/
def IsDefinite (L : Language α) (k : ℕ) : Prop :=
  Function.FactorsThrough (· ∈ L) (Edge.right.takeAt k)

/-- A language is **reverse `k`-definite** (left-edge): membership factors through
the length-`k` prefix. -/
def IsReverseDefinite (L : Language α) (k : ℕ) : Prop :=
  Function.FactorsThrough (· ∈ L) (Edge.left.takeAt k)

/-- A language is **generalized `k`-definite** (Lambert's ℒℐ_k): membership factors
through the joint length-`k` prefix and suffix [lambert-2026]. -/
def IsGeneralizedDefinite (L : Language α) (k : ℕ) : Prop :=
  Function.FactorsThrough (· ∈ L) (fun w => (Edge.left.takeAt k w, Edge.right.takeAt k w))

/-- Generalized definiteness in two-hypothesis form: equal length-`k` prefix and
suffix give L-equivalence (unpacking the joint-projection invariance). -/
lemma isGeneralizedDefinite_iff_edges {k : ℕ} {L : Language α} :
    L.IsGeneralizedDefinite k ↔
      ∀ ⦃a b⦄, Edge.left.takeAt k a = Edge.left.takeAt k b →
        Edge.right.takeAt k a = Edge.right.takeAt k b → (a ∈ L ↔ b ∈ L) :=
  ⟨fun h _ _ hpre hsuf => iff_of_eq (h (by simp only [hpre, hsuf])),
   fun h _ _ hpair => propext (h (congrArg Prod.fst hpair) (congrArg Prod.snd hpair))⟩

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

/-! ### Reverse duality -/

private lemma takeAt_left_reverse (k : ℕ) (l : List α) :
    Edge.left.takeAt k l.reverse = (Edge.right.takeAt k l).reverse := by
  simp [Edge.takeAt_left, Edge.takeAt_right, List.rtake_eq_reverse_take_reverse]

private lemma takeAt_right_reverse (k : ℕ) (l : List α) :
    Edge.right.takeAt k l.reverse = (Edge.left.takeAt k l).reverse := by
  simp [Edge.takeAt_left, Edge.takeAt_right, List.rtake_eq_reverse_take_reverse]

/-- **Reverse duality**: reverse-`k`-definite is `k`-definite of the reversed language. -/
theorem isReverseDefinite_iff_isDefinite_reverse {k : ℕ} {L : Language α} :
    L.IsReverseDefinite k ↔ L.reverse.IsDefinite k := by
  constructor
  · intro h a b hab
    have key : Edge.left.takeAt k a.reverse = Edge.left.takeAt k b.reverse := by
      rw [takeAt_left_reverse, takeAt_left_reverse, hab]
    simpa only [Language.mem_reverse] using h key
  · intro h a b hab
    have key : Edge.right.takeAt k a.reverse = Edge.right.takeAt k b.reverse := by
      rw [takeAt_right_reverse, takeAt_right_reverse, hab]
    simpa only [Language.reverse_mem_reverse] using h key

/-! ### Inclusions into ℒℐ_k -/

/-- **D_k ⊆ ℒℐ_k**: the suffix alone determines membership, so the joint
prefix-and-suffix test does too. -/
theorem IsDefinite.toIsGeneralizedDefinite {k : ℕ} {L : Language α}
    (h : L.IsDefinite k) : L.IsGeneralizedDefinite k :=
  fun _ _ hab => h (congrArg Prod.snd hab)

/-- **RD_k ⊆ ℒℐ_k**: symmetric, via the prefix. -/
theorem IsReverseDefinite.toIsGeneralizedDefinite {k : ℕ} {L : Language α}
    (h : L.IsReverseDefinite k) : L.IsGeneralizedDefinite k :=
  fun _ _ hab => h (congrArg Prod.fst hab)

/-! ### `𝒩 = 𝒟 ∩ 𝒦` -/

/-- A language whose membership is constant off a finite set `s` is finite-or-cofinite:
either some word outside `s` lies in `L` (forcing `Lᶜ ⊆ s`) or none does (forcing
`L ⊆ s`). The reusable engine behind the reverse direction of `𝒩 = 𝒟 ∩ 𝒦`. -/
theorem isFiniteOrCofinite_of_eventually_constant {L : Language α} {s : Set (List α)}
    (hs : s.Finite) (h : ∀ a ∈ sᶜ, ∀ b ∈ sᶜ, (a ∈ L ↔ b ∈ L)) : L.IsFiniteOrCofinite := by
  by_cases h_witness : ∃ w₀ ∈ sᶜ, w₀ ∈ L
  · obtain ⟨w₀, hw₀_s, hw₀_L⟩ := h_witness
    refine Or.inr (hs.subset ?_)
    intro w hwLc
    by_contra hws
    exact hwLc ((h w hws w₀ hw₀_s).mpr hw₀_L)
  · simp only [not_exists, not_and] at h_witness
    refine Or.inl (hs.subset ?_)
    intro w hwL
    by_contra hws
    exact h_witness w hws hwL

/-- In a bounded language, membership factors through the length-`(N+1)` edge projection:
words longer than `N` are out, and shorter words are their own length-`(N+1)` edge
substring, so that substring determines membership. -/
private lemma factorsThrough_takeAt_of_bounded {L : Language α} {N : ℕ} (e : Edge)
    (h_bound : ∀ w ∈ L, w.length ≤ N) :
    Function.FactorsThrough (· ∈ L) (e.takeAt (N + 1)) := by
  refine fun a b hab => ?_
  have hlen : min (N + 1) a.length = min (N + 1) b.length := by
    have := congrArg List.length hab
    rwa [Edge.length_takeAt, Edge.length_takeAt] at this
  by_cases ha : a.length ≤ N
  · have hb : b.length ≤ N := by omega
    rw [Edge.takeAt_of_length_le e (by omega), Edge.takeAt_of_length_le e (by omega)] at hab
    rw [hab]
  · have hb : ¬ b.length ≤ N := by omega
    exact propext ⟨fun h => absurd (h_bound a h) ha, fun h => absurd (h_bound b h) hb⟩

/-- When the complement is bounded, membership still factors through the length-`(N+1)`
edge projection: `factorsThrough_takeAt_of_bounded` gives it for `Lᶜ`, and factoring
through is preserved by negation (`Lᶜᶜ = L`). -/
private lemma factorsThrough_takeAt_of_cobounded {L : Language α} {N : ℕ} (e : Edge)
    (h_bound : ∀ w ∈ Lᶜ, w.length ≤ N) :
    Function.FactorsThrough (· ∈ L) (e.takeAt (N + 1)) :=
  fun _ _ hab =>
    propext (not_iff_not.mp (iff_of_eq (factorsThrough_takeAt_of_bounded e h_bound hab)))

/-- A finite set of words has a length bound. -/
private lemma exists_length_bound_of_finite {S : Set (List α)} (h : S.Finite) :
    ∃ N, ∀ w ∈ S, w.length ≤ N :=
  let ⟨N, hN⟩ := (h.image (·.length)).exists_le
  ⟨N, fun w hw => hN _ ⟨w, hw, rfl⟩⟩

/-- **Forward direction of `𝒩 = 𝒟 ∩ 𝒦`**: a finite-or-cofinite language is both
`k`-definite and reverse-`k'`-definite for some `k`, `k'`. -/
theorem IsFiniteOrCofinite.exists_isDefinite_and_isReverseDefinite
    {L : Language α} (h : L.IsFiniteOrCofinite) :
    (∃ k, L.IsDefinite k) ∧ (∃ k', L.IsReverseDefinite k') := by
  rcases h with h | h
  · obtain ⟨N, hN⟩ := exists_length_bound_of_finite h
    exact ⟨⟨N + 1, factorsThrough_takeAt_of_bounded .right hN⟩,
           ⟨N + 1, factorsThrough_takeAt_of_bounded .left hN⟩⟩
  · obtain ⟨N, hN⟩ := exists_length_bound_of_finite h
    exact ⟨⟨N + 1, factorsThrough_takeAt_of_cobounded .right hN⟩,
           ⟨N + 1, factorsThrough_takeAt_of_cobounded .left hN⟩⟩

/-- **Reverse direction of `𝒩 = 𝒟 ∩ 𝒦` (finite alphabet)**: if `L` is both
`k`-definite and reverse-`k'`-definite, it is finite-or-cofinite. For words of
length `≥ k + k'` membership is constant (bridge argument), so either the long
words are all in `L` (`Lᶜ` bounded) or none are (`L` bounded). -/
theorem isFiniteOrCofinite_of_isDefinite_and_isReverseDefinite [Finite α]
    {L : Language α}
    (h : (∃ k, L.IsDefinite k) ∧ (∃ k', L.IsReverseDefinite k')) :
    L.IsFiniteOrCofinite := by
  obtain ⟨⟨k, hD⟩, ⟨k', hR⟩⟩ := h
  refine isFiniteOrCofinite_of_eventually_constant (List.finite_length_lt α (k + k')) ?_
  intro w₁ hw₁ w₂ hw₂
  have hk : k ≤ w₁.length := by rw [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hw₁; omega
  have hk' : k' ≤ w₂.length := by rw [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hw₂; omega
  exact (iff_of_eq (hD (takeAt_right_eq_of_bridge hk hk').symm)).trans
    (iff_of_eq (hR (takeAt_left_eq_of_bridge hk hk')))

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
