/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.Definite`.
-/
module

public import Mathlib.Computability.Language
public import Mathlib.Logic.Function.Basic
public import Linglib.Core.Relation.FactorsThroughOn
public import Linglib.Core.Data.List.DropRight
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Data.Set.Finite.List

/-!
# Definite languages

This file defines the definite languages and their relatives. A language `L` is *`k`-definite*
when membership of a word is decided by its last `k` letters: any two words with the same
length-`k` suffix are both in `L` or both outside it. Perles, Rabin and Shamir develop the theory
of these languages; *reverse `k`-definite* languages are the mirror image through the length-`k`
prefix, and *generalized `k`-definite* languages are decided by the prefix and suffix together.

## Main definitions

* `Edge`, `Edge.takeAt`: an edge of a word and its length-`k` part there (`right` for the suffix,
  `left` for the prefix).
* `Language.IsDefinite`, `Language.IsReverseDefinite`, `Language.IsGeneralizedDefinite`: membership
  factors through the suffix, the prefix, and both.
* `Language.IsFiniteOrCofinite`: `L` or its complement is finite.

## Main results

* `Language.IsDefinite.toIsGeneralizedDefinite`,
  `Language.IsReverseDefinite.toIsGeneralizedDefinite`: definite and reverse definite languages are
  generalized definite.
* `Language.isFiniteOrCofinite_iff_exists_isDefinite_and_isReverseDefinite`: over a finite
  alphabet, a language is finite or cofinite exactly when it is both definite and reverse definite.

## References

* [perles-rabin-shamir-1963]
* [pin-mfa]
-/

@[expose] public section

variable {α : Type*}

/-! ### Edge projections -/

/-- An `Edge` names an end of a word, `right` for the end that definite languages inspect and
`left` for the beginning that reverse definite languages inspect. -/
inductive Edge | left | right
  deriving DecidableEq, Repr

namespace Edge

variable (e : Edge) (k : ℕ) (xs : List α)

/-- The length-`k` part of `xs` at an edge, its prefix `List.take` at the left and its suffix
`List.rtake` at the right. A word shorter than `k` is returned in full. -/
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

/-- The left-`k`-prefix of `p ++ rest` is that of `p`, when `k ≤ p.length`. -/
lemma takeAt_left_append_of_le_length {k : ℕ} (p rest : List α) (h : k ≤ p.length) :
    Edge.left.takeAt k (p ++ rest) = Edge.left.takeAt k p :=
  List.take_append_of_le_length h

/-- The right-`k`-suffix of `x ++ rest` is that of `rest`, when `k ≤ rest.length`. -/
lemma takeAt_right_append_of_le_length {k : ℕ} (x rest : List α) (h : k ≤ rest.length) :
    Edge.right.takeAt k (x ++ rest) = Edge.right.takeAt k rest :=
  List.rtake_append_of_le_length h

/-- `takeAt k` is idempotent, since its output already has length at most `k`. -/
lemma takeAt_idem : e.takeAt k (e.takeAt k xs) = e.takeAt k xs :=
  takeAt_of_length_le e (by rw [length_takeAt]; exact min_le_left _ _)

/-- A shorter edge substring of a longer one is the shorter edge substring. -/
lemma takeAt_takeAt_of_le {k k' : ℕ} (h : k ≤ k') (xs : List α) :
    e.takeAt k (e.takeAt k' xs) = e.takeAt k xs := by
  cases e <;> simp [List.take_take, List.rtake_rtake, h]

end Edge

/-! ### Edge-bridge identities

Two long words are bridged by a word sharing the length-`k` suffix of the first and the
length-`k'` prefix of the second. This is the combinatorial step behind the characterization of
the finite and cofinite languages. -/

/-- The word `w₂.take k' ++ w₁.rtake k` shares the length-`k` suffix of `w₁`. -/
private lemma takeAt_right_eq_of_bridge {k k' : ℕ} {w₁ w₂ : List α}
    (hw₁ : k ≤ w₁.length) (_hw₂ : k' ≤ w₂.length) :
    Edge.right.takeAt k (w₂.take k' ++ w₁.rtake k) = Edge.right.takeAt k w₁ := by
  have hk : k ≤ (w₁.rtake k).length := by rw [List.length_rtake]; omega
  rw [Edge.takeAt_right, Edge.takeAt_right, List.rtake_append_of_le_length hk,
    List.rtake_of_length_le (by rw [List.length_rtake]; omega)]

/-- The same bridge shares `w₂`'s length-`k'` prefix. -/
private lemma takeAt_left_eq_of_bridge {k k' : ℕ} {w₁ w₂ : List α}
    (_hw₁ : k ≤ w₁.length) (hw₂ : k' ≤ w₂.length) :
    Edge.left.takeAt k' (w₂.take k' ++ w₁.rtake k) = Edge.left.takeAt k' w₂ := by
  rw [Edge.takeAt_left, Edge.takeAt_left,
    List.take_append_of_le_length (by rw [List.length_take]; omega), List.take_take, min_self]

namespace Language

variable {α : Type*}


/-! ### The definite family -/

/-- A language is *`k`-definite* when membership factors through the length-`k` suffix. -/
def IsDefinite (L : Language α) (k : ℕ) : Prop :=
  Function.FactorsThrough (· ∈ L) (Edge.right.takeAt k)

/-- A language is *reverse `k`-definite* when membership factors through the length-`k`
prefix. -/
def IsReverseDefinite (L : Language α) (k : ℕ) : Prop :=
  Function.FactorsThrough (· ∈ L) (Edge.left.takeAt k)

/-- A language is *generalized `k`-definite* when membership factors through the length-`k`
prefix and suffix together. -/
def IsGeneralizedDefinite (L : Language α) (k : ℕ) : Prop :=
  Function.FactorsThrough (· ∈ L) (fun w ↦ (Edge.left.takeAt k w, Edge.right.takeAt k w))

/-- A language is generalized `k`-definite exactly when words with equal length-`k` prefix and
suffix are both in it or both outside it. -/
lemma isGeneralizedDefinite_iff_edges {k : ℕ} {L : Language α} :
    L.IsGeneralizedDefinite k ↔
      ∀ ⦃a b⦄, Edge.left.takeAt k a = Edge.left.takeAt k b →
        Edge.right.takeAt k a = Edge.right.takeAt k b → (a ∈ L ↔ b ∈ L) :=
  ⟨fun h _ _ hpre hsuf ↦ iff_of_eq (h (by simp only [hpre, hsuf])),
   fun h _ _ hpair ↦ propext (h (congrArg Prod.fst hpair) (congrArg Prod.snd hpair))⟩

/-- A language is `k`-definite exactly when every word is in it just when its length-`k` suffix
is. -/
lemma isDefinite_iff_mem_takeAt {k : ℕ} {L : Language α} :
    L.IsDefinite k ↔ ∀ w, w ∈ L ↔ Edge.right.takeAt k w ∈ L := by
  unfold IsDefinite
  rw [Function.factorsThrough_iff_of_idempotent (fun a ↦ Edge.right.takeAt_idem k a)]
  simp only [eq_iff_iff]

/-- A language is reverse `k`-definite exactly when every word is in it just when its length-`k`
prefix is. -/
lemma isReverseDefinite_iff_mem_takeAt {k : ℕ} {L : Language α} :
    L.IsReverseDefinite k ↔ ∀ w, w ∈ L ↔ Edge.left.takeAt k w ∈ L := by
  unfold IsReverseDefinite
  rw [Function.factorsThrough_iff_of_idempotent (fun a ↦ Edge.left.takeAt_idem k a)]
  simp only [eq_iff_iff]

/-- A language is *finite or cofinite* when it or its complement is finite. -/
def IsFiniteOrCofinite (L : Language α) : Prop :=
  L.Finite ∨ Lᶜ.Finite

/-- The words whose length-`k` suffix lies in a given set form a `k`-definite language. -/
theorem isDefinite_setOf_right (k : ℕ) (P : Set (List α)) :
    IsDefinite {w | Edge.right.takeAt k w ∈ P} k :=
  fun _ _ hab ↦ congrArg (· ∈ P) hab

/-- The words whose length-`k` prefix lies in a given set form a reverse `k`-definite
language. -/
theorem isReverseDefinite_setOf_left (k : ℕ) (P : Set (List α)) :
    IsReverseDefinite {w | Edge.left.takeAt k w ∈ P} k :=
  fun _ _ hab ↦ congrArg (· ∈ P) hab

/-! ### Monotonicity in the window -/

/-- A `k`-definite language is `k'`-definite for every `k' ≥ k`. -/
theorem IsDefinite.mono {k k' : ℕ} {L : Language α} (h : L.IsDefinite k) (hk : k ≤ k') :
    L.IsDefinite k' :=
  fun _ _ hab ↦
    h (by rw [← Edge.takeAt_takeAt_of_le .right hk, hab, Edge.takeAt_takeAt_of_le .right hk])

/-- A reverse `k`-definite language is reverse `k'`-definite for every `k' ≥ k`. -/
theorem IsReverseDefinite.mono {k k' : ℕ} {L : Language α} (h : L.IsReverseDefinite k)
    (hk : k ≤ k') : L.IsReverseDefinite k' :=
  fun _ _ hab ↦
    h (by rw [← Edge.takeAt_takeAt_of_le .left hk, hab, Edge.takeAt_takeAt_of_le .left hk])

/-- A generalized `k`-definite language is generalized `k'`-definite for every `k' ≥ k`. -/
theorem IsGeneralizedDefinite.mono {k k' : ℕ} {L : Language α} (h : L.IsGeneralizedDefinite k)
    (hk : k ≤ k') : L.IsGeneralizedDefinite k' :=
  fun a b hab ↦ by
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj hab
    refine h (Prod.ext ?_ ?_)
    · show Edge.left.takeAt k a = Edge.left.takeAt k b
      rw [← Edge.takeAt_takeAt_of_le .left hk, h₁, Edge.takeAt_takeAt_of_le .left hk]
    · show Edge.right.takeAt k a = Edge.right.takeAt k b
      rw [← Edge.takeAt_takeAt_of_le .right hk, h₂, Edge.takeAt_takeAt_of_le .right hk]

/-! ### Affix languages -/

/-- The words beginning with `xs`. -/
def ofPrefix (xs : List α) : Language α := {w | xs <+: w}

/-- The words ending in `xs`. -/
def ofSuffix (xs : List α) : Language α := {w | xs <:+ w}

/-- The words beginning with `xs` form a reverse definite language with window `xs.length`. -/
theorem isReverseDefinite_ofPrefix (xs : List α) : (ofPrefix xs).IsReverseDefinite xs.length :=
  fun a b hab ↦ by
    simp only [Edge.takeAt_left] at hab
    show (xs <+: a) = (xs <+: b)
    rw [List.prefix_iff_eq_take, List.prefix_iff_eq_take, hab]

/-- The words ending in `xs` form a definite language with window `xs.length`. -/
theorem isDefinite_ofSuffix (xs : List α) : (ofSuffix xs).IsDefinite xs.length :=
  fun a b hab ↦ by
    show (xs <:+ a) = (xs <:+ b)
    rw [List.suffix_iff_eq_drop, List.suffix_iff_eq_drop]
    exact congrArg (xs = ·) hab

/-! ### Reverse duality -/

private lemma takeAt_left_reverse (k : ℕ) (l : List α) :
    Edge.left.takeAt k l.reverse = (Edge.right.takeAt k l).reverse := by
  simp [Edge.takeAt_left, Edge.takeAt_right, List.rtake_eq_reverse_take_reverse]

private lemma takeAt_right_reverse (k : ℕ) (l : List α) :
    Edge.right.takeAt k l.reverse = (Edge.left.takeAt k l).reverse := by
  simp [Edge.takeAt_left, Edge.takeAt_right, List.rtake_eq_reverse_take_reverse]

/-- A language is reverse `k`-definite exactly when its reversal is `k`-definite. -/
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

/-! ### Inclusions into the generalized definite languages -/

/-- A `k`-definite language is generalized `k`-definite. -/
theorem IsDefinite.toIsGeneralizedDefinite {k : ℕ} {L : Language α}
    (h : L.IsDefinite k) : L.IsGeneralizedDefinite k :=
  fun _ _ hab ↦ h (congrArg Prod.snd hab)

/-- A reverse `k`-definite language is generalized `k`-definite. -/
theorem IsReverseDefinite.toIsGeneralizedDefinite {k : ℕ} {L : Language α}
    (h : L.IsReverseDefinite k) : L.IsGeneralizedDefinite k :=
  fun _ _ hab ↦ h (congrArg Prod.fst hab)

/-! ### Finite and cofinite languages -/

/-- A language whose membership is constant off a finite set `s` is finite or cofinite, since
either `Lᶜ ⊆ s` or `L ⊆ s`. -/
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

/-- In a language of words of length at most `N`, membership factors through the
length-`(N + 1)` edge projection, since longer words are outside and shorter ones are their own
projection. -/
private lemma factorsThrough_takeAt_of_bounded {L : Language α} {N : ℕ} (e : Edge)
    (h_bound : ∀ w ∈ L, w.length ≤ N) :
    Function.FactorsThrough (· ∈ L) (e.takeAt (N + 1)) := by
  refine fun a b hab ↦ ?_
  have hlen : min (N + 1) a.length = min (N + 1) b.length := by
    have := congrArg List.length hab
    rwa [Edge.length_takeAt, Edge.length_takeAt] at this
  by_cases ha : a.length ≤ N
  · have hb : b.length ≤ N := by omega
    rw [Edge.takeAt_of_length_le e (by omega), Edge.takeAt_of_length_le e (by omega)] at hab
    rw [hab]
  · have hb : ¬ b.length ≤ N := by omega
    exact propext ⟨fun h ↦ absurd (h_bound a h) ha, fun h ↦ absurd (h_bound b h) hb⟩

/-- A language whose words have length at most `N` is `(N + 1)`-definite. -/
theorem isDefinite_succ_of_forall_length_le {L : Language α} {N : ℕ}
    (h : ∀ w ∈ L, w.length ≤ N) : L.IsDefinite (N + 1) :=
  factorsThrough_takeAt_of_bounded .right h

/-- A language whose words have length at most `N` is reverse `(N + 1)`-definite. -/
theorem isReverseDefinite_succ_of_forall_length_le {L : Language α} {N : ℕ}
    (h : ∀ w ∈ L, w.length ≤ N) : L.IsReverseDefinite (N + 1) :=
  factorsThrough_takeAt_of_bounded .left h

/-- When the complement of a language consists of words of length at most `N`, membership still
factors through the length-`(N + 1)` edge projection. -/
private lemma factorsThrough_takeAt_of_cobounded {L : Language α} {N : ℕ} (e : Edge)
    (h_bound : ∀ w ∈ Lᶜ, w.length ≤ N) :
    Function.FactorsThrough (· ∈ L) (e.takeAt (N + 1)) :=
  fun _ _ hab ↦
    propext (not_iff_not.mp (iff_of_eq (factorsThrough_takeAt_of_bounded e h_bound hab)))

/-- A finite set of words has a length bound. -/
private lemma exists_length_bound_of_finite {S : Set (List α)} (h : S.Finite) :
    ∃ N, ∀ w ∈ S, w.length ≤ N :=
  let ⟨N, hN⟩ := (h.image (·.length)).exists_le
  ⟨N, fun w hw ↦ hN _ ⟨w, hw, rfl⟩⟩

/-- A finite or cofinite language is definite and reverse definite. -/
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

/-- Over a finite alphabet, a language that is both definite and reverse definite is finite or
cofinite, since membership is constant on words of length at least `k + k'`. -/
theorem isFiniteOrCofinite_of_isDefinite_and_isReverseDefinite [Finite α]
    {L : Language α}
    (h : (∃ k, L.IsDefinite k) ∧ (∃ k', L.IsReverseDefinite k')) :
    L.IsFiniteOrCofinite := by
  obtain ⟨⟨k, hD⟩, ⟨k', hR⟩⟩ := h
  refine isFiniteOrCofinite_of_eventually_constant (List.finite_length_lt α (k + k')) ?_
  intro w₁ hw₁ w₂ hw₂
  have hk : k ≤ w₁.length := by rw [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hw₁; omega
  have hk' : k' ≤ w₂.length := by rw [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hw₂; omega
  exact (iff_of_eq (hD (takeAt_right_eq_of_bridge hk hk').symm)).trans
    (iff_of_eq (hR (takeAt_left_eq_of_bridge hk hk')))

/-- Over a finite alphabet, a language is finite or cofinite exactly when it is definite and
reverse definite. -/
theorem isFiniteOrCofinite_iff_exists_isDefinite_and_isReverseDefinite [Finite α]
    {L : Language α} :
    L.IsFiniteOrCofinite ↔
    (∃ k, L.IsDefinite k) ∧ (∃ k', L.IsReverseDefinite k') :=
  ⟨IsFiniteOrCofinite.exists_isDefinite_and_isReverseDefinite,
   isFiniteOrCofinite_of_isDefinite_and_isReverseDefinite⟩

end Language
