/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Defs
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Fintype.Order

/-!
# Definite and Reverse-Definite Languages (D_k, RD_k)

A language `L` is **`k`-definite** when membership is determined by the
last `k` symbols of the input [rogers-pullum-2011] [lambert-2022]:
any two strings agreeing on their length-`k` suffix are L-equivalent.
The dual notion, **reverse `k`-definite** (RD_k), checks the length-`k`
*prefix* instead.

These are weaker than SL_k in expressive power — they look at one fixed
position (the edge) rather than every contiguous window — but they are
foundational for the right- and left-context-only fragments of
finite-state computation. Concrete linguistic uses include word-final
neutralization (D_1 / D_2: a constraint on the last few segments) and
word-initial prosodic templates (RD_k).

## Strictly definite vs definite

The classical definite/strictly-definite distinction collapses for the
generative formulation used here: a language is definite iff it is
strictly definite (the permitted-suffix set is just the suffixes of
L-members), so we use a single `DefiniteGrammar` type and elide the
"strictly" qualifier.

## No boundary augmentation

Unlike SL/LT, D and RD do not use boundary symbols: the suffix/prefix
already privileges the edge structurally, and adding `none` markers
would just shift indexing by `k - 1`. The grammar's `permitted` set is
over the raw alphabet `α`, not `Augmented α`.

## Edge parameterization

Both D_k and RD_k are parameterized over an `Edge` (right vs left), so a
single `EdgeDefiniteGrammar` covers both classes; `DefiniteGrammar` and
`ReverseDefiniteGrammar` are abbreviations selecting the right and left
edges respectively.

## Generalised definite and finite-or-cofinite

This file also houses two related affix-based classes from
[lambert-2026]:

* `IsGeneralizedDefinite k` (Lambert's ℒℐ_k): membership is determined by
  the joint length-`k` prefix and length-`k` suffix. Strictly more
  expressive than `IsDefinite k ⊔ IsReverseDefinite k` because a single
  formula can simultaneously constrain both edges.
* `IsFiniteOrCofinite` (Lambert's 𝒩, see Lambert (2026) p. 8 fn. 4): the
  classical co/finite class, finite sets and complements thereof. Equals
  `IsDefinite k ∩ IsReverseDefinite k` for sufficiently large `k`.

Both are derived predicates (not new structural grammars): the algebra
they characterise is already captured by `EdgeDefiniteGrammar` and
`Set.Finite`.
-/

namespace Core.Computability.Subregular

variable {α : Type*}

/-- Which edge of the string the definite test inspects. `right` gives
classical D_k (final substring); `left` gives RD_k (initial substring). -/
inductive Edge | left | right
  deriving DecidableEq, Repr

namespace Edge

/-- Take the length-`k` substring at this edge of `xs`. `right` returns
the last `k` symbols; `left` returns the first `k`. Strings shorter than
`k` are returned in full. -/
def takeAt (e : Edge) (k : ℕ) (xs : List α) : List α :=
  match e with
  | .left  => xs.take k
  | .right => xs.drop (xs.length - k)

/-- Edge-parameterized monoid combination. The "anchor" element `x`
sits on the side dictated by `e` (left edge → x is on the left,
right edge → x is on the right); `s` multiplies on the **opposite**
side. Concretely:
* `combine .left  x s = x * s`  (anchor on left, s appended)
* `combine .right x s = s * x`  (anchor on right, s prepended)

This unifies the two structurally-symmetric monoid operations that
appear in Pin's algebraic equations:
* D (definite, suffix-determined) uses `combine .right [αs] s = s · [αs]`
* K (reverse-definite, prefix-determined) uses `combine .left [αs] s = [αs] · s`

The Edge tag selects which edge is "load-bearing" for membership; `s`
is the absorbed element acting from the opposite end. -/
def combine {M : Type*} [Mul M] (e : Edge) (x s : M) : M :=
  match e with
  | .left  => x * s
  | .right => s * x

@[simp] lemma combine_left {M : Type*} [Mul M] (x s : M) :
    Edge.combine .left x s = x * s := rfl

@[simp] lemma combine_right {M : Type*} [Mul M] (x s : M) :
    Edge.combine .right x s = s * x := rfl

end Edge

/-- An **edge-definite `k`-grammar** over `α`: a set of permitted
length-(≤`k`) edge substrings. A string is accepted iff its `Edge`
length-`k` substring is permitted. -/
@[ext]
structure EdgeDefiniteGrammar (k : ℕ) (e : Edge) (α : Type*) where
  /-- The set of permitted length-(≤`k`) edge substrings. -/
  permitted : Set (List α)

namespace EdgeDefiniteGrammar

variable {k : ℕ} {e : Edge}

instance : Inhabited (EdgeDefiniteGrammar k e α) := ⟨⟨Set.univ⟩⟩

/-- The language generated: strings whose `Edge` length-`k` substring
is permitted. -/
def lang (G : EdgeDefiniteGrammar k e α) : Language α := fun w =>
  e.takeAt k w ∈ G.permitted

@[simp] lemma mem_lang (G : EdgeDefiniteGrammar k e α) (w : List α) :
    w ∈ G.lang ↔ e.takeAt k w ∈ G.permitted := Iff.rfl

end EdgeDefiniteGrammar

/-- A **`k`-definite grammar**: edge-definite at the right (final
substring). -/
abbrev DefiniteGrammar (k : ℕ) (α : Type*) := EdgeDefiniteGrammar k .right α

/-- A **reverse `k`-definite grammar**: edge-definite at the left (initial
substring). -/
abbrev ReverseDefiniteGrammar (k : ℕ) (α : Type*) := EdgeDefiniteGrammar k .left α

/-- A language `L` is **`k`-definite** at the right edge iff some
`DefiniteGrammar k α` generates exactly `L`. -/
def IsDefinite (k : ℕ) (L : Language α) : Prop :=
  ∃ G : DefiniteGrammar k α, G.lang = L

/-- A language `L` is **reverse `k`-definite** (left-edge) iff some
`ReverseDefiniteGrammar k α` generates exactly `L`. -/
def IsReverseDefinite (k : ℕ) (L : Language α) : Prop :=
  ∃ G : ReverseDefiniteGrammar k α, G.lang = L

/-! ## Generalised definite (ℒℐ_k) -/

/-- A language `L` is **generalized `k`-definite** iff strings agreeing
on both their length-`k` prefix and length-`k` suffix have the same
membership in `L` ([lambert-2026] Prop 16). Derived predicate: the
class is the conjunction of left-edge and right-edge `k`-definite tests,
no new structural grammar required. -/
def IsGeneralizedDefinite (k : ℕ) (L : Language α) : Prop :=
  ∀ w₁ w₂ : List α,
    Edge.left.takeAt k w₁ = Edge.left.takeAt k w₂ →
    Edge.right.takeAt k w₁ = Edge.right.takeAt k w₂ →
    (w₁ ∈ L ↔ w₂ ∈ L)

/-- **D_k ⊆ ℒℐ_k**: every `k`-definite language is generalized `k`-definite.
The right-edge test alone determines membership, so the joint
prefix-and-suffix hypothesis is more than sufficient. -/
theorem IsDefinite.toIsGeneralizedDefinite {k : ℕ} {L : Language α}
    (h : IsDefinite k L) : IsGeneralizedDefinite k L := by
  obtain ⟨G, rfl⟩ := h
  intro w₁ w₂ _ hsuf
  simp only [EdgeDefiniteGrammar.mem_lang, hsuf]

/-- **RD_k ⊆ ℒℐ_k**: every reverse `k`-definite language is generalized
`k`-definite. -/
theorem IsReverseDefinite.toIsGeneralizedDefinite {k : ℕ} {L : Language α}
    (h : IsReverseDefinite k L) : IsGeneralizedDefinite k L := by
  obtain ⟨G, rfl⟩ := h
  intro w₁ w₂ hpre _
  simp only [EdgeDefiniteGrammar.mem_lang, hpre]

/-! ## Finite or cofinite (𝒩) -/

/-- A language `L` is **finite-or-cofinite** iff either `L` itself is
finite, or its complement `Lᶜ` is finite ([lambert-2026] p. 8 fn 4).
This is the smallest interesting Boolean-closed subregular class:
intersection of the definite and reverse-definite classes for
sufficiently large `k`. -/
def IsFiniteOrCofinite (L : Language α) : Prop :=
  L.Finite ∨ Lᶜ.Finite

/-! ## Co/finite = D ∩ RD (classical Pin/Eilenberg theorem)

A language is finite-or-cofinite iff it is `k`-definite for some `k`
**and** reverse-`k'`-definite for some `k'`. This is a language-level
theorem: pure list combinatorics, no syntactic-monoid content. The
algebraic counterpart (Pin's `𝒩 = ⟦sx^ω = x^ω = x^ω s⟧` characterization)
lives in `SyntacticMonoid/Pin.lean`. -/

/-- A bounded language (every word of length ≤ N) admits a `k`-definite
grammar with `k = N + 1`. Internal helper used for both Finite and
Cofinite halves; the `permitted` set is supplied by the caller. -/
private theorem IsDefinite_of_bounded_aux {L : Language α} {N : ℕ}
    (h_bound : ∀ w ∈ L, w.length ≤ N) :
    IsDefinite (N + 1) L := by
  refine ⟨⟨{ ks : List α | ks.length < N + 1 ∧ ks ∈ L }⟩, ?_⟩
  ext w
  show Edge.right.takeAt (N + 1) w ∈ {ks | ks.length < N + 1 ∧ ks ∈ L} ↔ w ∈ L
  by_cases hw_short : w.length < N + 1
  · have hw_eq : Edge.right.takeAt (N + 1) w = w := by
      show w.drop (w.length - (N + 1)) = w
      have : w.length - (N + 1) = 0 := by omega
      rw [this, List.drop_zero]
    rw [hw_eq]
    exact ⟨And.right, fun hL => ⟨hw_short, hL⟩⟩
  · push_neg at hw_short
    refine ⟨?_, ?_⟩
    · rintro ⟨hlen, _⟩
      have : (Edge.right.takeAt (N + 1) w).length = N + 1 := by
        show (w.drop (w.length - (N + 1))).length = N + 1
        rw [List.length_drop]; omega
      omega
    · intro hL
      have := h_bound w hL
      omega

/-- Mirror for the left edge. -/
private theorem IsReverseDefinite_of_bounded_aux {L : Language α} {N : ℕ}
    (h_bound : ∀ w ∈ L, w.length ≤ N) :
    IsReverseDefinite (N + 1) L := by
  refine ⟨⟨{ ks : List α | ks.length < N + 1 ∧ ks ∈ L }⟩, ?_⟩
  ext w
  show Edge.left.takeAt (N + 1) w ∈ {ks | ks.length < N + 1 ∧ ks ∈ L} ↔ w ∈ L
  by_cases hw_short : w.length < N + 1
  · have hw_eq : Edge.left.takeAt (N + 1) w = w :=
      List.take_of_length_le (le_of_lt hw_short)
    rw [hw_eq]
    exact ⟨And.right, fun hL => ⟨hw_short, hL⟩⟩
  · push_neg at hw_short
    refine ⟨?_, ?_⟩
    · rintro ⟨hlen, _⟩
      have : (Edge.left.takeAt (N + 1) w).length = N + 1 := by
        show (w.take (N + 1)).length = N + 1
        rw [List.length_take]; omega
      omega
    · intro hL
      have := h_bound w hL
      omega

/-- A "co-bounded" language (complement bounded) admits a `k`-definite
grammar where the `permitted` set accepts all length-`k` suffixes. -/
private theorem IsDefinite_of_cobounded_aux {L : Language α} {N : ℕ}
    (h_bound : ∀ w ∈ Lᶜ, w.length ≤ N) :
    IsDefinite (N + 1) L := by
  refine ⟨⟨{ ks : List α |
    (ks.length < N + 1 ∧ ks ∈ L) ∨ ks.length = N + 1 }⟩, ?_⟩
  ext w
  show Edge.right.takeAt (N + 1) w ∈
       {ks | (ks.length < N + 1 ∧ ks ∈ L) ∨ ks.length = N + 1} ↔ w ∈ L
  by_cases hw_short : w.length < N + 1
  · have hw_eq : Edge.right.takeAt (N + 1) w = w := by
      show w.drop (w.length - (N + 1)) = w
      have : w.length - (N + 1) = 0 := by omega
      rw [this, List.drop_zero]
    rw [hw_eq]
    refine ⟨?_, fun hL => Or.inl ⟨hw_short, hL⟩⟩
    rintro (⟨_, hL⟩ | hlen)
    · exact hL
    · omega
  · push_neg at hw_short
    refine ⟨?_, ?_⟩
    · intro _
      by_contra hcontra
      have hLc : w ∈ Lᶜ := hcontra
      have := h_bound w hLc
      omega
    · intro _
      right
      show (Edge.right.takeAt (N + 1) w).length = N + 1
      show (w.drop (w.length - (N + 1))).length = N + 1
      rw [List.length_drop]; omega

private theorem IsReverseDefinite_of_cobounded_aux {L : Language α} {N : ℕ}
    (h_bound : ∀ w ∈ Lᶜ, w.length ≤ N) :
    IsReverseDefinite (N + 1) L := by
  refine ⟨⟨{ ks : List α |
    (ks.length < N + 1 ∧ ks ∈ L) ∨ ks.length = N + 1 }⟩, ?_⟩
  ext w
  show Edge.left.takeAt (N + 1) w ∈
       {ks | (ks.length < N + 1 ∧ ks ∈ L) ∨ ks.length = N + 1} ↔ w ∈ L
  by_cases hw_short : w.length < N + 1
  · have hw_eq : Edge.left.takeAt (N + 1) w = w :=
      List.take_of_length_le (le_of_lt hw_short)
    rw [hw_eq]
    refine ⟨?_, fun hL => Or.inl ⟨hw_short, hL⟩⟩
    rintro (⟨_, hL⟩ | hlen)
    · exact hL
    · omega
  · push_neg at hw_short
    refine ⟨?_, ?_⟩
    · intro _
      by_contra hcontra
      have hLc : w ∈ Lᶜ := hcontra
      have := h_bound w hLc
      omega
    · intro _
      right
      show (Edge.left.takeAt (N + 1) w).length = N + 1
      show (w.take (N + 1)).length = N + 1
      rw [List.length_take]; omega

/-- A finite set of words has a length bound. Bridges the
`Set.Finite`/`Finite ↑·` representation issue by going through
`Set.Finite.image` with an explicit `Set.Finite` annotation. -/
private theorem exists_length_bound_of_finite {S : Set (List α)}
    (h : S.Finite) : ∃ N, ∀ w ∈ S, w.length ≤ N := by
  classical
  have h_set : Set.Finite S := h
  obtain ⟨N, hN⟩ := (Set.Finite.image (·.length) h_set).exists_le
  exact ⟨N, fun w hw => hN _ ⟨w, hw, rfl⟩⟩

/-- **Forward direction of Pin's `𝒩 = 𝒟 ∩ 𝒦` theorem**: a finite-or-cofinite
language is both `k`-definite and reverse-`k'`-definite for some `k`, `k'`. -/
theorem IsFiniteOrCofinite.exists_isDefinite_and_isReverseDefinite
    {L : Language α} (h : IsFiniteOrCofinite L) :
    (∃ k, IsDefinite k L) ∧ (∃ k', IsReverseDefinite k' L) := by
  rcases h with h | h
  · obtain ⟨N, hN⟩ := exists_length_bound_of_finite h
    exact ⟨⟨N + 1, IsDefinite_of_bounded_aux hN⟩,
           ⟨N + 1, IsReverseDefinite_of_bounded_aux hN⟩⟩
  · obtain ⟨N, hN⟩ := exists_length_bound_of_finite h
    exact ⟨⟨N + 1, IsDefinite_of_cobounded_aux hN⟩,
           ⟨N + 1, IsReverseDefinite_of_cobounded_aux hN⟩⟩

/-- Helper: bridge two long words via `w' = w₂.take k' ++ w₁.drop (w₁.length - k)`.
The bridge has length `k' + k`, shares the right-`k`-suffix with `w₁`,
and shares the left-`k'`-prefix with `w₂`. -/
private lemma takeAt_right_eq_of_bridge {α : Type*} {k k' : ℕ}
    {w₁ w₂ : List α} (hw₁ : k ≤ w₁.length) (hw₂ : k' ≤ w₂.length) :
    Edge.right.takeAt k (w₂.take k' ++ w₁.drop (w₁.length - k)) =
    Edge.right.takeAt k w₁ := by
  show (w₂.take k' ++ w₁.drop (w₁.length - k)).drop
        ((w₂.take k' ++ w₁.drop (w₁.length - k)).length - k) =
       w₁.drop (w₁.length - k)
  have h_take_len : (w₂.take k').length = k' := by
    rw [List.length_take]; omega
  have h_drop_len : (w₁.drop (w₁.length - k)).length = k := by
    rw [List.length_drop]; omega
  have h_total : (w₂.take k' ++ w₁.drop (w₁.length - k)).length = k' + k := by
    rw [List.length_append, h_take_len, h_drop_len]
  have hlen_diff :
      (w₂.take k' ++ w₁.drop (w₁.length - k)).length - k = k' := by
    rw [h_total]; omega
  rw [hlen_diff]
  exact List.drop_left' h_take_len

private lemma takeAt_left_eq_of_bridge {α : Type*} {k k' : ℕ}
    {w₁ w₂ : List α} (_hw₁ : k ≤ w₁.length) (hw₂ : k' ≤ w₂.length) :
    Edge.left.takeAt k' (w₂.take k' ++ w₁.drop (w₁.length - k)) =
    Edge.left.takeAt k' w₂ := by
  show (w₂.take k' ++ w₁.drop (w₁.length - k)).take k' = w₂.take k'
  have h_take_len : (w₂.take k').length = k' := by
    rw [List.length_take]; omega
  rw [List.take_append_of_le_length (by rw [h_take_len])]
  rw [List.take_take]
  congr 1; omega

/-- **Reverse direction of Pin's `𝒩 = 𝒟 ∩ 𝒦` theorem (α-finite case)**:
if `L` is both `k`-definite and reverse-`k'`-definite, AND the alphabet
is finite, then `L` is finite-or-cofinite.

The α-finiteness hypothesis is necessary: with infinite α, words of
bounded length need not form a finite set. The phonology context
([lambert-2026]) implicitly assumes finite alphabets.

Proof sketch: for words of length `≥ k + k'`, membership is constant.
Bridge argument: any two such words `w₁`, `w₂` are related via
`w' = w₂.take k' ++ w₁.drop (w₁.length - k)` of length `k' + k`. By
`k`-definiteness applied to (w₁, w'), they share L-membership; by
reverse-`k'`-definiteness applied to (w', w₂), they share L-membership.
Then either all long words are in `L` (so `Lᶜ` is bounded, hence finite)
or none are (so `L` is bounded). -/
theorem isFiniteOrCofinite_of_isDefinite_and_isReverseDefinite [Finite α]
    {L : Language α}
    (h : (∃ k, IsDefinite k L) ∧ (∃ k', IsReverseDefinite k' L)) :
    IsFiniteOrCofinite L := by
  classical
  obtain ⟨⟨k, GD, hGD⟩, ⟨k', GR, hGR⟩⟩ := h
  -- Constancy: for w₁, w₂ both of length ≥ k + k', w₁ ∈ L ↔ w₂ ∈ L.
  have constancy : ∀ w₁ w₂ : List α,
      k + k' ≤ w₁.length → k + k' ≤ w₂.length → (w₁ ∈ L ↔ w₂ ∈ L) := by
    intro w₁ w₂ hw₁ hw₂
    set w' := w₂.take k' ++ w₁.drop (w₁.length - k) with hw'_def
    have hk_le_w₁ : k ≤ w₁.length := by omega
    have hk'_le_w₂ : k' ≤ w₂.length := by omega
    have h_right : Edge.right.takeAt k w' = Edge.right.takeAt k w₁ :=
      takeAt_right_eq_of_bridge hk_le_w₁ hk'_le_w₂
    have h_left : Edge.left.takeAt k' w' = Edge.left.takeAt k' w₂ :=
      takeAt_left_eq_of_bridge hk_le_w₁ hk'_le_w₂
    have hw₁_iff_w' : w₁ ∈ L ↔ w' ∈ L := by
      rw [← hGD]; show _ ∈ GD.permitted ↔ _ ∈ GD.permitted; rw [h_right]
    have hw'_iff_w₂ : w' ∈ L ↔ w₂ ∈ L := by
      rw [← hGR]; show _ ∈ GR.permitted ↔ _ ∈ GR.permitted; rw [h_left]
    exact hw₁_iff_w'.trans hw'_iff_w₂
  -- For α finite, the set of words of length < k + k' is finite.
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
    -- w of length ≥ k+k', and w₀ ∈ L of length ≥ k+k'. By constancy, w ∈ L.
    -- But hwLc says w ∈ Lᶜ, contradiction.
    exact hwLc ((constancy w w₀ hge hw₀_len).mpr hw₀_L)
  · left
    push_neg at h_witness
    apply Set.Finite.subset h_short_finite
    intro w hwL
    show w.length < k + k'
    by_contra hge
    push_neg at hge
    exact h_witness w hge hwL

/-- **Pin's `𝒩 = 𝒟 ∩ 𝒦` theorem (α-finite case)**: a language over a
finite alphabet is finite-or-cofinite iff it is both `k`-definite for
some `k` **and** reverse-`k'`-definite for some `k'`. -/
theorem isFiniteOrCofinite_iff_exists_isDefinite_and_isReverseDefinite [Finite α]
    {L : Language α} :
    IsFiniteOrCofinite L ↔
    (∃ k, IsDefinite k L) ∧ (∃ k', IsReverseDefinite k' L) :=
  ⟨IsFiniteOrCofinite.exists_isDefinite_and_isReverseDefinite,
   isFiniteOrCofinite_of_isDefinite_and_isReverseDefinite⟩

end Core.Computability.Subregular
