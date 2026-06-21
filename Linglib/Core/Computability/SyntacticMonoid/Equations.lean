/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Language
import Linglib.Core.Computability.SyntacticMonoid
import Linglib.Core.Computability.Subregular.Language.Definite
import Linglib.Core.Data.List.DropRight

/-!
# Equational characterizations of subregular language classes

[lambert-2026] §6.2 (paper p. 22-25, with summary in Table 6 p. 28)
characterizes each base-class of subregular languages by a system of
equations on the *syntactic semigroup*: `D = ⟦sx^ω = x^ω⟧`,
`K = ⟦x^ω y = x^ω⟧`, `LI = ⟦x^ω y x^ω = x^ω⟧`, `N = ⟦x^ω y = x^ω;
yx^ω = x^ω⟧` (definite, reverse-definite, generalized-definite,
co/finite, respectively).

This file lands the **`k`-definite case** (Lambert Prop 53, p. 23) as a
feasibility probe — the simplest entry into Lambert's algebraic story
because it requires no `omegaPow` (idempotent power) machinery.
Lambert's claim:

> A language is `k`-definite if and only if it is in
> `⟦sx₁ … xₖ = x₁ … xₖ⟧`.

## Mathlib precedent: monoid + length-`k` letter-sequence variables

Lambert's syntactic *semigroup* excludes the empty word; our
`Language.syntacticMonoid L` (built via `Con (FreeMonoid α)`, see
`SyntacticMonoid.lean`) includes the identity (the class of the empty
word). Mathlib's `Con.Quotient` precedent gives us a `Monoid`, not a
`Semigroup`; there is no established mathlib `syntacticSemigroup`
pattern. **We follow mathlib precedent and keep the `Monoid` setting.**

### Letter-sequence quantification (not arbitrary monoid elements)

To recover Lambert's intended characterization in the monoid setting,
the equation quantifies `x₁, …, xₖ` over **length-`k` letter sequences**
in the alphabet `α` rather than over arbitrary syntactic-monoid
elements. This is the "generators" interpretation: the equation says
"prepending any prefix to a length-`k` letter sequence preserves its
syntactic class".

The naïve pure-monoid form
`∀ s ≠ 1, ∀ xs : List M of length k, (∀ x ∈ xs, x ≠ 1) →
   s * xs.prod = xs.prod`
is **strictly weaker** and does not characterize `k`-definite. Concrete
counterexample: take `L = (a|b)*` over the alphabet `{a, b, c}` —
membership is "no `c` anywhere". Then `[a] = [b] = 1` in the syntactic
monoid (inserting `a` or `b` anywhere preserves "no `c`"), and the
syntactic monoid is the rank-2 lattice `M = {1, 0}` with `0 = [c]`
absorbing. The pure-monoid equation trivially holds: the only
non-identity element is `0`, and `0 * 0 = 0`. Yet `L` is not
`k`-definite for any `k` — the words `c·a^k` and `a^k` share the
length-`k` suffix `a^k` but only the latter is in `L`.

The letter-sequence formulation rules this out: for `αs = [a]` of
length 1, the syntactic class of `αs` is `1` in `M`, and the equation
`s * 1 = 1` forces `s = 1`, which fails for `s = [c] = 0`. So the
equation correctly detects that `L` is not 1-definite.

(Lambert's semigroup version sidesteps the trivial-letter issue
because his syntactic semigroup is generated only by the *non-trivial*
letter classes, implicitly ignoring L-trivial letters in the alphabet.
The letter-sequence monoid form makes this explicit.)

## Main definitions

* `Language.kDefiniteEquation L k` — the equation
  `∀ s ∈ L.syntacticMonoid, ∀ αs : List α with αs.length = k,
  s * [αs] = [αs]`. The product on the left is monoid multiplication
  in `L.syntacticMonoid`; `[αs]` denotes
  `L.toSyntacticMonoid (FreeMonoid.ofList αs)`.

## Main results

* `Language.IsDefinite.satisfies_kDefiniteEquation` — **forward
  direction**: a `k`-definite language's syntactic monoid satisfies
  the equation. Proof: extract a `FreeMonoid α` representative `w` of
  `s`; the equation reduces to `SyntacticEquiv L (w ++ αs) αs`, which
  follows from `takeAt_right_append_left_absorb` (since `|αs| = k`,
  the length-`k` suffix of `x ++ w ++ αs ++ y` already discards `w`).

* `Language.isDefinite_of_satisfies_kDefiniteEquation` — **reverse
  direction**: the equation implies `k`-definiteness. Construction:
  `G.permitted := { Edge.right.takeAt k w | w ∈ L }`. The trivial
  inclusion `L ⊆ G.lang` holds with witness `w' = w`. The reverse
  inclusion `G.lang ⊆ L` is by case analysis on word length: short
  words equal their own suffix (forcing equality); long words decompose
  as `prefix ++ ks` and the equation gives `SyntacticEquiv L w ks`,
  then `L`-saturation closes the case.

* `Language.isDefinite_iff_satisfies_kDefiniteEquation` — Lambert
  Prop 53 bidirectional bundling.

In the same file, Lambert Prop 57 (reverse-definite, K) and Prop 58
(generalized definite, ℒℐ) are also landed using the same letter-sequence
template. The Pin omega-power forms (`Pin.lean`) consume these finite-`k`
iffs to derive their own iffs.

## Out of scope (queued for follow-up files)

* `multitier ℬ𝒯C` extensions ([lambert-2026] §6.3, Table 6 right
  column).

## References

* [lambert-2026] §6.2, Prop 53 (paper p. 23).
* [straubing-1985], [almeida-1995] — the equational-class
  framework Lambert builds on.
-/

open _root_.Subregular

namespace Language

/-- **Lambert (2026) Prop 53 equation** (length-`k` letter-sequence form):
for any element `s` of `L.syntacticMonoid` and any length-`k` letter
sequence `αs : List α`, prepending `s` to the syntactic class of `αs`
preserves it.

The variables `x₁, …, xₖ` of Lambert's notation
`⟦sx₁ … xₖ = x₁ … xₖ⟧` are instantiated by the letters of `αs`,
each `xᵢ` as the syntactic class of a single letter, so the product
`x₁ ⋯ xₖ` corresponds to the syntactic class of `αs`. See file
docstring for the rationale: the alternative pure-monoid form
quantifying over arbitrary `xs : List M` is strictly weaker and
fails to characterize `k`-definite. -/
def kDefiniteEquation {α : Type*} (L : Language α) (k : ℕ) : Prop :=
  ∀ (s : L.syntacticMonoid) (αs : List α), αs.length = k →
    s * L.toSyntacticMonoid (FreeMonoid.ofList αs) =
    L.toSyntacticMonoid (FreeMonoid.ofList αs)

variable {α : Type*}

-- ============================================================================
-- §1. Helper lemmas on `Edge.right.takeAt`
-- ============================================================================

/-- The right-`k`-suffix of `x ++ rest` equals the right-`k`-suffix of `rest`
whenever `rest.length ≥ k` — the `Edge.takeAt` view of
`List.rtake_append_of_le_length`. -/
lemma takeAt_right_append_left_absorb {α : Type*}
    (x rest : List α) {k : ℕ} (h : k ≤ rest.length) :
    Edge.right.takeAt k (x ++ rest) = Edge.right.takeAt k rest :=
  List.rtake_append_of_le_length x rest h

-- ============================================================================
-- §2. Lifting the equation to `SyntacticEquiv`
-- ============================================================================

/-- Under the `k`-definite equation, prepending any prefix to a
length-`k` word gives a syntactically equivalent word.

This is the algebraic heart of the reverse direction: applying the
equation at `s = [w]` and unfolding
`L.toSyntacticMonoid (w * αs) = L.toSyntacticMonoid w *
L.toSyntacticMonoid αs` gives the syntactic-monoid equality
`[w * αs] = [αs]`, which lifts via `Quotient.exact` to the two-sided
syntactic equivalence on the underlying lists. -/
lemma syntacticEquiv_of_kDefiniteEquation {L : Language α} {k : ℕ}
    (h : Language.kDefiniteEquation L k)
    (w αs : List α) (hαs_len : αs.length = k) :
    SyntacticEquiv L (w ++ αs) αs := by
  have h_eq :=
    h (L.toSyntacticMonoid (FreeMonoid.ofList w)) αs hαs_len
  have h_pre :
      L.toSyntacticMonoid (FreeMonoid.ofList (w ++ αs)) =
      L.toSyntacticMonoid (FreeMonoid.ofList αs) := by
    rw [FreeMonoid.ofList_append, MonoidHom.map_mul]
    exact h_eq
  exact Quotient.exact h_pre

-- ============================================================================
-- §3. Lambert Prop 53 — both directions
-- ============================================================================

/-- **Lambert Prop 53 (forward direction)**: a `k`-definite language's
syntactic monoid satisfies the `k`-definite equation: prepending any
syntactic-monoid element `s` to a length-`k` letter sequence `αs`
preserves the syntactic class of `αs`. -/
theorem IsDefinite.satisfies_kDefiniteEquation
    {L : Language α} {k : ℕ} (hL : L.IsDefinite k) :
    Language.kDefiniteEquation L k := by
  intro s αs hαs_len
  obtain ⟨w, hw⟩ := Quotient.exists_rep s
  rw [show s = L.toSyntacticMonoid w from hw.symm, ← MonoidHom.map_mul]
  apply Quotient.sound
  intro x y
  show x ++ FreeMonoid.toList (w * FreeMonoid.ofList αs) ++ y ∈ L ↔
       x ++ FreeMonoid.toList (FreeMonoid.ofList αs) ++ y ∈ L
  have hwmul : FreeMonoid.toList (w * FreeMonoid.ofList αs) =
               FreeMonoid.toList w ++ αs := rfl
  have hαsId : FreeMonoid.toList (FreeMonoid.ofList αs) = αs := rfl
  rw [hwmul, hαsId]
  refine hL.iff ?_
  rw [show x ++ (FreeMonoid.toList w ++ αs) ++ y =
          (x ++ FreeMonoid.toList w) ++ (αs ++ y) by simp [List.append_assoc],
      show x ++ αs ++ y = x ++ (αs ++ y) by simp [List.append_assoc]]
  have h_combined_len : k ≤ (αs ++ y).length := by
    rw [List.length_append]; omega
  rw [takeAt_right_append_left_absorb (x ++ FreeMonoid.toList w)
        (αs ++ y) h_combined_len,
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
   the equation to get `SyntacticEquiv L w u`; saturation closes.
3. `u.length > k`, `w.length ≤ k`: symmetric to (2).
4. Both `u.length > k`, `w.length > k`: both decompose as
   `prefix ++ ks` for the shared length-`k` suffix `ks`. Apply
   equation to both, getting `SyntacticEquiv L w ks` and
   `SyntacticEquiv L u ks`; chain transitively, then saturation. -/
theorem isDefinite_of_satisfies_kDefiniteEquation
    {L : Language α} {k : ℕ}
    (h : Language.kDefiniteEquation L k) :
    L.IsDefinite k := by
  -- Membership equals membership of the length-`k` suffix: short words are their
  -- own suffix; long words are syntactically equivalent to it via the equation.
  have key : ∀ w : List α, w ∈ L ↔ Edge.right.takeAt k w ∈ L := by
    intro w
    by_cases hw : w.length ≤ k
    · rw [Edge.takeAt_right, List.rtake_of_length_le hw]
    · push_neg at hw
      have hlen : (Edge.right.takeAt k w).length = k := by
        rw [Edge.takeAt_right, List.length_rtake]; omega
      have hequiv : SyntacticEquiv L w (Edge.right.takeAt k w) := by
        have base := syntacticEquiv_of_kDefiniteEquation h
          (w.take (w.length - k)) (Edge.right.takeAt k w) hlen
        have decomp : w = w.take (w.length - k) ++ Edge.right.takeAt k w :=
          (List.rdrop_append_rtake w k).symm
        rwa [← decomp] at base
      exact mem_iff_of_syntacticEquiv hequiv
  exact Language.invariantUnder_iff.mpr fun a b hab => by rw [key a, key b, hab]

/-- **Lambert (2026) Prop 53**: a language is `k`-definite iff its
syntactic monoid satisfies the `k`-definite equation. Bidirectional
bundling of `IsDefinite.satisfies_kDefiniteEquation` and
`isDefinite_of_satisfies_kDefiniteEquation`. -/
theorem isDefinite_iff_satisfies_kDefiniteEquation
    {L : Language α} {k : ℕ} :
    L.IsDefinite k ↔ Language.kDefiniteEquation L k :=
  ⟨IsDefinite.satisfies_kDefiniteEquation,
   isDefinite_of_satisfies_kDefiniteEquation⟩

-- ============================================================================
-- §4. Lambert Prop 57 — reverse-definite (mirror of D)
-- ============================================================================

/-- **Lambert (2026) Prop 57 equation** for **reverse-definite**
languages (length-`k` letter-sequence, monoid form): for any element
`s` of the syntactic monoid and any length-`k` letter sequence `αs`,
**post**-multiplying `[αs]` by `s` preserves it. Mirror of
`kDefiniteEquation` with right-multiplication instead of left.

Lambert's notation: `𝒦_k = ⟦x₁ ⋯ xₖ s = x₁ ⋯ xₖ⟧` (paper Prop 57). -/
def kReverseDefiniteEquation (L : Language α) (k : ℕ) : Prop :=
  ∀ (s : L.syntacticMonoid) (αs : List α), αs.length = k →
    L.toSyntacticMonoid (FreeMonoid.ofList αs) * s =
    L.toSyntacticMonoid (FreeMonoid.ofList αs)

-- §4.1. Helper lemmas on `Edge.left.takeAt` (mirror of §1)

/-- The left-`k`-prefix of `xs ++ y` equals the left-`k`-prefix of
`xs` whenever `xs.length ≥ k`. -/
private lemma takeAt_left_append_right_absorb {α : Type*}
    (xs y : List α) {k : ℕ} (h : k ≤ xs.length) :
    Edge.left.takeAt k (xs ++ y) = Edge.left.takeAt k xs := by
  show (xs ++ y).take k = xs.take k
  exact List.take_append_of_le_length h

/-- When `xs.length ≤ k`, the left-`k`-prefix of `xs` is `xs` itself. -/
private lemma takeAt_left_of_short {α : Type*} {k : ℕ} {xs : List α}
    (h : xs.length ≤ k) : Edge.left.takeAt k xs = xs := by
  show xs.take k = xs
  exact List.take_of_length_le h

/-- When `xs.length ≥ k`, the left-`k`-prefix of `xs` has length exactly `k`. -/
private lemma takeAt_left_length_of_long {α : Type*} {k : ℕ} {xs : List α}
    (h : k ≤ xs.length) : (Edge.left.takeAt k xs).length = k := by
  show (xs.take k).length = k
  rw [List.length_take]; omega

/-- A list `xs` of length `≥ k` decomposes as
`Edge.left.takeAt k xs ++ xs.drop k`. -/
private lemma decompose_at_left_takeAt {α : Type*} {k : ℕ} {xs : List α}
    (_h : k ≤ xs.length) :
    xs = Edge.left.takeAt k xs ++ xs.drop k := by
  show xs = xs.take k ++ xs.drop k
  exact (List.take_append_drop _ _).symm

-- §4.2. Lifting the K equation to `SyntacticEquiv`

/-- Under the reverse-`k`-definite equation, **appending** any suffix to
a length-`k` word gives a syntactically equivalent word. Mirror of
`syntacticEquiv_of_kDefiniteEquation`. -/
lemma syntacticEquiv_of_kReverseDefiniteEquation {L : Language α} {k : ℕ}
    (h : Language.kReverseDefiniteEquation L k)
    (αs w : List α) (hαs_len : αs.length = k) :
    SyntacticEquiv L (αs ++ w) αs := by
  have h_eq :=
    h (L.toSyntacticMonoid (FreeMonoid.ofList w)) αs hαs_len
  have h_pre :
      L.toSyntacticMonoid (FreeMonoid.ofList (αs ++ w)) =
      L.toSyntacticMonoid (FreeMonoid.ofList αs) := by
    rw [FreeMonoid.ofList_append, MonoidHom.map_mul]
    exact h_eq
  exact Quotient.exact h_pre

-- §4.3. Lambert Prop 57 — both directions

/-- **Lambert Prop 57 (forward direction)**: a reverse-`k`-definite
language's syntactic monoid satisfies the reverse-`k`-definite equation. -/
theorem IsReverseDefinite.satisfies_kReverseDefiniteEquation
    {L : Language α} {k : ℕ} (hL : L.IsReverseDefinite k) :
    Language.kReverseDefiniteEquation L k := by
  intro s αs hαs_len
  obtain ⟨w, hw⟩ := Quotient.exists_rep s
  rw [show s = L.toSyntacticMonoid w from hw.symm, ← MonoidHom.map_mul]
  apply Quotient.sound
  intro x y
  show x ++ FreeMonoid.toList (FreeMonoid.ofList αs * w) ++ y ∈ L ↔
       x ++ FreeMonoid.toList (FreeMonoid.ofList αs) ++ y ∈ L
  have hwmul : FreeMonoid.toList (FreeMonoid.ofList αs * w) =
               αs ++ FreeMonoid.toList w := rfl
  have hαsId : FreeMonoid.toList (FreeMonoid.ofList αs) = αs := rfl
  rw [hwmul, hαsId]
  refine hL.iff ?_
  rw [show x ++ (αs ++ FreeMonoid.toList w) ++ y =
          (x ++ αs) ++ (FreeMonoid.toList w ++ y) by simp [List.append_assoc],
      show x ++ αs ++ y = (x ++ αs) ++ y from by simp [List.append_assoc]]
  have h_combined_len : k ≤ (x ++ αs).length := by
    rw [List.length_append]; omega
  rw [takeAt_left_append_right_absorb (x ++ αs)
        (FreeMonoid.toList w ++ y) h_combined_len,
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
    · rw [takeAt_left_of_short hw]
    · push_neg at hw
      have hlen : (Edge.left.takeAt k w).length = k :=
        takeAt_left_length_of_long (le_of_lt hw)
      have hequiv : SyntacticEquiv L w (Edge.left.takeAt k w) := by
        have base := syntacticEquiv_of_kReverseDefiniteEquation h
          (Edge.left.takeAt k w) (w.drop k) hlen
        rwa [← decompose_at_left_takeAt (le_of_lt hw)] at base
      exact mem_iff_of_syntacticEquiv hequiv
  exact Language.invariantUnder_iff.mpr fun a b hab => by rw [key a, key b, hab]

/-- **Lambert (2026) Prop 57**: a language is reverse-`k`-definite iff
its syntactic monoid satisfies the reverse-`k`-definite equation. -/
theorem isReverseDefinite_iff_satisfies_kReverseDefiniteEquation
    {L : Language α} {k : ℕ} :
    L.IsReverseDefinite k ↔ Language.kReverseDefiniteEquation L k :=
  ⟨IsReverseDefinite.satisfies_kReverseDefiniteEquation,
   isReverseDefinite_of_satisfies_kReverseDefiniteEquation⟩

-- ============================================================================
-- §5. Lambert Prop 58 — generalized definite (sandwich form)
-- ============================================================================

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
    L.toSyntacticMonoid (FreeMonoid.ofList αs) * s *
    L.toSyntacticMonoid (FreeMonoid.ofList αs) =
    L.toSyntacticMonoid (FreeMonoid.ofList αs)


-- §5.1. Lifting LI equation to `SyntacticEquiv`

/-- Under the LI equation, sandwiching any word `w` between two copies
of a length-`k` word `αs` is syntactically equivalent to `αs` alone. -/
lemma syntacticEquiv_of_kGeneralizedDefiniteEquation
    {L : Language α} {k : ℕ}
    (h : Language.kGeneralizedDefiniteEquation L k)
    (αs w : List α) (hαs_len : αs.length = k) :
    SyntacticEquiv L (αs ++ w ++ αs) αs := by
  have h_eq :=
    h (L.toSyntacticMonoid (FreeMonoid.ofList w)) αs hαs_len
  have h_pre :
      L.toSyntacticMonoid (FreeMonoid.ofList (αs ++ w ++ αs)) =
      L.toSyntacticMonoid (FreeMonoid.ofList αs) := by
    rw [FreeMonoid.ofList_append, FreeMonoid.ofList_append, MonoidHom.map_mul,
        MonoidHom.map_mul]
    exact h_eq
  exact Quotient.exact h_pre

-- §5.2. Lambert Prop 58 — forward direction

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
  obtain ⟨w, hw⟩ := Quotient.exists_rep s
  rw [show s = L.toSyntacticMonoid w from hw.symm]
  rw [show L.toSyntacticMonoid (FreeMonoid.ofList αs) * L.toSyntacticMonoid w *
        L.toSyntacticMonoid (FreeMonoid.ofList αs) =
      L.toSyntacticMonoid (FreeMonoid.ofList αs * w * FreeMonoid.ofList αs) by
    rw [MonoidHom.map_mul, MonoidHom.map_mul]]
  apply Quotient.sound
  intro x y
  show x ++ FreeMonoid.toList (FreeMonoid.ofList αs * w * FreeMonoid.ofList αs) ++ y ∈ L ↔
       x ++ FreeMonoid.toList (FreeMonoid.ofList αs) ++ y ∈ L
  -- Both sides reduce to checking IsGeneralizedDefinite on appropriate words.
  have hwmul : FreeMonoid.toList (FreeMonoid.ofList αs * w * FreeMonoid.ofList αs) =
               αs ++ FreeMonoid.toList w ++ αs := rfl
  have hαsId : FreeMonoid.toList (FreeMonoid.ofList αs) = αs := rfl
  rw [hwmul, hαsId]
  -- Apply IsGenDef to (x ++ αs ++ toList w ++ αs ++ y, x ++ αs ++ y).
  apply isGeneralizedDefinite_iff_edges.mp hL
  · -- takeAt_left k matches: both have x ++ αs as prefix.
    show (x ++ (αs ++ FreeMonoid.toList w ++ αs) ++ y).take k =
         (x ++ αs ++ y).take k
    rw [show x ++ (αs ++ FreeMonoid.toList w ++ αs) ++ y =
            (x ++ αs) ++ (FreeMonoid.toList w ++ αs ++ y) by
          simp [List.append_assoc],
        show x ++ αs ++ y = (x ++ αs) ++ y from by simp [List.append_assoc]]
    have h_xαs_len : k ≤ (x ++ αs).length := by
      rw [List.length_append]; omega
    rw [List.take_append_of_le_length h_xαs_len,
        List.take_append_of_le_length h_xαs_len]
  · -- takeAt_right k matches: both end with αs ++ y.
    show Edge.right.takeAt k (x ++ (αs ++ FreeMonoid.toList w ++ αs) ++ y) =
         Edge.right.takeAt k (x ++ αs ++ y)
    rw [show x ++ (αs ++ FreeMonoid.toList w ++ αs) ++ y =
            (x ++ αs ++ FreeMonoid.toList w) ++ (αs ++ y) by
          simp [List.append_assoc],
        show x ++ αs ++ y = x ++ (αs ++ y) by simp [List.append_assoc]]
    have h_αsy_len : k ≤ (αs ++ y).length := by
      rw [List.length_append]; omega
    rw [takeAt_right_append_left_absorb (x ++ αs ++ FreeMonoid.toList w)
          (αs ++ y) h_αsy_len,
        takeAt_right_append_left_absorb x (αs ++ y) h_αsy_len]

-- §5.3. Lambert Prop 58 — reverse direction

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
      show (w₁.take k).length = k
      rw [List.length_take]; omega
    have hw₂_long : k ≤ w₂.length := by
      have h_pre_len_w₂ : (Edge.left.takeAt k w₂).length = k := by
        rw [← hpre]; exact h_pre_len_w₁
      have : (w₂.take k).length = k := h_pre_len_w₂
      rw [List.length_take] at this; omega
    -- Set up αs, βs, b_i, c_i and the two decompositions of each wᵢ.
    set αs := Edge.left.takeAt k w₁ with hαs_def
    set βs := Edge.right.takeAt k w₁ with hβs_def
    have hαs_len : αs.length = k := h_pre_len_w₁
    have hβs_len : βs.length = k := by
      show (w₁.drop (w₁.length - k)).length = k
      rw [List.length_drop]; omega
    set b₁ := w₁.drop k with hb₁_def
    set b₂ := w₂.drop k with hb₂_def
    set c₁ := w₁.take (w₁.length - k) with hc₁_def
    set c₂ := w₂.take (w₂.length - k) with hc₂_def
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
    -- Way 1: αs-sandwich gives `(w₁ ++ w₂) ≡_L w₂`.
    have h_αs_eq : SyntacticEquiv L (w₁ ++ w₂) w₂ := by
      rw [hw₁_αs, hw₂_αs]
      intro x y
      -- Apply (αs ++ b₁ ++ αs) ≡_L αs at context (x, b₂ ++ y).
      have h_inner := syntacticEquiv_of_kGeneralizedDefiniteEquation
        h αs b₁ hαs_len x (b₂ ++ y)
      simp only [List.append_assoc] at h_inner ⊢
      exact h_inner
    -- Way 2: βs-sandwich gives `(w₁ ++ w₂) ≡_L w₁`.
    have h_βs_eq : SyntacticEquiv L (w₁ ++ w₂) w₁ := by
      rw [hw₁_βs, hw₂_βs]
      intro x y
      -- Apply (βs ++ c₂ ++ βs) ≡_L βs at context (x ++ c₁, y).
      have h_inner := syntacticEquiv_of_kGeneralizedDefiniteEquation
        h βs c₂ hβs_len (x ++ c₁) y
      simp only [List.append_assoc] at h_inner ⊢
      exact h_inner
    -- Combine: w₁ ≡_L w₂.
    have hequiv : SyntacticEquiv L w₁ w₂ := h_βs_eq.symm.trans h_αs_eq
    exact mem_iff_of_syntacticEquiv hequiv
  · -- Short case: `|w₁| < k`. Then `Edge.left.takeAt k w₁ = w₁`, so
    -- the prefix equality yields `w₁ = Edge.left.takeAt k w₂`, which
    -- forces `|w₂| ≤ k` (otherwise the takeAt has length `k > |w₁|`).
    push_neg at hw₁_long
    have h_w₁_pre : Edge.left.takeAt k w₁ = w₁ := by
      show w₁.take k = w₁
      exact List.take_of_length_le (le_of_lt hw₁_long)
    rw [h_w₁_pre] at hpre
    -- Now hpre : w₁ = Edge.left.takeAt k w₂.
    by_cases hw₂_long : k ≤ w₂.length
    · -- Length-`k` takeAt of `w₂` has length `k > |w₁|`. Contradicts hpre.
      have h_pre_len : (Edge.left.takeAt k w₂).length = k := by
        show (w₂.take k).length = k
        rw [List.length_take]; omega
      rw [← hpre] at h_pre_len
      omega
    · push_neg at hw₂_long
      have h_w₂_pre : Edge.left.takeAt k w₂ = w₂ := by
        show w₂.take k = w₂
        exact List.take_of_length_le (le_of_lt hw₂_long)
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
