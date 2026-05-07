/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.SyntacticMonoid
import Linglib.Core.Computability.Subregular.Definite

/-!
# Equational characterizations of subregular language classes

@cite{lambert-2026} §6.2 (paper p. 22-25, with summary in Table 6 p. 28)
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

* `Lambert.Equations.kDefiniteEquation L k` — the equation
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

## Out of scope (queued for follow-up files)

* `omegaPow` for finite monoids (Almeida 1995): the unique idempotent
  in `⟨x⟩`. Required for Lambert Props 56/57/58 (definite,
  reverse-definite, generalized-definite equations using `x^ω`).
  Mathlib-promotable as a sibling of `Mathlib.Algebra.Group.Idempotent`.
* Lambert Props 56/57/58 themselves — once `omegaPow` lands, each is a
  one-screen proof following the same letter-sequence template as
  Prop 53 here.
* `multitier ℬ𝒯C` extensions (@cite{lambert-2026} §6.3, Table 6 right
  column).

## References

* @cite{lambert-2026} §6.2, Prop 53 (paper p. 23).
* @cite{straubing-1985}, @cite{almeida-1995} — the equational-class
  framework Lambert builds on.
-/

namespace Lambert.Equations

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

end Lambert.Equations

open Core.Computability.Subregular

namespace Language

variable {α : Type*}

-- ============================================================================
-- §1. Helper lemmas on `Edge.right.takeAt`
-- ============================================================================

/-- The right-`k`-suffix of `x ++ rest` equals the right-`k`-suffix
of `rest` whenever `rest.length ≥ k`. -/
private lemma takeAt_right_append_left_absorb {α : Type*}
    (x rest : List α) {k : ℕ} (h : k ≤ rest.length) :
    Edge.right.takeAt k (x ++ rest) = Edge.right.takeAt k rest := by
  show (x ++ rest).drop ((x ++ rest).length - k) =
       rest.drop (rest.length - k)
  rw [List.length_append,
      show x.length + rest.length - k = x.length + (rest.length - k) by omega,
      List.drop_length_add_append]

/-- When `xs.length ≤ k`, the right-`k`-suffix of `xs` is `xs` itself. -/
private lemma takeAt_right_of_short {α : Type*} {k : ℕ} {xs : List α}
    (h : xs.length ≤ k) : Edge.right.takeAt k xs = xs := by
  show xs.drop (xs.length - k) = xs
  have : xs.length - k = 0 := by omega
  rw [this, List.drop_zero]

/-- When `xs.length ≥ k`, the right-`k`-suffix of `xs` has length exactly `k`. -/
private lemma takeAt_right_length_of_long {α : Type*} {k : ℕ} {xs : List α}
    (h : k ≤ xs.length) : (Edge.right.takeAt k xs).length = k := by
  show (xs.drop (xs.length - k)).length = k
  rw [List.length_drop]; omega

/-- A list `xs` of length `≥ k` decomposes as
`xs.take (xs.length - k) ++ Edge.right.takeAt k xs`. -/
private lemma decompose_at_right_takeAt {α : Type*} {k : ℕ} {xs : List α}
    (_h : k ≤ xs.length) :
    xs = xs.take (xs.length - k) ++ Edge.right.takeAt k xs := by
  show xs = xs.take (xs.length - k) ++ xs.drop (xs.length - k)
  exact (List.take_append_drop _ _).symm

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
    (h : Lambert.Equations.kDefiniteEquation L k)
    (w αs : List α) (hαs_len : αs.length = k) :
    SyntacticEquiv L (w ++ αs) αs := by
  have h_eq :=
    h (L.toSyntacticMonoid (FreeMonoid.ofList w)) αs hαs_len
  have h_pre :
      L.toSyntacticMonoid (FreeMonoid.ofList (w ++ αs)) =
      L.toSyntacticMonoid (FreeMonoid.ofList αs) := by
    have hmul : (FreeMonoid.ofList (w ++ αs) : FreeMonoid α) =
                FreeMonoid.ofList w * FreeMonoid.ofList αs := rfl
    rw [hmul, MonoidHom.map_mul]
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
    {L : Language α} {k : ℕ} (hL : IsDefinite k L) :
    Lambert.Equations.kDefiniteEquation L k := by
  obtain ⟨G, hG⟩ := hL
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
  rw [hwmul, hαsId, ← hG]
  show Edge.right.takeAt k (x ++ (FreeMonoid.toList w ++ αs) ++ y) ∈ G.permitted ↔
       Edge.right.takeAt k (x ++ αs ++ y) ∈ G.permitted
  have hsuf_eq :
      Edge.right.takeAt k (x ++ (FreeMonoid.toList w ++ αs) ++ y) =
      Edge.right.takeAt k (x ++ αs ++ y) := by
    rw [show x ++ (FreeMonoid.toList w ++ αs) ++ y =
            (x ++ FreeMonoid.toList w) ++ (αs ++ y) by simp [List.append_assoc],
        show x ++ αs ++ y = x ++ (αs ++ y) by simp [List.append_assoc]]
    have h_combined_len : k ≤ (αs ++ y).length := by
      rw [List.length_append]; omega
    rw [takeAt_right_append_left_absorb (x ++ FreeMonoid.toList w)
          (αs ++ y) h_combined_len,
        takeAt_right_append_left_absorb x (αs ++ y) h_combined_len]
  rw [hsuf_eq]

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
    (h : Lambert.Equations.kDefiniteEquation L k) :
    IsDefinite k L := by
  refine ⟨{ permitted := { ks | ∃ w ∈ L, Edge.right.takeAt k w = ks } }, ?_⟩
  ext w
  refine ⟨?_, fun hw => ⟨w, hw, rfl⟩⟩
  rintro ⟨u, hu, hsuf⟩
  by_cases hu_short : u.length ≤ k
  · have hu_eq : Edge.right.takeAt k u = u := takeAt_right_of_short hu_short
    by_cases hw_short : w.length ≤ k
    · -- (1) both short: takeAts are u, w themselves; equality forces w = u
      have hw_eq : Edge.right.takeAt k w = w := takeAt_right_of_short hw_short
      rw [hu_eq, hw_eq] at hsuf
      rw [← hsuf]; exact hu
    · -- (2) u short, w long: u must have length k
      push_neg at hw_short
      have hw_len_suf : (Edge.right.takeAt k w).length = k :=
        takeAt_right_length_of_long (le_of_lt hw_short)
      rw [← hsuf, hu_eq] at hw_len_suf
      rw [hu_eq] at hsuf
      have hw_decomp : w = w.take (w.length - k) ++ u := by
        rw [hsuf]
        exact decompose_at_right_takeAt (le_of_lt hw_short)
      have hequiv : SyntacticEquiv L w u := by
        rw [hw_decomp]
        exact syntacticEquiv_of_kDefiniteEquation h _ _ hw_len_suf
      rw [mem_iff_of_syntacticEquiv hequiv]; exact hu
  · push_neg at hu_short
    have hu_len_suf : (Edge.right.takeAt k u).length = k :=
      takeAt_right_length_of_long (le_of_lt hu_short)
    by_cases hw_short : w.length ≤ k
    · -- (3) u long, w short: w must have length k
      have hw_eq : Edge.right.takeAt k w = w := takeAt_right_of_short hw_short
      rw [hw_eq] at hsuf
      rw [hsuf] at hu_len_suf
      have hu_decomp : u = u.take (u.length - k) ++ w := by
        rw [← hsuf]
        exact decompose_at_right_takeAt (le_of_lt hu_short)
      have hequiv : SyntacticEquiv L u w := by
        rw [hu_decomp]
        exact syntacticEquiv_of_kDefiniteEquation h _ _ hu_len_suf
      exact (mem_iff_of_syntacticEquiv hequiv).mp hu
    · -- (4) both long: shared length-k suffix
      push_neg at hw_short
      have hw_len_suf : (Edge.right.takeAt k w).length = k :=
        takeAt_right_length_of_long (le_of_lt hw_short)
      have hequiv_u : SyntacticEquiv L u (Edge.right.takeAt k u) := by
        have base := syntacticEquiv_of_kDefiniteEquation h
          (u.take (u.length - k)) (Edge.right.takeAt k u) hu_len_suf
        rwa [← decompose_at_right_takeAt (le_of_lt hu_short)] at base
      have hequiv_w : SyntacticEquiv L w (Edge.right.takeAt k w) := by
        have base := syntacticEquiv_of_kDefiniteEquation h
          (w.take (w.length - k)) (Edge.right.takeAt k w) hw_len_suf
        rwa [← decompose_at_right_takeAt (le_of_lt hw_short)] at base
      have hequiv : SyntacticEquiv L w u := by
        apply hequiv_w.trans
        rw [← hsuf]
        exact hequiv_u.symm
      rw [mem_iff_of_syntacticEquiv hequiv]; exact hu

/-- **Lambert (2026) Prop 53**: a language is `k`-definite iff its
syntactic monoid satisfies the `k`-definite equation. Bidirectional
bundling of `IsDefinite.satisfies_kDefiniteEquation` and
`isDefinite_of_satisfies_kDefiniteEquation`. -/
theorem isDefinite_iff_satisfies_kDefiniteEquation
    {L : Language α} {k : ℕ} :
    IsDefinite k L ↔ Lambert.Equations.kDefiniteEquation L k :=
  ⟨IsDefinite.satisfies_kDefiniteEquation,
   isDefinite_of_satisfies_kDefiniteEquation⟩

end Language
