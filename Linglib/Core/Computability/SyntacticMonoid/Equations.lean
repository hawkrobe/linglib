/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.SyntacticMonoid
import Linglib.Core.Computability.Subregular.Definite

/-!
# Equational characterizations of subregular language classes

Lambert (2026) §6.2 (paper p. 22-25, with summary in Table 6 p. 28)
characterizes each base-class of subregular languages by a system of
equations on the *syntactic semigroup*: `D = ⟦sx^ω = x^ω⟧`,
`K = ⟦x^ω y = x^ω⟧`, `LI = ⟦x^ω y x^ω = x^ω⟧`, `N = ⟦x^ω y = x^ω;
yx^ω = x^ω⟧` (for definite, reverse-definite, generalized-definite,
co/finite, respectively).

This file lands the **`k`-definite case** (Lambert Prop 53, p. 23) as a
feasibility probe — the simplest entry into Lambert's algebraic story
because it requires no `omegaPow` (idempotent power) machinery.
Lambert's claim:

> A language is `k`-definite if and only if it is in
> `⟦sx₁ … xₖ = x₁ … xₖ⟧`.

Where the equation ranges over all instantiations of `s, x₁, …, xₖ` in
the syntactic semigroup.

## Mathlib precedent: monoid + non-identity sidecondition

Lambert's syntactic *semigroup* excludes the empty word; our
`Language.syntacticMonoid L` (built via `Con (FreeMonoid α)`, see
`SyntacticMonoid.lean`) includes the identity (the class of the empty
word). Mathlib's `Con.Quotient` precedent gives us a `Monoid`, not a
`Semigroup`; there is no established mathlib `syntacticSemigroup`
pattern. **We follow mathlib precedent and keep the `Monoid` setting**,
carrying `(s ≠ 1)` and `(∀ x ∈ xs, x ≠ 1)` sideconditions to recover
Lambert's semigroup convention.

The sidecondition is honest: a syntactic-monoid representative of a
non-identity class `[s]` is automatically a non-empty word (if every
representative of `s` were `[]`, then `s = (toQuotient []) = 1`,
contradiction). The sidecondition `s ≠ 1` is the categorical lift of
"the variable ranges over the syntactic *semigroup*".

## Main definitions

* `Lambert.Equations.kDefiniteEquation k M` — the equation
  `⟦sx₁ … xₖ = x₁ … xₖ⟧` on a monoid `M`, with non-identity
  sideconditions on `s` and on each `xᵢ`.

## Main results (status)

* `Language.IsDefinite.satisfies_kDefiniteEquation` — **forward
  direction PROVEN**: a `k`-definite language's syntactic monoid
  satisfies the equation. Proof works by extracting `FreeMonoid`
  representatives for each syntactic-monoid argument (each non-identity
  class has a non-empty representative; ~20 LOC `exists_rep_list_of_ne_one`
  helper) and applying the right-`k`-suffix-absorption argument at the
  representative level.

* `Language.isDefinite_of_satisfies_kDefiniteEquation` — **reverse
  direction sorry'd**. Proof sketch (paper p. 23, Lambert's "Suppose
  strings a and b have the same k-suffix…"): given the equation,
  construct a `DefiniteGrammar k α` for `L` whose permitted set is
  `{Edge.right.takeAt k w | w ∈ L}`. Show `G.lang = L` by case analysis
  on string length, using the equation to handle the long-string case.

* `Language.isDefinite_iff_satisfies_kDefiniteEquation` — Lambert
  Prop 53 bidirectional bundling. Forward half proven; reverse
  half sorry'd until the grammar construction lands.

## Out of scope (queued for follow-up files)

* `omegaPow` for finite monoids (Almeida 1995): the unique idempotent
  in `⟨x⟩`. Required for Lambert Props 56/57/58 (definite,
  reverse-definite, generalized-definite equations using `x^ω`).
  Mathlib-promotable as a sibling of `Mathlib.Algebra.Group.Idempotent`.
* Lambert Props 56/57/58 themselves — once `omegaPow` lands, each is a
  one-screen proof following the same forward-direction template as
  Prop 53 here.
* `multitier ℬ𝒯C` extensions (Lambert §6.3, Table 6 right column).

## References

* @cite{lambert-2026} §6.2, Prop 53 (paper p. 23).
* @cite{straubing-1985}, @cite{almeida-1995} — the equational-class
  framework Lambert builds on.
-/

namespace Lambert.Equations

variable {M : Type*} [Monoid M]

/-- **Lambert (2026) Prop 53 equation** `⟦sx₁ … xₖ = x₁ … xₖ⟧`: for all
non-identity `s : M` and all length-`k` lists `xs` of non-identity
elements, the prepended `s · xs.prod` equals `xs.prod`. The
non-identity sideconditions match Lambert's syntactic-semigroup
convention (which excludes the empty word) — see file docstring for
the mathlib-precedent rationale. -/
def kDefiniteEquation (k : ℕ) (M : Type*) [Monoid M] : Prop :=
  ∀ (s : M), s ≠ 1 →
  ∀ (xs : List M), xs.length = k → (∀ x ∈ xs, x ≠ 1) →
    s * xs.prod = xs.prod

end Lambert.Equations

open Core.Computability.Subregular

namespace Language

variable {α : Type*}

/-- Helper: extract a `FreeMonoid α` representative for each element of
a list of syntactic-monoid elements, preserving the non-identity
property. Each non-identity class has a non-empty representative
(else the class would be `1`). -/
private lemma exists_rep_list_of_ne_one {L : Language α}
    (xs : List L.syntacticMonoid) (hxs : ∀ x ∈ xs, x ≠ 1) :
    ∃ ws : List (FreeMonoid α),
      ws.map L.toSyntacticMonoid = xs ∧
      ws.length = xs.length ∧
      (∀ w ∈ ws, w ≠ 1) := by
  induction xs with
  | nil => exact ⟨[], rfl, rfl, fun _ h => absurd h List.not_mem_nil⟩
  | cons x xs' ih =>
    have hx_ne : x ≠ 1 := hxs x List.mem_cons_self
    have hxs'_ne : ∀ y ∈ xs', y ≠ 1 :=
      fun y hy => hxs y (List.mem_cons_of_mem _ hy)
    obtain ⟨ws', hws'_map, hws'_len, hws'_ne⟩ := ih hxs'_ne
    obtain ⟨x', hx'_rep⟩ := Quotient.exists_rep x
    have hx_eq : L.toSyntacticMonoid x' = x := hx'_rep
    have hx'_ne : x' ≠ (1 : FreeMonoid α) := by
      intro hcontra
      apply hx_ne
      rw [← hx_eq, hcontra]
      exact L.toSyntacticMonoid.map_one
    refine ⟨x' :: ws', ?_, ?_, ?_⟩
    · simp [List.map_cons, hx_eq, hws'_map]
    · simp [hws'_len]
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact hx'_ne
      · exact hws'_ne w hw'

/-- Helper: a list of non-empty words has total length ≥ the list length. -/
private lemma list_prod_length_ge {α : Type*} (ws : List (FreeMonoid α))
    (hws : ∀ w ∈ ws, w ≠ 1) : (FreeMonoid.toList ws.prod).length ≥ ws.length := by
  induction ws with
  | nil => simp
  | cons w ws' ih =>
    have hw_ne : w ≠ 1 := hws w List.mem_cons_self
    have hw_pos : (1 : ℕ) ≤ (FreeMonoid.toList w).length := by
      rcases hwl : (FreeMonoid.toList w) with _ | _
      · exact absurd (show w = 1 from hwl) hw_ne
      · simp
    have hih := ih (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw'))
    show (FreeMonoid.toList ((w :: ws').prod)).length ≥ (w :: ws').length
    rw [List.prod_cons]
    show (FreeMonoid.toList (w * ws'.prod)).length ≥ (w :: ws').length
    show (FreeMonoid.toList w ++ FreeMonoid.toList ws'.prod).length ≥
         (w :: ws').length
    simp only [List.length_append, List.length_cons]
    omega

/-- Helper: the right-`k`-suffix of `x ++ rest` equals the right-`k`-suffix
of `rest` whenever `rest.length ≥ k`. -/
private lemma takeAt_right_append_left_absorb {α : Type*}
    (x rest : List α) {k : ℕ} (h : k ≤ rest.length) :
    Edge.right.takeAt k (x ++ rest) = Edge.right.takeAt k rest := by
  show (x ++ rest).drop ((x ++ rest).length - k) =
       rest.drop (rest.length - k)
  rw [List.length_append,
      show x.length + rest.length - k = x.length + (rest.length - k) by omega,
      List.drop_length_add_append]

/-- Helper: at the `FreeMonoid` representative level, the `k`-definite
equation holds via the right-`k`-suffix-absorption argument. -/
private lemma definite_freeMonoid_satisfiesEq {L : Language α} {k : ℕ}
    (G : DefiniteGrammar k α) (hG : G.lang = L)
    (s : FreeMonoid α) (_hs : s ≠ 1)
    (ws : List (FreeMonoid α)) (hws_len : ws.length = k)
    (hws_ne : ∀ w ∈ ws, w ≠ 1) :
    SyntacticEquiv L (s * ws.prod) ws.prod := by
  intro x y
  -- Goal: x ++ (s * ws.prod : FreeMonoid α) ++ y ∈ L ↔ x ++ ws.prod ++ y ∈ L
  -- Bridge `*` to `++` on lists.
  show x ++ FreeMonoid.toList (s * ws.prod) ++ y ∈ L ↔
       x ++ FreeMonoid.toList ws.prod ++ y ∈ L
  have hsmul : FreeMonoid.toList (s * ws.prod) =
               FreeMonoid.toList s ++ FreeMonoid.toList ws.prod := rfl
  rw [hsmul, ← hG]
  show Edge.right.takeAt k
        (x ++ (FreeMonoid.toList s ++ FreeMonoid.toList ws.prod) ++ y) ∈
        G.permitted ↔
       Edge.right.takeAt k (x ++ FreeMonoid.toList ws.prod ++ y) ∈ G.permitted
  have hprod_len : (FreeMonoid.toList ws.prod).length ≥ k := by
    have := list_prod_length_ge ws hws_ne; omega
  have hsuf_eq :
      Edge.right.takeAt k
          (x ++ (FreeMonoid.toList s ++ FreeMonoid.toList ws.prod) ++ y) =
      Edge.right.takeAt k (x ++ FreeMonoid.toList ws.prod ++ y) := by
    rw [show x ++ (FreeMonoid.toList s ++ FreeMonoid.toList ws.prod) ++ y =
            (x ++ FreeMonoid.toList s) ++ (FreeMonoid.toList ws.prod ++ y) by
          simp [List.append_assoc],
        show x ++ FreeMonoid.toList ws.prod ++ y =
            x ++ (FreeMonoid.toList ws.prod ++ y) by simp [List.append_assoc]]
    have h_combined_len : k ≤ (FreeMonoid.toList ws.prod ++ y).length := by
      rw [List.length_append]; omega
    rw [takeAt_right_append_left_absorb (x ++ FreeMonoid.toList s)
          (FreeMonoid.toList ws.prod ++ y) h_combined_len,
        takeAt_right_append_left_absorb x
          (FreeMonoid.toList ws.prod ++ y) h_combined_len]
  rw [hsuf_eq]

/-- **Lambert Prop 53 (forward direction)**: a `k`-definite language's
syntactic monoid satisfies the `k`-definite equation
`⟦sx₁ … xₖ = x₁ … xₖ⟧`. -/
theorem IsDefinite.satisfies_kDefiniteEquation
    {L : Language α} {k : ℕ} (hL : IsDefinite k L) :
    Lambert.Equations.kDefiniteEquation k L.syntacticMonoid := by
  obtain ⟨G, hG⟩ := hL
  intro s hs xs hxs_len hxs_ne
  -- Extract representatives.
  obtain ⟨s', hs'_rep⟩ := Quotient.exists_rep s
  have hs'_eq : L.toSyntacticMonoid s' = s := hs'_rep
  have hs'_ne : s' ≠ (1 : FreeMonoid α) := by
    intro hcontra; apply hs
    rw [← hs'_eq, hcontra]; exact L.toSyntacticMonoid.map_one
  obtain ⟨ws, hws_map, hws_len, hws_ne⟩ := exists_rep_list_of_ne_one xs hxs_ne
  -- Bridge xs.prod = L.toSyntacticMonoid ws.prod via map_list_prod.
  have hxs_prod : xs.prod = L.toSyntacticMonoid ws.prod := by
    rw [← hws_map, ← MonoidHom.map_list_prod]
  rw [← hs'_eq, hxs_prod, ← MonoidHom.map_mul]
  -- Goal: L.toSyntacticMonoid (s' * ws.prod) = L.toSyntacticMonoid ws.prod
  exact Quotient.sound
    (definite_freeMonoid_satisfiesEq G hG s' hs'_ne ws (by omega) hws_ne)

/-- **Lambert Prop 53 (reverse direction, scaffolding)**: if a language's
syntactic monoid satisfies the `k`-definite equation, then the language
is `k`-definite. Proof deferred — see file docstring. -/
theorem isDefinite_of_satisfies_kDefiniteEquation
    {L : Language α} {k : ℕ}
    (h : Lambert.Equations.kDefiniteEquation k L.syntacticMonoid) :
    IsDefinite k L := by
  sorry

/-- **Lambert (2026) Prop 53**: a language is `k`-definite iff its
syntactic semigroup satisfies the `k`-definite equation
`⟦sx₁ … xₖ = x₁ … xₖ⟧`. Bidirectional bundling of
`IsDefinite.satisfies_kDefiniteEquation` and
`isDefinite_of_satisfies_kDefiniteEquation`. -/
theorem isDefinite_iff_satisfies_kDefiniteEquation
    {L : Language α} {k : ℕ} :
    IsDefinite k L ↔ Lambert.Equations.kDefiniteEquation k L.syntacticMonoid :=
  ⟨IsDefinite.satisfies_kDefiniteEquation,
   isDefinite_of_satisfies_kDefiniteEquation⟩

end Language
