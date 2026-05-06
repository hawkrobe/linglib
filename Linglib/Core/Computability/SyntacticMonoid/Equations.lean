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

* `Language.isDefinite_iff_satisfies_kDefiniteEquation` — Lambert's
  Prop 53 bidirectional. **Both directions sorry'd**; this PR is the
  scaffolding + design-validation, with the proofs queued for follow-up.

  Forward direction proof sketch (paper p. 23): given `IsDefinite k L`
  via grammar `G`, take representatives `s', w_1, …, w_k` of the
  syntactic-monoid arguments. Each `w_i ≠ 1` implies `|w_i| ≥ 1`, so
  `|w_1 … w_k| ≥ k`. Then for any left context `x` and right context
  `y`, the right-`k`-suffix of `x ++ s' ++ w_1 ++ … ++ w_k ++ y` is
  determined by `w_1 ++ … ++ w_k ++ y` alone (since that part is
  already length-`≥ k`); same for `x ++ w_1 ++ … ++ w_k ++ y`. So the
  two strings have the same `k`-suffix, hence the same membership in
  `L`. The list-of-quotient-elements representative extraction is
  mechanically complex but straightforward.

  Reverse direction proof sketch (paper p. 23, Lambert's "Suppose
  strings a and b have the same k-suffix…"): given the equation,
  construct a `DefiniteGrammar k α` for `L` whose permitted set is
  `{takeAt right k w | w ∈ L}`. Show `G.lang = L` by case analysis on
  string length.

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

/-- **Lambert Prop 53 (forward direction, scaffolding)**: a `k`-definite
language's syntactic monoid satisfies the `k`-definite equation. Proof
deferred — see file docstring "Main results (status)" for the sketch.

Implementation note: a first attempt at this proof was 60 lines using
explicit `Quotient.exists_rep` extraction for `xs : List L.syntacticMonoid`,
but ran into `Con.toQuotient` vs `Language.toSyntacticMonoid` coercion
fights with mathlib's `MonoidHom.map_list_prod`. A clean version
requires either (a) an `@[simp] toSyntacticMonoid_apply` API expansion,
or (b) staging the proof at the FreeMonoid representative level first
(`SyntacticEquiv L (s' * ws.prod) ws.prod`) and then transferring once
via `Quotient.sound`. Queued for a follow-up; the equation definition
above is the substantive design choice. -/
theorem IsDefinite.satisfies_kDefiniteEquation
    {L : Language α} {k : ℕ} (hL : IsDefinite k L) :
    Lambert.Equations.kDefiniteEquation k L.syntacticMonoid := by
  sorry

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
