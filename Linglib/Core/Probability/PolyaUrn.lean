import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Pólya urn scheme (Dirichlet–multinomial likelihood)

@cite{odonnell-2015}

A *Pólya urn* over an alphabet of size `K` is a sequential sampling
scheme governed by strictly-positive pseudo-counts
`π : Fin K → ℝ`. The first draw is categorical with weights
`π_i / Σ π`; the `(N + 1)`-th draw conditional on previous counts
`x_1, …, x_K` is categorical with weights
`(π_i + x_i) / (Σ π + Σ x)` — a "rich-get-richer" dynamic.

By de Finetti's theorem this is exactly the marginal of a
Dirichlet–multinomial mixture: drawing `θ ~ Dirichlet(π)` then
sampling i.i.d. from `Categorical(θ)` and integrating out `θ` gives
the same distribution. The counts vector after `N` draws has the
closed-form likelihood

```
P(x | π) = Γ(Σ π) / Γ(Σ π + Σ x)  ·  ∏ Γ(π_i + x_i) / Γ(π_i)
```

This file gives the structure and the closed-form likelihood. The
sequential sampler itself is not formalized; only the closed form is
needed by downstream Bayesian-non-parametric constructions in
`Theories/Probabilistic/Grammar/` (Dirichlet-multinomial PCFG,
adaptor grammars, fragment grammars).

## Main definitions

- `PolyaUrn K` — the data of the urn (per-color pseudo-counts).
- `PolyaUrn.total` — the sum `Σ π_i` (often written `α`).
- `PolyaUrn.partitionProb` — closed-form Dirichlet–multinomial mass
  for a count vector.

## References

- @cite{odonnell-2015} §3.1.3, eq 3.7.
-/

namespace ProbabilityTheory

open Real

/--
A Pólya urn scheme over an alphabet of size `K`, parameterized by
strictly-positive pseudo-counts. In the de Finetti representation
the pseudo-counts are the Dirichlet hyperparameters: i.i.d. draws
from `Categorical(θ)` for `θ ~ Dirichlet(pseudo)` have the same
joint as the Pólya urn.
-/
@[ext]
structure PolyaUrn (K : ℕ) where
  /-- Per-color pseudo-count (the Dirichlet hyperparameter). -/
  pseudo : Fin K → ℝ
  /-- Pseudo-counts are strictly positive. -/
  pseudo_pos : ∀ i, 0 < pseudo i

namespace PolyaUrn

variable {K : ℕ} (u : PolyaUrn K)

/-- The total pseudo-count `Σ π_i`. Strictly positive when `K ≠ 0`. -/
noncomputable def total : ℝ := ∑ i, u.pseudo i

theorem total_pos [NeZero K] : 0 < u.total :=
  Finset.sum_pos (fun i _ => u.pseudo_pos i) Finset.univ_nonempty

/--
Closed-form likelihood of observing the count vector `x` after
`Σ x_i` draws from the urn `u`. This is the Dirichlet–multinomial
probability mass

```
P(x | π) = Γ(Σ π) / Γ(Σ π + Σ x)  ·  ∏ Γ(π_i + x_i) / Γ(π_i)
```

The closed form depends only on the count vector, not on the order in
which the draws occurred. This **exchangeability** is what makes the
recursive stochastic equations defining DMPCFG, adaptor grammars,
and fragment grammars in `Theories.Probabilistic.Grammar.*`
well-defined as marginals over draw order.
-/
noncomputable def partitionProb (x : Fin K → ℕ) : ℝ :=
  Gamma u.total / Gamma (u.total + ∑ i, (x i : ℝ)) *
    ∏ i, Gamma (u.pseudo i + x i) / Gamma (u.pseudo i)

/-- The empty count vector — no draws — has likelihood `1`. -/
theorem partitionProb_zero [NeZero K] :
    u.partitionProb (fun _ => 0) = 1 := by
  unfold partitionProb
  simp only [Nat.cast_zero, Finset.sum_const_zero, add_zero]
  rw [div_self (Gamma_pos_of_pos u.total_pos).ne', one_mul]
  apply Finset.prod_eq_one
  intro i _
  exact div_self (Gamma_pos_of_pos (u.pseudo_pos i)).ne'

end PolyaUrn

end ProbabilityTheory
