import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Pólya urn scheme (Dirichlet–multinomial likelihood)

@cite{odonnell-2015}

A *Pólya urn* over an alphabet `α` is a sequential sampling
scheme governed by strictly-positive pseudo-counts
`π : α → ℝ`. The first draw is categorical with weights
`π_i / Σ π`; the `(N + 1)`-th draw conditional on previous counts
`x_1, …` is categorical with weights `(π_i + x_i) / (Σ π + Σ x)` —
a "rich-get-richer" dynamic.

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
`Theories/Morphology/FragmentGrammars/` (`DMPCFG`, `AdaptorGrammar`,
`FragmentGrammar`).

## Type-polymorphic alphabet

The alphabet `α` is an arbitrary type; operations require
`[Fintype α]` (so that `∑ i, ...` and `∏ i, ...` are well-defined),
and theorems requiring positivity of the total pseudo-count
additionally need `[Nonempty α]`. The previous `Fin K`-indexed shape
is the special case `α = Fin K` (with `[NeZero K]` equivalent to
`[Nonempty (Fin K)]`); the polymorphic shape composes cleanly with
`Finset`-restricted alphabets needed by per-LHS PCFG factors.

## Main definitions

- `PolyaUrn α` — pseudo-counts on `α`.
- `PolyaUrn.total` — the sum `Σ π_i` (often written `α` in the
  literature; here we avoid that letter because it clashes with the
  alphabet type).
- `PolyaUrn.partitionProb` — closed-form Dirichlet–multinomial mass
  for a count vector.

## References

- @cite{odonnell-2015} §3.1.3, eq 3.7.
-/

namespace ProbabilityTheory

open Real

/--
A Pólya urn scheme over the alphabet `α`, parameterized by
strictly-positive pseudo-counts. In the de Finetti representation
the pseudo-counts are the Dirichlet hyperparameters: i.i.d. draws
from `Categorical(θ)` for `θ ~ Dirichlet(pseudo)` have the same
joint as the Pólya urn.
-/
@[ext]
structure PolyaUrn (α : Type) where
  /-- Per-color pseudo-count (the Dirichlet hyperparameter). -/
  pseudo : α → ℝ
  /-- Pseudo-counts are strictly positive. -/
  pseudo_pos : ∀ i, 0 < pseudo i

namespace PolyaUrn

variable {α : Type} [Fintype α] (u : PolyaUrn α)

/-- The total pseudo-count `Σ π_i`. Strictly positive when `α` is nonempty. -/
noncomputable def total : ℝ := ∑ i, u.pseudo i

theorem total_pos [Nonempty α] : 0 < u.total :=
  Finset.sum_pos (fun i _ => u.pseudo_pos i) Finset.univ_nonempty

/--
Closed-form likelihood of observing the count vector `x` after
`Σ x_i` draws from the urn `u`. This is the Dirichlet–multinomial
probability mass

```
P(x | π) = Γ(Σ π) / Γ(Σ π + Σ x)  ·  ∏ Γ(π_i + x_i) / Γ(π_i)
```

The closed form depends only on the count vector, not on the order in
which the draws occurred. This **exchangeability** is the property
that makes the recursive stochastic equations defining DMPCFG,
adaptor grammars, and fragment grammars in
`Theories.Morphology.FragmentGrammars.*` well-defined as marginals
over draw order.
-/
noncomputable def partitionProb (x : α → ℕ) : ℝ :=
  Gamma u.total / Gamma (u.total + ∑ i, (x i : ℝ)) *
    ∏ i, Gamma (u.pseudo i + x i) / Gamma (u.pseudo i)

/-- The empty count vector — no draws — has likelihood `1`. -/
theorem partitionProb_zero [Nonempty α] :
    u.partitionProb (fun _ => 0) = 1 := by
  unfold partitionProb
  simp only [Nat.cast_zero, Finset.sum_const_zero, add_zero]
  rw [div_self (Gamma_pos_of_pos u.total_pos).ne', one_mul]
  apply Finset.prod_eq_one
  intro i _
  exact div_self (Gamma_pos_of_pos (u.pseudo_pos i)).ne'

/--
Pólya partition probabilities are strictly positive on nonempty
alphabets. Since `Γ` is positive on positive reals and pseudo-counts
are positive, every Γ-ratio in the closed form is positive. Used by
downstream consumers (`DMPCFG`, `AdaptorGrammar`) to derive
nonnegativity of corpus probabilities.
-/
theorem partitionProb_pos [Nonempty α] (x : α → ℕ) :
    0 < u.partitionProb x := by
  have h_total_pos : 0 < u.total := u.total_pos
  have h_x_nn : (0 : ℝ) ≤ ∑ i, (x i : ℝ) :=
    Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hΓ_num_pos : 0 < Gamma u.total := Gamma_pos_of_pos h_total_pos
  have hΓ_den_pos : 0 < Gamma (u.total + ∑ i, (x i : ℝ)) :=
    Gamma_pos_of_pos (by linarith)
  have hRatio_pos :
      0 < Gamma u.total / Gamma (u.total + ∑ i, (x i : ℝ)) :=
    div_pos hΓ_num_pos hΓ_den_pos
  have hProd_pos :
      0 < ∏ i, Gamma (u.pseudo i + x i) / Gamma (u.pseudo i) := by
    apply Finset.prod_pos
    intro i _
    have h_psi_pos : 0 < u.pseudo i := u.pseudo_pos i
    have h_xi_nn : (0 : ℝ) ≤ (x i : ℝ) := Nat.cast_nonneg _
    refine div_pos (Gamma_pos_of_pos ?_) (Gamma_pos_of_pos h_psi_pos)
    linarith
  unfold partitionProb
  exact mul_pos hRatio_pos hProd_pos

/-- Pólya partition probabilities are nonnegative — corollary of
    `partitionProb_pos`. Stated for use without `[Nonempty α]`
    discharging in downstream nonneg proofs. -/
theorem partitionProb_nonneg [Nonempty α] (x : α → ℕ) :
    0 ≤ u.partitionProb x :=
  (u.partitionProb_pos x).le

end PolyaUrn

end ProbabilityTheory
