import Linglib.Core.Probability.PolyaUrn
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Dirichlet–multinomial distribution

@cite{odonnell-2015}

The count-vector PMF associated with a `PolyaUrn`. Sequentially: the
distribution of `(x_1, …, x_K)` after drawing `N` times from the
urn, where `x_i` counts how often color `i` was drawn. By
Dirichlet–Categorical conjugacy, equivalently obtained by sampling
`θ ~ Dirichlet(π)` and then `(x_1, …, x_K) ~ Multinomial(N; θ)` and
integrating out `θ`.

Closed-form mass at `x : α → ℕ` with `∑ i, x i = N`:

```
P(x | π) = (N! / ∏ x_i!) · Γ(Σ π) / Γ(Σ π + N) · ∏ Γ(π_i + x_i) / Γ(π_i)
```

The first factor is the multinomial coefficient (number of draw
sequences realizing the count vector `x`); the rest is
`PolyaUrn.seqProb x` (the per-sequence likelihood, defined in the
sibling file `PolyaUrn.lean`).

## Two-tier mathlib pattern

Mirrors `Mathlib.Probability.Distributions.Poisson.Basic`'s
`poissonPMFReal` + `poissonPMF`: a raw-`ℝ` closed form `pmfReal` and
a proper `PMF (α → ℕ)` wrapper `pmf` constructed directly from a
`HasSum` proof.

## Status

Normalization (`pmfReal_hasSum_one`) is currently `sorry`:
equivalent to the Dirichlet integration identity, and a candidate to
upstream to mathlib alongside a proper
`Mathlib/Probability/Distributions/Dirichlet.lean` /
`DirichletMultinomial.lean`.

## Why split from `PolyaUrn.lean`

Downstream consumers (`Theories/Morphology/FragmentGrammars/DMPCFG`,
`AdaptorGrammar`, `FragmentGrammar`) consume only
`PolyaUrn.seqProb` — a corpus IS a labeled derivation sequence, not
a draw from the unlabeled-count distribution. Bundling the PMF
machinery into `PolyaUrn.lean` would force every consumer of
`seqProb` to pay the `Probability.ProbabilityMassFunction.Basic`
import cost (~10s of olean loading via `MeasureTheory.Measure.Dirac`).
Mathlib analog: `Distributions/Poisson/Basic.lean` is distinct from
`Distributions/Poisson/Variance.lean` for the same import-discipline
reason.

## Why we avoid `PMF.ofFinset` + `Finset.piAntidiag` + `Nat.multinomial`

Each lives in a heavier mathlib file
(`ProbabilityMassFunction.Constructions`, `Algebra.Order.Antidiag.Pi`,
`Data.Nat.Choose.Multinomial`) and we don't need them: the PMF can
be built directly from a `HasSum` (mathlib's `PMF.ofFinset` is
itself just `⟨_, hasSum_sum_of_ne_finset_zero ...⟩`), the support
characterization fits as an inline `if ∑ i, x i = N then _ else 0`,
and the multinomial coefficient is just `(∑ i, x i)! / ∏ i, (x i)!`
written out. Mathlib's Poisson takes the same approach
(`⟨ENNReal.ofReal ∘ poissonPMFReal r, _⟩`).

The labeled→unlabeled `.map` to `PMF (Nat.Partition N)` is deferred
to a future file (would import `Combinatorics.Enumerative.Partition`
and `ProbabilityMassFunction.Monad` for `.map`).

## Main definitions

- `DirichletMultinomial.pmfReal` — closed-form mass at a count
  vector, as a raw `ℝ` (= multinomial coefficient · `seqProb`).
- `DirichletMultinomial.pmf` — the distribution as a proper
  `PMF (α → ℕ)`, supported on count vectors summing to `N`.
  Normalization currently sorried (`pmfReal_hasSum_one`).
-/

namespace ProbabilityTheory

namespace DirichletMultinomial

variable {α : Type*} [Fintype α] (u : PolyaUrn α)

/-- Dirichlet–multinomial closed-form mass at a count vector, as a
raw `ℝ`. The multinomial coefficient `(∑ x_i)! / ∏ (x_i!)` counts
how many draw sequences realize the count vector `x`; multiplying
by `PolyaUrn.seqProb x` gives the count-vector mass. For `x`
summing to `N`, this equals
`(N! / ∏ x_i!) · Γ(Σ π) / Γ(Σ π + N) · ∏ Γ(π_i + x_i) / Γ(π_i)` —
the standard Dirichlet–multinomial mass. -/
noncomputable def pmfReal (x : α → ℕ) : ℝ :=
  ((∑ i, x i).factorial : ℝ) / (∏ i, (x i).factorial : ℝ) * u.seqProb x

theorem pmfReal_nonneg [Nonempty α] (x : α → ℕ) :
    0 ≤ pmfReal u x := by
  unfold pmfReal
  refine mul_nonneg (div_nonneg (Nat.cast_nonneg _) ?_) (u.seqProb_pos x).le
  exact_mod_cast (Finset.univ.prod (fun i => (x i).factorial)).zero_le

/--
**Dirichlet–multinomial normalization.** The closed-form mass sums
to `1` over count vectors of any fixed total `N` (zero elsewhere).

Proof sketch (not formalized): equivalent to the Dirichlet
integration identity. By Dirichlet–Categorical conjugacy and the
multinomial theorem,

```
1 = ∫ (∑ θ_i)^N dDirichlet(π)
  = ∫ ∑_{x : Σ = N} (multinomial x) · ∏ θ_i^(x_i) dDirichlet(π)
  = ∑_{x : Σ = N} (N! / ∏ x_i!) · Γ(Σ π) / Γ(Σ π + N) · ∏ Γ(π_i + x_i) / Γ(π_i)
```

TODO: prove. Mathlib does not currently have the Dirichlet
distribution; this normalization is a candidate to upstream alongside
a proper `Mathlib/Probability/Distributions/DirichletMultinomial.lean`.
-/
theorem pmfReal_hasSum_one [DecidableEq α] [Nonempty α] (N : ℕ) :
    HasSum (fun x : α → ℕ =>
      if ∑ i, x i = N then ENNReal.ofReal (pmfReal u x) else 0) 1 := by
  sorry

/--
The Dirichlet–multinomial distribution as a proper `PMF (α → ℕ)`,
supported on count vectors summing to `N`.

Constructed directly from `HasSum` (mirroring mathlib's Poisson
`⟨ENNReal.ofReal ∘ poissonPMFReal r, _⟩`) rather than via heavier
`PMF.ofFinset` / `Finset.piAntidiag` machinery — see file docstring.
-/
noncomputable def pmf [DecidableEq α] [Nonempty α] (N : ℕ) : PMF (α → ℕ) :=
  ⟨fun x => if ∑ i, x i = N then ENNReal.ofReal (pmfReal u x) else 0,
   pmfReal_hasSum_one u N⟩

/-- Closed-form value at a count vector summing to `N`. -/
@[simp]
theorem pmf_apply [DecidableEq α] [Nonempty α] (N : ℕ) (x : α → ℕ)
    (hx : ∑ i, x i = N) :
    pmf u N x = ENNReal.ofReal (pmfReal u x) := by
  show (if ∑ i, x i = N then _ else 0) = _
  exact if_pos hx

/-- Outside its support (count vectors that don't sum to `N`), the
    Dirichlet–multinomial PMF is zero. -/
theorem pmf_apply_of_sum_ne [DecidableEq α] [Nonempty α]
    (N : ℕ) (x : α → ℕ) (hx : ∑ i, x i ≠ N) :
    pmf u N x = 0 := by
  show (if ∑ i, x i = N then _ else 0) = _
  exact if_neg hx

end DirichletMultinomial

end ProbabilityTheory
