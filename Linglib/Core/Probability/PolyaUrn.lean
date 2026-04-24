import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Pólya urn (per-sequence likelihood)

@cite{odonnell-2015}

A *Pólya urn* over an alphabet `α` is a sequential sampling
scheme governed by strictly-positive pseudo-counts
`π : α → ℝ`. The first draw is categorical with weights
`π_i / Σ π`; the `(N + 1)`-th draw conditional on previous counts
`x_1, …` is categorical with weights `(π_i + x_i) / (Σ π + Σ x)` — a
preferential-attachment dynamic, finite-`K` variant of the
power-law-tail dynamic that the Pitman–Yor process exhibits in the
unbounded-alphabet limit.

By Dirichlet–Categorical conjugacy, drawing `θ ~ Dirichlet(π)` then
sampling i.i.d. from `Categorical(θ)` and integrating out `θ` yields
the same exchangeable sequence law (the de Finetti representation
theorem guarantees that *some* mixing measure exists; identifying it
as Dirichlet is conjugacy + integration). The probability of any
specific draw sequence with counts `x_1, …, x_K` has the closed form
of @cite{odonnell-2015} eq 3.7 (-- UNVERIFIED: section/equation
number from memory; verify against PDF):

```
P(seq | π) = Γ(Σ π) / Γ(Σ π + Σ x)  ·  ∏ Γ(π_i + x_i) / Γ(π_i)
```

This file gives only the closed-form per-sequence likelihood
`seqProb` — the form fragment-grammar consumers in
`Theories/Morphology/FragmentGrammars/` actually use (a corpus IS a
labeled derivation sequence, not a draw from the unlabeled-count
distribution). The corresponding count-vector PMF — the
"Dirichlet–multinomial distribution" — lives in the sibling file
`DirichletMultinomial.lean`, which carries the heavier
`Probability.ProbabilityMassFunction.Basic` import (transitively
~10s of olean loading via `MeasureTheory.Measure.Dirac`).

The sequential sampler itself is not formalized — only the closed
form is needed by downstream constructions.

## Type-polymorphic alphabet

The alphabet `α` is an arbitrary type; operations require
`[Fintype α]` (so that `∑ i, ...` and `∏ i, ...` are well-defined),
and theorems requiring positivity of the total pseudo-count
additionally need `[Nonempty α]`. The previous `Fin K`-indexed shape
is the special case `α = Fin K` (with `[NeZero K]` equivalent to
`[Nonempty (Fin K)]`); the polymorphic shape composes cleanly with
`Finset`-restricted alphabets needed by per-LHS PCFG factors.

## Relationship to `PitmanYor`

The Pólya urn is often described as the "finite-K Chinese Restaurant
Process". This is correct sequentially but misleading
distributionally: the labeled count distribution
`DirichletMultinomial.pmf` (sibling file) is *not* equal at any
finite `K` to the partition distribution `PitmanYor.partitionProb`
at `discount = 0`. The two agree only in the limit `K → ∞` with
symmetric pseudo-counts `π_i = b/K` (Blackwell & MacQueen 1973;
Ferguson 1973). The bridge is therefore a limit theorem, not a
finite equality, and is not yet formalized — the labeled→unlabeled
`.map` pushforward to `PMF (Nat.Partition N)` (the natural target
type for such a bridge) is also deferred.

## Main definitions

- `PolyaUrn α` — pseudo-counts on `α` (the Dirichlet hyperparameters).
- `PolyaUrn.total` — the sum `Σ π_i`.
- `PolyaUrn.seqProb` — closed-form per-sequence likelihood
  (eq 3.7 of @cite{odonnell-2015}, depending only on counts).

## References

- @cite{odonnell-2015} — Pólya-urn closed form for DMPCFG (-- UNVERIFIED:
  §3.1.3 eq 3.7 from memory; verify against PDF).
- Blackwell, D. & MacQueen, J. B. (1973). "Ferguson distributions via
  Pólya urn schemes". *The Annals of Statistics* 1(2): 353–355.
- Ferguson, T. S. (1973). "A Bayesian analysis of some nonparametric
  problems". *The Annals of Statistics* 1(2): 209–230.
-/

namespace ProbabilityTheory

open Real

/--
A Pólya urn scheme over the alphabet `α`, parameterized by
strictly-positive pseudo-counts. In the de Finetti representation
the pseudo-counts are the Dirichlet hyperparameters: i.i.d. draws
from `Categorical(θ)` for `θ ~ Dirichlet(pseudo)` have the same
exchangeable sequence law as the Pólya urn.
-/
@[ext]
structure PolyaUrn (α : Type*) where
  /-- Per-color pseudo-count (the Dirichlet hyperparameter). -/
  pseudo : α → ℝ
  /-- Pseudo-counts are strictly positive. -/
  pseudo_pos : ∀ i, 0 < pseudo i

namespace PolyaUrn

variable {α : Type*} [Fintype α] (u : PolyaUrn α)

/-- The total pseudo-count `Σ π_i`. Strictly positive when `α` is nonempty. -/
def total : ℝ := ∑ i, u.pseudo i

theorem total_pos [Nonempty α] : 0 < u.total :=
  Finset.sum_pos (fun i _ => u.pseudo_pos i) Finset.univ_nonempty

/--
Closed-form *per-sequence likelihood* (not the count PMF — see
`DirichletMultinomial.pmfReal` for that): probability that a draw
sequence with counts `x` was emitted by the urn `u`.

```
P(seq | π) = Γ(Σ π) / Γ(Σ π + Σ x)  ·  ∏ Γ(π_i + x_i) / Γ(π_i)
```

Depends only on the counts (not the order), which is what makes the
recursive stochastic equations defining DMPCFG, adaptor grammars, and
fragment grammars in `Theories.Morphology.FragmentGrammars.*`
well-defined as marginals over draw order — *partition
exchangeability* in the EPPF sense, distinct from but implied by
exchangeability proper of the joint sequence law.

To convert to the count-vector PMF, multiply by the multinomial
coefficient `(∑ x_i)! / ∏ (x_i!)`. See `DirichletMultinomial`.
-/
noncomputable def seqProb (x : α → ℕ) : ℝ :=
  Gamma u.total / Gamma (u.total + ∑ i, (x i : ℝ)) *
    ∏ i, Gamma (u.pseudo i + x i) / Gamma (u.pseudo i)

/-- The empty count vector — no draws — has per-sequence likelihood `1`. -/
theorem seqProb_zero [Nonempty α] :
    u.seqProb (fun _ => 0) = 1 := by
  unfold seqProb
  simp only [Nat.cast_zero, Finset.sum_const_zero, add_zero]
  rw [div_self (Gamma_pos_of_pos u.total_pos).ne', one_mul]
  apply Finset.prod_eq_one
  intro i _
  exact div_self (Gamma_pos_of_pos (u.pseudo_pos i)).ne'

/--
Per-sequence Pólya likelihood is strictly positive on nonempty
alphabets. Used by downstream consumers (`DMPCFG`, `AdaptorGrammar`)
to derive nonnegativity of corpus probabilities.
-/
theorem seqProb_pos [Nonempty α] (x : α → ℕ) :
    0 < u.seqProb x := by
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
  unfold seqProb
  exact mul_pos hRatio_pos hProd_pos

end PolyaUrn

end ProbabilityTheory
