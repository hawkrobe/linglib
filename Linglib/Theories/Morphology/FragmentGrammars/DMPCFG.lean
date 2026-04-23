import Linglib.Theories.Morphology.FragmentGrammars.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Dirichlet–multinomial PCFG (DMPCFG)

@cite{odonnell-2015}

The "full-parsing" model of @cite{odonnell-2015} §2.4.1 / §3.1.4: a
PCFG with a Dirichlet prior on the per-LHS rule-weight vector.
Marginalizing out the rule weights yields the closed-form corpus
probability of eq 3.9 — the Dirichlet–multinomial likelihood.

```
P(D | M) = ∏_{A ∈ V}
  [ Γ(Σ_i π_i^A) / Γ(Σ_i π_i^A + Σ_i x_i^A)
    · ∏_i Γ(π_i^A + x_i^A) / Γ(π_i^A) ]
```

where `π_i^A` are the Dirichlet hyperparameters (pseudo-counts) for
the `i`-th rule with LHS `A`, and `x_i^A` is the count of that rule
across the corpus `D`.

## Why DMPCFG does not factorize

The crucial difference from a multinomial PCFG (`MultinomialPCFG`)
is that *the same rule's count enters the same Pólya term across all
derivations in the corpus*. Two derivations using rule `r` are
correlated through the shared `x_r` in the closed form. As a result,
`P(D | M) ≠ ∏_d P(d | M)` — DMPCFG derivations are *exchangeable but
not independent*. This is exactly why
`StochasticGenerator` takes corpora rather than single derivations.

## Connection to `PolyaUrn`

The per-LHS factor `lhsFactor M D A` is the closed-form Pólya-urn
partition probability over rules with LHS `A`, using `M.pseudo`
restricted to those rules. The formula is inlined here rather than
constructed from `Linglib.Core.Probability.PolyaUrn` because the
current `PolyaUrn (K : ℕ)` parameterization does not compose cleanly
with `Finset.filter`-shaped rule restrictions; bridging via subtypes
would require Type-polymorphic `PolyaUrn`, which we defer until a
second consumer needs it (per "don't speculatively factor").

## Main definitions

- `DMPCFG G` — per-rule Dirichlet pseudo-counts.
- `DMPCFG.derivRuleCount` — count of rule applications in one
  derivation tree.
- `DMPCFG.corpusRuleCount` — count of rule applications across a
  corpus.
- `DMPCFG.lhsFactor` — per-LHS Pólya partition factor.
- `DMPCFG.corpusProb` — eq 3.9 closed-form corpus probability.
- `DMPCFG.toStochasticGenerator` — projection to the abstract API.

## References

- @cite{odonnell-2015} §2.4.1, §3.1.4 (eq 3.7–3.9).
-/

namespace Morphology.FragmentGrammars

open Real

/--
A Dirichlet–multinomial PCFG over `G`: per-rule pseudo-counts that
parametrize a Dirichlet prior on the per-LHS rule-weight vector.

Per @cite{odonnell-2015} §2.4.1 the conditional distribution over
weights given a corpus is again Dirichlet (conjugacy), so the
posterior MAP weights are proportional to corpus rule frequencies.
-/
@[ext]
structure DMPCFG {T : Type} [DecidableEq T] (G : ContextFreeGrammar T)
    [DecidableEq G.NT] where
  /-- Per-rule pseudo-count (Dirichlet hyperparameter). -/
  pseudo : ContextFreeRule T G.NT → ℝ
  /-- Pseudo-counts are strictly positive on grammar rules. -/
  pseudo_pos : ∀ r ∈ G.rules, 0 < pseudo r

namespace DMPCFG

variable {T : Type} [DecidableEq T] {G : ContextFreeGrammar T} [DecidableEq G.NT]

mutual
/-- Number of times rule `r` is applied at internal nodes of the
    derivation tree `t`. -/
def derivRuleCount (r : ContextFreeRule T G.NT) :
    CFGTree T G.NT → ℕ
  | .leaf _ => 0
  | .node nt cs =>
      (if r = ⟨nt, cs.map CFGTree.rootSymbol⟩ then 1 else 0) +
      derivRuleCountList r cs

/-- List version of `derivRuleCount`. -/
def derivRuleCountList (r : ContextFreeRule T G.NT) :
    List (CFGTree T G.NT) → ℕ
  | [] => 0
  | t :: ts => derivRuleCount r t + derivRuleCountList r ts
end

/-- Total number of times rule `r` is used across the corpus `D`. -/
def corpusRuleCount (r : ContextFreeRule T G.NT)
    (D : Multiset (CFGTree T G.NT)) : ℕ :=
  (D.map (derivRuleCount r)).sum

variable (M : DMPCFG G)

/-- Sum of pseudo-counts over rules with LHS `a`: the `Σ π^A` term. -/
noncomputable def pseudoSumLHS (a : G.NT) : ℝ :=
  ∑ r ∈ G.rules.filter (·.input = a), M.pseudo r

/-- Total rule-count for rules with LHS `a` across the corpus: the `Σ x^A` term. -/
def corpusSumLHS (a : G.NT) (D : Multiset (CFGTree T G.NT)) : ℕ :=
  ∑ r ∈ G.rules.filter (·.input = a), corpusRuleCount r D

/--
Per-LHS Pólya–urn factor in the eq 3.9 product. For LHS `a` with
pseudo-counts `π_i^A` and corpus counts `x_i^A`,

```
  Γ(Σ π_i^A) / Γ(Σ π_i^A + Σ x_i^A)  ·  ∏_i Γ(π_i^A + x_i^A) / Γ(π_i^A) .
```
-/
noncomputable def lhsFactor (a : G.NT) (D : Multiset (CFGTree T G.NT)) : ℝ :=
  Gamma (M.pseudoSumLHS a) /
    Gamma (M.pseudoSumLHS a + (corpusSumLHS a D : ℝ)) *
    ∏ r ∈ G.rules.filter (·.input = a),
      Gamma (M.pseudo r + corpusRuleCount r D) / Gamma (M.pseudo r)

/--
DMPCFG corpus probability — eq 3.9 of @cite{odonnell-2015}. Product
over LHSs that appear in the grammar of the per-LHS Pólya factor.
LHSs with no rules in `G` contribute trivially (empty image term)
so the product is over `G.rules.image (·.input)`.
-/
noncomputable def corpusProb (D : Multiset (CFGTree T G.NT)) : ℝ :=
  ∏ a ∈ G.rules.image (·.input), M.lhsFactor a D

/-- For LHSs that have at least one rule, the pseudo-count sum is positive. -/
theorem pseudoSumLHS_pos {a : G.NT} (ha : a ∈ G.rules.image (·.input)) :
    0 < M.pseudoSumLHS a := by
  obtain ⟨r0, hr0_mem, hr0_input⟩ := Finset.mem_image.mp ha
  unfold pseudoSumLHS
  apply Finset.sum_pos
  · intro r hr
    rw [Finset.mem_filter] at hr
    exact M.pseudo_pos r hr.1
  · refine ⟨r0, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hr0_mem, hr0_input⟩

/-- The per-LHS factor is strictly positive when the LHS has rules. -/
theorem lhsFactor_pos {a : G.NT} (ha : a ∈ G.rules.image (·.input))
    (D : Multiset (CFGTree T G.NT)) : 0 < M.lhsFactor a D := by
  have h_psum_pos : 0 < M.pseudoSumLHS a := M.pseudoSumLHS_pos ha
  have h_corp_nn : (0 : ℝ) ≤ (corpusSumLHS a D : ℝ) := Nat.cast_nonneg _
  have hΓ_num_pos : 0 < Gamma (M.pseudoSumLHS a) := Gamma_pos_of_pos h_psum_pos
  have hΓ_den_pos : 0 < Gamma (M.pseudoSumLHS a + (corpusSumLHS a D : ℝ)) :=
    Gamma_pos_of_pos (by linarith)
  have hRatio_pos :
      0 < Gamma (M.pseudoSumLHS a) /
            Gamma (M.pseudoSumLHS a + (corpusSumLHS a D : ℝ)) :=
    div_pos hΓ_num_pos hΓ_den_pos
  have hProd_pos :
      0 < ∏ r ∈ G.rules.filter (·.input = a),
            Gamma (M.pseudo r + corpusRuleCount r D) / Gamma (M.pseudo r) := by
    apply Finset.prod_pos
    intro r hr
    rw [Finset.mem_filter] at hr
    have h_psr_pos : 0 < M.pseudo r := M.pseudo_pos r hr.1
    have h_corp_r_nn : (0 : ℝ) ≤ (corpusRuleCount r D : ℝ) := Nat.cast_nonneg _
    refine div_pos (Gamma_pos_of_pos ?_) (Gamma_pos_of_pos h_psr_pos)
    linarith
  unfold lhsFactor
  exact mul_pos hRatio_pos hProd_pos

/-- DMPCFG corpus probabilities are nonnegative (in fact, positive). -/
theorem corpusProb_nonneg (D : Multiset (CFGTree T G.NT)) :
    0 ≤ M.corpusProb D := by
  unfold corpusProb
  apply Finset.prod_nonneg
  intro a ha
  exact (M.lhsFactor_pos ha D).le

/-- DMPCFG induces a stochastic generator on `G`. -/
noncomputable def toStochasticGenerator : StochasticGenerator G where
  corpusProb := M.corpusProb
  corpusProb_nonneg := M.corpusProb_nonneg

end DMPCFG

end Morphology.FragmentGrammars
