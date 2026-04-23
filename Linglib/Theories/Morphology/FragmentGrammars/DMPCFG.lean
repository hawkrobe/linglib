import Linglib.Core.Computability.CFGTree
import Linglib.Core.Probability.PolyaUrn
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
not independent*. The corpus probability is a corpus-level function;
there is no clean per-derivation factorization to expose.

## Connection to `PolyaUrn`

The per-LHS factor `lhsFactor M D A` IS the closed-form Pólya-urn
partition probability over rules with LHS `A`, using `M.pseudo`
restricted to those rules. The Type-polymorphic `PolyaUrn α` from
`Linglib.Core.Probability.PolyaUrn` is constructed per-LHS via
`lhsUrn`; positivity of `corpusProb` is derived structurally from
`PolyaUrn.partitionProb_pos`.

## Main definitions

- `DMPCFG G` — per-rule Dirichlet pseudo-counts.
- `DMPCFG.derivRuleCount` — count of rule applications in one
  derivation tree.
- `DMPCFG.corpusRuleCount` — count of rule applications across a
  corpus.
- `DMPCFG.lhsUrn` — per-LHS `PolyaUrn` over the subtype of rules
  with that LHS.
- `DMPCFG.lhsCounts` — per-LHS corpus counts as a function on the
  subtype.
- `DMPCFG.lhsFactor` — per-LHS Pólya partition probability
  (delegates to `PolyaUrn.partitionProb`).
- `DMPCFG.corpusProb` — eq 3.9 closed-form corpus probability.

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

/-- The subtype of rules with LHS `a` (as a sort, for indexing). -/
abbrev RulesWithLHS (a : G.NT) : Type :=
  { r : ContextFreeRule T G.NT // r ∈ G.rules.filter (·.input = a) }

/--
Per-LHS Pólya urn over the subtype of rules with LHS `a`,
parameterized by `M.pseudo` restricted to those rules.
-/
noncomputable def lhsUrn (a : G.NT) :
    ProbabilityTheory.PolyaUrn (RulesWithLHS (G := G) a) where
  pseudo := fun ⟨r, _⟩ => M.pseudo r
  pseudo_pos := fun ⟨r, hr⟩ => M.pseudo_pos r (Finset.mem_filter.mp hr).1

/-- Per-LHS corpus rule-count vector as a function on the subtype. -/
def lhsCounts (a : G.NT) (D : Multiset (CFGTree T G.NT)) :
    RulesWithLHS (G := G) a → ℕ :=
  fun ⟨r, _⟩ => corpusRuleCount r D

/--
Per-LHS factor in the eq 3.9 product: the Pólya partition probability
of the corpus rule-counts under the per-LHS pseudo-counts.

```
  Γ(Σ π_i^A) / Γ(Σ π_i^A + Σ x_i^A)  ·  ∏_i Γ(π_i^A + x_i^A) / Γ(π_i^A) .
```
-/
noncomputable def lhsFactor (a : G.NT) (D : Multiset (CFGTree T G.NT)) : ℝ :=
  (M.lhsUrn a).partitionProb (lhsCounts a D)

/--
DMPCFG corpus probability — eq 3.9 of @cite{odonnell-2015}. Product
over LHSs that appear in the grammar of the per-LHS Pólya factor.
LHSs with no rules in `G` contribute trivially (empty image term)
so the product is over `G.rules.image (·.input)`.
-/
noncomputable def corpusProb (D : Multiset (CFGTree T G.NT)) : ℝ :=
  ∏ a ∈ G.rules.image (·.input), M.lhsFactor a D

omit [DecidableEq T] in
/-- For LHSs that have at least one rule, the subtype is nonempty. -/
theorem nonempty_rulesWithLHS_of_mem_image {a : G.NT}
    (ha : a ∈ G.rules.image (·.input)) :
    Nonempty (RulesWithLHS (G := G) a) := by
  obtain ⟨r0, hr0_mem, hr0_input⟩ := Finset.mem_image.mp ha
  exact ⟨r0, Finset.mem_filter.mpr ⟨hr0_mem, hr0_input⟩⟩

/-- The per-LHS factor is strictly positive when the LHS has rules.
    Direct corollary of `PolyaUrn.partitionProb_pos`. -/
theorem lhsFactor_pos {a : G.NT} (ha : a ∈ G.rules.image (·.input))
    (D : Multiset (CFGTree T G.NT)) : 0 < M.lhsFactor a D := by
  haveI := nonempty_rulesWithLHS_of_mem_image ha
  exact (M.lhsUrn a).partitionProb_pos _

/-- DMPCFG corpus probabilities are nonnegative (in fact, positive). -/
theorem corpusProb_nonneg (D : Multiset (CFGTree T G.NT)) :
    0 ≤ M.corpusProb D := by
  unfold corpusProb
  apply Finset.prod_nonneg
  intro a ha
  exact (M.lhsFactor_pos ha D).le

end DMPCFG

end Morphology.FragmentGrammars
