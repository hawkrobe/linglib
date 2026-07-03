import Linglib.Core.Computability.ContextFreeGrammar.Tree
import Linglib.Core.Computability.ContextFreeGrammar.Weighted
import Linglib.Core.Probability.Entropy
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Multinomial probabilistic context-free grammar

[odonnell-2015]

The baseline stochastic CFG: for each nonterminal `A`, a multinomial
distribution over `A`'s expansions; the probability of a derivation
tree factorizes as the product of the rule weights it uses, and the
probability of a corpus factorizes across derivations.

This construction predates [odonnell-2015] by decades — see
Booth 1969, Booth & Thompson 1973, Chi & Geman 1998 for the
canonical literature on PCFG and per-LHS multinomial structure (these
are not yet in `references.bib`; cite-key additions deferred).
[odonnell-2015] §3.1.2 gives the didactic treatment we follow
for notation and as the substrate for the §3.1.4–§3.1.8 family of
*priors over* multinomial PCFGs (DMPCFG, MAG, FG) that build on this
baseline.

## Factorization ([odonnell-2015] eq 3.2 + eq 3.5)

Per [odonnell-2015] eq 3.2, the per-derivation probability is
the product of the rule weights it uses:

```
P(d | G) = ∏_{r ∈ d} θ_r          (eq 3.2)
```

Per [odonnell-2015] eq 3.5, the corpus probability collects
these into a single product over rules:

```
P(D | G) = ∏_{A ∈ V_NT} ∏_{r ∈ R^A} (θ_r^A)^{x_r^A}     (eq 3.5)
```

`derivProb` formalizes eq 3.2; `corpusProb` is its natural lift to a
multiset of derivations. The count-form (eq 3.5) is provably
equivalent to the per-derivation form (`corpusProb_eq_prod_pow_count`,
deferred — needs `derivRuleCount` extracted from `DMPCFG` to a
shared substrate first).

The factorization across derivations (`corpusProb_add`) is what
distinguishes the multinomial-PCFG baseline from its richer-prior
descendants `DMPCFG`, `MAG`, `FG`, where exchangeable Pólya / PYP /
beta-binomial state couples derivations through shared corpus-aggregate
counts. `DOP` estimators (DOP1, ENDOP) also factorize via Goodman
1998/2003's PCFG reductions, despite being on the
"non-baseline" side of the substrate; see `Comparisons.lean`.

## Architecture

`MultinomialPCFG G` is a single point in weight space: for each LHS,
a `PMF` over its rule bucket. Mathlib's `PMF` discipline is genuine
here, not aspirational — normalization is part of what a probability
mass function *is*, so the previous `ruleProb_nonneg` /
`ruleProb_normalized` side conditions disappear and `noncomputable` is
forced only by `PMF`'s `ℝ≥0∞` carrier (not by our use of `ℝ`).

The forgetful projection to `WeightedCFG G ℝ≥0∞` (`Core/Computability/
WeightedCFG.lean`) is `toWeightedCFG`. The bridge from richer-prior
descendants is the *function* `DMPCFG.posteriorMAP : DMPCFG G →
Multiset _ → MultinomialPCFG G` (`DMPCFG.lean`): collapse a Dirichlet
prior, conditioned on a corpus, into its MAP point estimate. DMPCFG
does **not** `extends MultinomialPCFG`; the two are conceptually
distinct objects — a prior over weight-points versus a single
weight-point.

The structure requires `[∀ a : G.NT, Nonempty (G.RulesWithLHS a)]`:
PMFs over empty supports don't exist, so grammars with "useless"
nonterminals (no expansion) cannot carry a `MultinomialPCFG`. This
constraint is now structural rather than implicit (the previous
`ruleProb_normalized` field demanded sum = 1 for every `a`, which was
unsatisfiable when the LHS bucket was empty).

## Main definitions

- `MultinomialPCFG G` — per-LHS PMF over the LHS rule bucket.
- `MultinomialPCFG.ruleProb` — per-rule probability (PMF mass on the
  rule's LHS bucket when `r ∈ G.rules`, else 0).
- `MultinomialPCFG.toWeightedCFG` — forgetful projection to
  `WeightedCFG G ℝ≥0∞`.
- `MultinomialPCFG.derivProb` — per-derivation probability, recursive
  product of rule weights through the tree (eq 3.2).
- `MultinomialPCFG.corpusProb` — corpus probability as the product of
  per-derivation probabilities.

## Main theorems

- `MultinomialPCFG.corpusProb_add` — multiplicativity over disjoint
  corpora (the Lean content of the "derivations are independent"
  claim).
- `MultinomialPCFG.corpusProb_zero` — empty corpus has probability 1.

## References

- [odonnell-2015] §3.1.2 (eq 3.2 + eq 3.5).
-/

namespace Morphology.FragmentGrammars

open scoped ENNReal

/--
A *multinomial PCFG* over `G`: for each nonterminal `a`, a `PMF` over
the rules with LHS `a`. Per [odonnell-2015] §3.1.2.

The structure carries normalization as a *structural* property via
mathlib's `PMF` (the partition function is bundled into what a `PMF`
is), eliminating the hand-rolled `ruleProb_nonneg` / `ruleProb_normalized`
side conditions that the previous shape carried.

Requires `[∀ a, Nonempty (G.RulesWithLHS a)]` because `PMF.ofFintype`
fails on empty supports — grammars with "useless nonterminals" (no
rules) cannot carry a `MultinomialPCFG`.
-/
@[ext]
structure MultinomialPCFG {T : Type} [DecidableEq T]
    (G : ContextFreeGrammar T) [DecidableEq G.NT]
    [∀ a : G.NT, Nonempty (G.RulesWithLHS a)] where
  /-- Per-LHS distribution over the rules sharing that LHS. -/
  rulePMF : (a : G.NT) → PMF (G.RulesWithLHS a)

namespace MultinomialPCFG

variable {T : Type} [DecidableEq T] {G : ContextFreeGrammar T}
  [DecidableEq G.NT] [∀ a : G.NT, Nonempty (G.RulesWithLHS a)]

/--
Per-rule probability under a multinomial PCFG: the PMF mass at the
rule's LHS bucket if `r ∈ G.rules`, else `0`. The case split is on
membership in the bucket `G.rules.filter (·.input = r.input)`, which
is equivalent to `r ∈ G.rules` (the LHS-equality side is trivially
true).

Returns `ℝ≥0∞` rather than `ℝ` so that nonnegativity is structural
and the value composes with mathlib's `PMF` API directly. The `ℝ`
view is `ENNReal.toReal ∘ ruleProb`.
-/
noncomputable def ruleProb (W : MultinomialPCFG G)
    (r : ContextFreeRule T G.NT) : ℝ≥0∞ :=
  if h : r ∈ G.rules.filter (·.input = r.input) then
    W.rulePMF r.input ⟨r, h⟩
  else 0

/-- The per-rule probability is `0` for rules outside the grammar.
    The `MultinomialPCFG` only assigns mass to rules of `G`; anything
    outside is implicitly weight `0`. -/
@[simp]
theorem ruleProb_eq_zero_of_not_mem (W : MultinomialPCFG G)
    {r : ContextFreeRule T G.NT} (hr : r ∉ G.rules) :
    W.ruleProb r = 0 := by
  unfold ruleProb
  rw [dif_neg]
  intro h
  exact hr (Finset.mem_filter.mp h).1

/-- The per-rule probability matches the PMF mass when `r ∈ G.rules`.
    The bucket-membership proof is reconstructed from `r ∈ G.rules`
    plus the trivial `r.input = r.input`. -/
theorem ruleProb_eq_pmf (W : MultinomialPCFG G)
    {r : ContextFreeRule T G.NT} (hr : r ∈ G.rules) :
    W.ruleProb r = W.rulePMF r.input
        ⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩⟩ := by
  unfold ruleProb
  rw [dif_pos]

/--
Forgetful projection to the unbundled weighted-CFG substrate
(`Core/Computability/WeightedCFG.lean`). The weights live in `ℝ≥0∞`,
with nonnegativity automatic by typing.

This is the projection promised by the previous-version docstring
("the unbundled 'weighted CFG' is genuinely useful for theories
where weights are not yet normalized; will be introduced when the
first such consumer arrives") — `DMPCFG` is that consumer; this is
the projection from `MultinomialPCFG` into the new shared substrate.
-/
noncomputable def toWeightedCFG (W : MultinomialPCFG G) :
    WeightedCFG G ℝ≥0∞ where
  weight := W.ruleProb
  weight_nonneg _ := zero_le

mutual
/-- Per-derivation probability under a multinomial PCFG
    ([odonnell-2015] eq 3.2). Recurses on the tree structure:
    each internal node contributes the weight of the rule it
    instantiates, leaves contribute `1`. Invalid rules (those not in
    `G.rules`) contribute `0` via `ruleProb`'s default. -/
noncomputable def derivProb (W : MultinomialPCFG G) :
    CFGTree T G.NT → ℝ≥0∞
  | .leaf _ => 1
  | .node nt cs =>
      W.ruleProb ⟨nt, cs.map CFGTree.rootSymbol⟩ * derivProbList W cs

/-- Product of derivation probabilities over a list of subtrees. -/
noncomputable def derivProbList (W : MultinomialPCFG G) :
    List (CFGTree T G.NT) → ℝ≥0∞
  | [] => 1
  | t :: ts => derivProb W t * derivProbList W ts
end

/--
Corpus probability of a multiset of derivations: the product of their
individual `derivProb` values. By construction this factorizes
multiplicatively over disjoint corpora — see `corpusProb_add`. The
count-form ([odonnell-2015] eq 3.5) is mathematically equivalent
but deferred (`corpusProb_eq_prod_pow_count`) until `derivRuleCount`
is extracted from `DMPCFG` to a shared substrate file.
-/
noncomputable def corpusProb (W : MultinomialPCFG G)
    (D : Multiset (CFGTree T G.NT)) : ℝ≥0∞ :=
  (D.map W.derivProb).prod

/-- The empty corpus has probability `1` — the empty product. -/
@[simp]
theorem corpusProb_zero (W : MultinomialPCFG G) :
    W.corpusProb (0 : Multiset (CFGTree T G.NT)) = 1 := by
  unfold corpusProb
  rw [Multiset.map_zero, Multiset.prod_zero]

/--
Multiplicativity over disjoint corpora: the corpus probability of a
union of two sub-corpora is the product of their corpus
probabilities. This is the Lean content of the "derivations are
independent" claim that distinguishes multinomial PCFGs from their
richer-prior descendants (`DMPCFG`, `MAG`, `FG`) — see
`Comparisons.lean` for the formal contrast.

Trivially true here by `Multiset.prod_add`; the *content* is that
the analogous theorem for `DMPCFG.corpusProb` *fails* (because the
Pólya factor couples derivations through shared rule counts).
-/
theorem corpusProb_add (W : MultinomialPCFG G)
    (D₁ D₂ : Multiset (CFGTree T G.NT)) :
    W.corpusProb (D₁ + D₂) = W.corpusProb D₁ * W.corpusProb D₂ := by
  unfold corpusProb
  rw [Multiset.map_add, Multiset.prod_add]

/-! ## Concrete instances -/

/-- The **uniform** multinomial PCFG: each LHS bucket gets the
    uniform distribution over its rules. The canonical baseline
    instance — the one a maximum-entropy estimator returns at zero
    data, useful as a reference point and as the `Inhabited` witness.

    Maximum-entropy property: for each LHS, this distribution maximizes
    `PMF.entropy` over the rule bucket. -/
noncomputable def uniform : MultinomialPCFG G where
  rulePMF a := PMF.uniformOfFintype (G.RulesWithLHS a)

noncomputable instance : Inhabited (MultinomialPCFG G) := ⟨uniform⟩

/-! ## Information-theoretic primitives (bridge to `Entropy`)

The per-LHS PMFs let us inherit mathlib's PMF entropy / KL machinery
directly. These primitives are the integration bridge to processing-cost
theories (`Processing/Memory/`): rule-weight entropy
gives the local uncertainty at each nonterminal expansion choice, and
KL between two MultinomialPCFGs measures how different their
rule-weight predictions are. -/

/-- Per-LHS entropy: entropy of the PMF over the rules with the given
    LHS. The local "uncertainty" of which expansion will be chosen for
    nonterminal `a`. Inherited via `PMF.entropy`. -/
noncomputable def lhsEntropy (W : MultinomialPCFG G) (a : G.NT) : ℝ :=
  (W.rulePMF a).entropy

/-- Entropy is nonneg — direct corollary of `PMF.entropy_nonneg`. -/
theorem lhsEntropy_nonneg (W : MultinomialPCFG G) (a : G.NT) :
    0 ≤ W.lhsEntropy a :=
  (W.rulePMF a).entropy_nonneg

/-! ## Count-form factorization ([odonnell-2015] eq 3.5) -/

/--
**The count-form factorization** ([odonnell-2015] eq 3.5).
For a corpus `D` of *valid* derivation trees, the corpus probability
collects rule contributions into a single product over the grammar's
rules raised to their corpus counts:

```
P(D | G) = ∏_{r ∈ G.rules} (W.ruleProb r) ^ (corpusRuleCount r D)
```

The validity precondition is essential: invalid trees use rules
outside `G.rules`, so the per-derivation product `derivProb` collapses
to 0 (via `ruleProb`'s default), but the count-form product over
`G.rules` ignores those rules and would compute a nonzero value.
For valid trees the two coincide.

**Status: stated, sorried.** Proof requires (1) per-tree count-form
`derivProb t = ∏_{r ∈ G.rules} ruleProb r ^ ruleCount r t` for valid
`t`, by mutual induction on `CFGTree`/`derivProb`'s mutual structure;
then (2) Multiset induction on `D` using `corpusProb_add` +
`corpusRuleCount_add` + `Finset.prod_pow_add`. The mutual induction
in (1) is the hard part — Lean's auto-generated `derivProb.induct`
needs careful handling. Architecture is in place; mechanical proof
deferred to a focused session. -/
theorem corpusProb_eq_prod_pow_count (W : MultinomialPCFG G)
    (D : Multiset (CFGTree T G.NT)) (h : ∀ t ∈ D, t.ValidFor G) :
    W.corpusProb D =
      ∏ r ∈ G.rules, (W.ruleProb r) ^ (CFGTree.corpusRuleCount r D) := by
  -- TODO: prove via per-tree count-form + Multiset induction
  sorry

end MultinomialPCFG

end Morphology.FragmentGrammars
