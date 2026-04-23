import Linglib.Core.Computability.CFGTree
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset

/-!
# Multinomial probabilistic context-free grammar

@cite{odonnell-2015}

The simplest stochastic CFG @cite{odonnell-2015} §3.1.2: each
production rule carries a fixed weight, weights for rules with the
same left-hand side sum to one, and the probability of a derivation
factorizes through the rules used. Equivalently, for each
nonterminal there is a multinomial distribution over its expansions.

Per @cite{odonnell-2015} eq 3.5, the corpus probability is

```
P(D | G) = ∏_{A ∈ V_NT} ∏_{r ∈ R^A} (θ_r^A)^{x_r^A}
```

which factorizes through individual derivation probabilities

```
P(d | G) = ∏_{r ∈ d} θ_r .
```

This factorization is what distinguishes multinomial PCFGs from the
other FG-family models (`DMPCFG`, `MAG`, `FG`, `DOP`), which couple
derivations through shared latent state.

## Main definitions

- `MultinomialPCFG G` — per-LHS multinomial weights with bundled
  normalization (mathlib's `PMF`/`ProbabilityMeasure` discipline:
  normalization is part of what a probability distribution *is*).
- `MultinomialPCFG.derivProb` — per-derivation probability,
  recursive on the tree structure.
- `MultinomialPCFG.corpusProb` — corpus probability as the product
  of derivation probabilities.

## References

- @cite{odonnell-2015} §3.1.2 (eq 3.4–3.5).
-/

namespace Morphology.FragmentGrammars

/--
A *multinomial PCFG* over `G`: rule weights are nonnegative and
sum to `1` for each left-hand-side nonterminal. Per
@cite{odonnell-2015} §3.1.2.

We bundle normalization into the structure (mathlib's `PMF`
discipline) rather than keeping it as a separate `Prop`. The
unbundled "weighted CFG" is genuinely useful for theories where
weights are not yet normalized (e.g. `DMPCFG`'s pre-Dirichlet
hyperparameters), and will be introduced when the first such
consumer arrives — per "don't speculatively factor."
-/
@[ext]
structure MultinomialPCFG {T : Type} (G : ContextFreeGrammar T) [DecidableEq G.NT] where
  /-- Probability mass for each rule. -/
  ruleProb : ContextFreeRule T G.NT → ℝ
  /-- Rule probabilities are nonnegative. -/
  ruleProb_nonneg : ∀ r, 0 ≤ ruleProb r
  /-- Per-LHS rule probabilities sum to one. -/
  ruleProb_normalized : ∀ a : G.NT,
    ∑ r ∈ G.rules.filter (·.input = a), ruleProb r = 1

namespace MultinomialPCFG

variable {T : Type} {G : ContextFreeGrammar T} [DecidableEq G.NT]

mutual
/-- Probability of a single derivation tree under the rule weights.
    Recurses on the tree structure: each internal node contributes
    the weight of the rule it instantiates. -/
noncomputable def derivProb (W : MultinomialPCFG G) :
    CFGTree T G.NT → ℝ
  | .leaf _ => 1
  | .node nt cs =>
      W.ruleProb ⟨nt, cs.map CFGTree.rootSymbol⟩ * derivProbList W cs

/-- Product of derivation probabilities over a list of subtrees. -/
noncomputable def derivProbList (W : MultinomialPCFG G) :
    List (CFGTree T G.NT) → ℝ
  | [] => 1
  | t :: ts => derivProb W t * derivProbList W ts
end

mutual
/-- Derivation probabilities are nonnegative. -/
theorem derivProb_nonneg (W : MultinomialPCFG G) :
    ∀ t : CFGTree T G.NT, 0 ≤ W.derivProb t := by
  intro t
  match t with
  | .leaf _ => exact zero_le_one
  | .node _ cs =>
    show 0 ≤ W.ruleProb _ * W.derivProbList cs
    exact mul_nonneg (W.ruleProb_nonneg _) (derivProbList_nonneg W cs)

/-- List version of `derivProb_nonneg`. -/
theorem derivProbList_nonneg (W : MultinomialPCFG G) :
    ∀ ts : List (CFGTree T G.NT), 0 ≤ W.derivProbList ts := by
  intro ts
  match ts with
  | [] => exact zero_le_one
  | t :: rest =>
    show 0 ≤ W.derivProb t * W.derivProbList rest
    exact mul_nonneg (derivProb_nonneg W t) (derivProbList_nonneg W rest)
end

/--
Corpus probability of a multiset of derivations: the product of
their individual derivation probabilities. This is the factorized
form @cite{odonnell-2015} eq 3.5 — independence across derivations
is special to multinomial PCFGs and *fails* for `DMPCFG` / `MAG` /
`FG` / `DOP`.
-/
noncomputable def corpusProb (W : MultinomialPCFG G)
    (D : Multiset (CFGTree T G.NT)) : ℝ :=
  (D.map W.derivProb).prod

/-- Corpus probability is nonnegative. -/
theorem corpusProb_nonneg (W : MultinomialPCFG G)
    (D : Multiset (CFGTree T G.NT)) : 0 ≤ W.corpusProb D := by
  unfold corpusProb
  exact Multiset.prod_map_nonneg fun t _ => W.derivProb_nonneg t

end MultinomialPCFG

end Morphology.FragmentGrammars
