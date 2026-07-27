import Linglib.Morphology.FragmentGrammars.DMPCFG
import Linglib.Morphology.FragmentGrammars.MultinomialPCFG

/-!
# FG-family cross-model comparisons

[odonnell-2015]

Theorems that pit `MultinomialPCFG`, `DMPCFG`, and (eventually) `MAG`
/ `FG` against each other on shared mathematical content. Anchored
on [odonnell-2015] §3.1 ontology of priors over multinomial
PCFGs.

## Architecture

These theorems live here, not in `MultinomialPCFG.lean` or
`DMPCFG.lean`, because they reason about *both* substrates and would
otherwise force one to import the other unnecessarily. Mirrors the
mathlib pattern of `*/Comparison.lean` files (e.g.
`Mathlib/Order/MinMax.lean` patterns relating different order
structures).

## Main theorems

- `dmpcfg_corpus_strictly_couples` — there exists a DMPCFG and corpus
  whose corpus probability *differs* from the corpus probability of
  its posterior-MAP MultinomialPCFG. Witnesses the "exchangeable but
  not independent" claim that both `MultinomialPCFG.lean` and
  `DMPCFG.lean` docstrings assert.

  **Status: stated, sorried.** Proof requires numeric construction of
  a 2-rule-per-LHS grammar + 2-derivation corpus with explicit
  `pseudo` values; the Pólya factor `(π₁)(π₂)/((π₁+π₂)(π₁+π₂+1))`
  must be shown distinct from the multinomial product
  `(π₁/(π₁+π₂)) · (π₂/(π₁+π₂))` — these differ by factor
  `(π₁+π₂)/(π₁+π₂+1) < 1`. Concrete witness deferred.
-/

namespace Morphology.FragmentGrammars

open scoped ENNReal

variable {T : Type} [DecidableEq T]
  {G : ContextFreeGrammar T} [DecidableEq G.NT]
  [∀ a : G.NT, Nonempty (G.RulesWithLHS a)]

/--
**The non-factorization counterexample.** There exists a DMPCFG
and a corpus whose DMPCFG corpus probability differs from the
multinomial-PCFG corpus probability of the corresponding posterior
MAP estimate.

This is the formal Lean witness of the "exchangeable but not
independent" claim that distinguishes DMPCFG from MultinomialPCFG.
The two assertions in the file docstrings of `MultinomialPCFG.lean`
("factorization is what distinguishes the multinomial-PCFG baseline
from its richer-prior descendants") and `DMPCFG.lean` ("`P(D | M) ≠
∏_d P(d | M)` — DMPCFG derivations are exchangeable but not
independent") collapse onto this single existential.

**Proof obligation (sorried for now).** Take any 2-rule-per-LHS
toy grammar; pick `pseudo` constant on those two rules; pick a corpus
of two derivations exercising the two rules. The DMPCFG side
produces a Pólya factor `Γ(π_total)/Γ(π_total+2) · Γ(π_1+1)Γ(π_2+1)
/ Γ(π_1)Γ(π_2)` which strictly differs from the per-derivation
product `(mapWeight r₁) · (mapWeight r₂)` of MAP weights.

The infrastructure is in place: `DMPCFG.posteriorMAP`,
`MultinomialPCFG.corpusProb`, and `DMPCFG.corpusProb` are all
defined; what's missing is the numeric witness and the explicit
Pólya-vs-product computation. -/
theorem dmpcfg_corpus_strictly_couples
    {T : Type} [DecidableEq T] :
    ∃ (G : ContextFreeGrammar T) (_ : DecidableEq G.NT)
      (_ : ∀ a : G.NT, Nonempty (G.RulesWithLHS a))
      (M : DMPCFG G) (D : Multiset (DerivationTree T G.NT)),
      ENNReal.ofReal (M.corpusProb D) ≠ (M.posteriorMAP D).corpusProb D := by
  -- TODO: concrete 2-rule grammar + 2-derivation corpus + numeric inequality.
  -- Architecture is in place; only the witness construction is deferred.
  sorry

end Morphology.FragmentGrammars
