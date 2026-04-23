import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Real.Basic
import Linglib.Core.Computability.CFGTree

/-!
# Fragment grammars: abstract API

@cite{odonnell-2015}

A *stochastic generator* over a CFG `G` is an assignment of
probability mass to multisets of derivations of `G`. This is the
abstract API satisfied by all five FG-family models in
@cite{odonnell-2015}:

| Model | Storage strategy | Section |
|---|---|---|
| Multinomial PCFG | (no learning prior) | §3.1.2 |
| Dirichlet–multinomial PCFG (`DMPCFG`) | full-parsing | §3.1.4 |
| MAP Adaptor Grammar (`MAG`) | full-listing | §3.1.7 |
| Fragment Grammar (`FG`) | inference-based | §3.1.8 |
| Data-Oriented Parsing (`DOP1` / `ENDOP`) | exemplar-based | §3.1.5 |

Each model in `Theories/Morphology/FragmentGrammars/` provides its
own concrete construction and a `toStochasticGenerator` projection.

## Why a structure rather than a typeclass?

There can be many stochastic generators over the same CFG —
corresponding to different parameter choices (rule weights,
hyperparameters, fragment-storage choices). Following the mathlib
convention for `MeasureTheory.Measure α` (a structure on `α`, not a
typeclass), we declare `StochasticGenerator G` as a structure: a
specific generator is data, not an attribute of `G` to be
type-class–inferred.

## Why corpora rather than single derivations?

For multinomial PCFGs the corpus probability factorizes:
`P(D | G) = Π_{d ∈ D} P(d | G)`. For `DMPCFG`, `MAG`, `FG`, and
`DOP` it does *not* factorize — these models are *exchangeable but
not independent* across derivations because of shared latent state
(Dirichlet-prior over rule weights, Pitman–Yor partition over
fragments, etc.). The abstract API therefore takes corpora as
inputs; the special case where the corpus probability factorizes is
captured downstream by the multinomial-PCFG instance.

## Main definitions

- `StochasticGenerator G` — corpus-probability assignment over `G`
  with nonnegativity.

## References

- @cite{odonnell-2015} §3.1.2 (eq 3.4–3.5), §3.1.4 (eq 3.9), §3.1.5
  (DOP), §3.1.7 (AG), §3.1.8 (FG).
-/

namespace Morphology.FragmentGrammars

/--
A *stochastic generator* over the context-free grammar `G` assigns
probability mass to multisets of derivations of `G`. The five
FG-family models in @cite{odonnell-2015} all instantiate this
structure via a `toStochasticGenerator` projection.

For some models (multinomial PCFG) the corpus probability
factorizes through individual derivation probabilities; for others
(`DMPCFG`, `MAG`, `FG`) it does not, because of shared latent state
across derivations. The structure abstracts over both cases.
-/
@[ext]
structure StochasticGenerator {T : Type} (G : ContextFreeGrammar T) where
  /-- Probability mass for a corpus of derivations. -/
  corpusProb : Multiset (CFGTree T G.NT) → ℝ
  /-- Probabilities are nonnegative. -/
  corpusProb_nonneg : ∀ D, 0 ≤ corpusProb D

end Morphology.FragmentGrammars
