import Linglib.Core.Probability.Eval
import Linglib.Core.Probability.Hypergeometric
import Linglib.Core.Probability.Posterior
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform

/-!
# `pmf_eval_simps` lemma tags

Universal closed-form PMF reductions tagged into the `pmf_eval_simps` simp
set. This is the consumer file for the attribute registered in `Eval.lean`.
Tagging is split out because Lean requires `register_simp_attr` and
`attribute [...]` to live in different files.

## What lives here

**Only** lemmas of the form "PMF expression at a point = closed form".
Arithmetic glue (`if_true`, `if_false`, `add_zero`, `Fin.sum_univ_*`, etc.)
is composed explicitly at each call site, not tagged into this set.

Domain-specific reductions (RSA softmaxBelief if-form, paper-specific
extension cardinalities) belong with their declaration site, scoped
`local attribute [pmf_eval_simps]` to avoid cross-file pollution of a
substrate set.
-/

attribute [pmf_eval_simps]
  PMF.pure_apply
  PMF.bind_apply_eq_finset_sum
  PMF.normalize_apply
  PMF.uniformOfFintype_apply
  PMF.hypergeometric_apply
  PMF.hypergeometric_apply_eq_ofReal
