import Mathlib.Tactic.Simps.Basic

/-!
# `pmf_eval_simps` — registered simp set for closed-form PMF reduction

A registered simp attribute, sibling of `mfld_simps`, `parity_simps`,
`monad_norm`. Tags lemmas of the form "PMF expression at a fully-instantiated
point = closed `ENNReal.ofReal` form" — no arithmetic glue (`if_true`,
`Fin.sum_univ_*`, `add_zero` come from the default simp set at call sites).

* **`EvalLemmas.lean`** tags the universal lemmas (`PMF.pure_apply`,
  `bind_apply_eq_finset_sum`, `hypergeometric_apply_eq_ofReal`, etc.).
* Domain-specific reductions (RSA softmaxBelief if-forms, paper-specific
  extension cardinalities) belong with their declaration site, scoped
  `local attribute [pmf_eval_simps]`, to avoid cross-file pollution of a
  substrate set.

Call sites use `simp +decide [pmf_eval_simps]` (the `+decide` fires
`if c then _ else _` branches whose condition is a decidable predicate),
followed by an explicit `norm_num`/`rw` closer where a residual remains.
The former `pmf_eval` / `ennreal_close` closer macros are retired: proofs
state their reductions explicitly.
-/

/-- Simp set for closed-form PMF reductions. Domain-specific
reductions should be added via `local attribute [pmf_eval_simps]` in
the consumer file to avoid cross-file pollution. -/
register_simp_attr pmf_eval_simps
