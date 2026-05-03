import Mathlib.Tactic.Simps.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# `pmf_eval_simps` — registered simp set for closed-form PMF reduction

A `simp` attribute + macro for evaluating PMF expressions of the form
`(some_PMF) a` to a closed-form `ENNReal.ofReal _` shape that
`norm_num` / `decide` can finish.

## Two-layer mathlib pattern

* **`pmf_eval_simps`** (here): registered simp attribute, sibling of
  `mfld_simps`, `parity_simps`, `monad_norm`. Tags closed-form PMF
  reductions ONLY (no arithmetic glue, no `if_true`, no `Fin.sum_univ_*`).
* **`pmf_eval`** (here): tactic macro that runs `simp only` on the set
  composed with the standard arithmetic glue (if-collapse, sum unfolders,
  ENNReal arithmetic) listed explicitly in the macro body, then a closer
  attempt.
* **`EvalLemmas.lean`**: tags the universal lemmas (`PMF.pure_apply`,
  `bind_apply_eq_finset_sum`, `hypergeometric_apply_eq_ofReal`, etc.).

## Domain

Goals where the LHS is a PMF expression at a fully-instantiated point
and the RHS is a closed-form rational. The macro composes the simp set
with the inevitable arithmetic glue right inside the macro body — visible
at the call site, not silently inherited via the simp set.

## Usage

```lean
example : (PMF.uniformOfFintype (Fin 4)) 0 = (4 : ℝ≥0∞)⁻¹ := by
  pmf_eval
```

## Decide invocation

`pmf_eval` enables `simp (config := { decide := true })`. This is the
kernel-decidability oracle — it lets `simp` fire `if c then a else b`
when `c` is decidable (e.g. `qualityOk … = true` after deciding the
predicate). **The cost**: `simp` will evaluate any `Decidable` instance
in scope; a slow instance can blow up elaboration time.

Use `pmf_eval_no_decide` / `pmf_eval_only` for the simp-only variants
when this is a concern.

## What it does NOT handle

Hypothesis-laden lemmas whose preconditions aren't decidable from the
syntactic form. Domain consumers (RSA papers) should derive `_apply_eq_ite`
variants in their own files and apply `local attribute [pmf_eval_simps]`
rather than polluting the substrate set with `private` paper-tagged lemmas.
-/

/-- Simp set for `pmf_eval`: closed-form PMF reductions. Domain-specific
reductions should be added via `local attribute [pmf_eval_simps]` in
the consumer file to avoid cross-file pollution. -/
register_simp_attr pmf_eval_simps

/-! ## The `pmf_eval` macros

The macro composes the simp set with the inevitable arithmetic glue
(if-collapse, sum unfolders, ENNReal arithmetic) explicitly. The glue is
listed inside the macro definition rather than tagged into the simp set
— so it's visible at the macro definition site and not silently inherited
by every consumer of `pmf_eval_simps`.

Three variants:
* `pmf_eval` — full chain with `decide := true`, closes via
  `norm_num`/`decide`/`rfl` waterfall. The standard call.
* `pmf_eval_no_decide` — same chain WITHOUT `decide := true`. Use when
  the kernel-eval oracle is undesirable (e.g. slow Decidable instances
  in scope).
* `pmf_eval_only` — `simp only` on the set + glue, no closer. Use when
  the residual needs follow-up tactics like `gcongr` or `ennreal_close`. -/

macro "pmf_eval" : tactic => `(tactic|
  (simp (config := { decide := true }) only
        [pmf_eval_simps, if_true, if_false, ↓reduceIte,
         add_zero, zero_add, ENNReal.ofReal_zero,
         Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four];
   first | done | norm_num | decide | rfl))

macro "pmf_eval_no_decide" : tactic => `(tactic|
  (simp only [pmf_eval_simps, if_true, if_false, ↓reduceIte,
              add_zero, zero_add, ENNReal.ofReal_zero,
              Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four];
   first | done | norm_num | decide | rfl))

macro "pmf_eval_only" : tactic => `(tactic|
  simp (config := { decide := true }) only
       [pmf_eval_simps, if_true, if_false, ↓reduceIte,
        add_zero, zero_add, ENNReal.ofReal_zero,
        Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four])

/-! ## `ennreal_close` — residual closer for `ofReal` arithmetic comparisons

After `pmf_eval_only`, residuals of the form
`ofReal a + ofReal b + ... < ofReal x + ofReal y + ...` (or `≤` / `=`) appear
when the partition functions of two PMFs are compared. The standard close is:

1. Combine each `ofReal a + ofReal b` into `ofReal (a + b)` via
   `← ENNReal.ofReal_add` (with positivity side-conditions).
2. Apply `ENNReal.ofReal_{lt,le,eq}_ofReal_iff` to reduce to a real comparison.
3. Finish with `norm_num`.

`ennreal_close` packages this. `gcongr` doesn't apply because `ENNReal` lacks
an `AddLeftStrictMono` instance (⊤ + a = ⊤ + b would block strict cancellation).
-/

macro "ennreal_close" : tactic => `(tactic|
  (-- Pre-normalization: drop spurious `* 0` / `+ 0` so the `← ofReal_add`
   -- positivity proofs don't get tripped up by un-simplified subexpressions.
   try simp only [mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one];
   -- Combine ofReal sums: `ofReal a + ofReal b → ofReal (a + b)`.
   repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)];
   -- Combine ofReal products: `ofReal a * ofReal b → ofReal (a * b)`.
   repeat rw [← ENNReal.ofReal_mul (by positivity)];
   -- After combining, sums may have a residual ofReal-times-ofReal that re-introduces +.
   repeat rw [← ENNReal.ofReal_add (by positivity) (by positivity)];
   first
     | exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
     | exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mpr (by norm_num)
     | exact ENNReal.ofReal_le_ofReal (by norm_num)
     | (congr 1; norm_num)
     | norm_num))
