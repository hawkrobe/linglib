import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Real.Basic

/-!
# Pitman–Yor process

@cite{odonnell-2015}

The Pitman–Yor process is a two-parameter Bayesian non-parametric
distribution generalizing the Chinese Restaurant Process (Dirichlet
process). It is the memoization distribution used by adaptor grammars
and fragment grammars in @cite{odonnell-2015} §2.3.4 and §2.3.6: each
nonterminal of a CFG is associated with a Pitman–Yor "restaurant"
whose tables hold previously-computed subderivations. The discount
parameter `a` controls the rate at which new tables (i.e. fresh
computations rather than memoized reuse) are created.

The sequential sampler (eq 3.12) is not formalized; only the
closed-form mass over partitions (eq 3.14), which is what downstream
FG-family constructions in `Theories/Probabilistic/Grammar/`
consume.

## Main definitions

- `stepPochhammer x s m` — iterated step product
  `x · (x + s) · (x + 2s) · … · (x + (m-1)s)` from
  @cite{odonnell-2015} eq 3.13. Generalizes the rising factorial
  (`s = 1`) and the geometric power (`s = 0`).
- `PitmanYor` — the two-parameter family `(a, b)` with `a ∈ [0, 1]`
  and `b ≥ -a`.
- `PitmanYor.partitionProb` — closed-form probability of a partition
  of `n` customers into tables of given sizes, @cite{odonnell-2015}
  eq 3.14.

## References

- @cite{odonnell-2015} §3.1.6, eq 3.12–3.14.
-/

namespace ProbabilityTheory

/--
Iterated step product `[x]_{m, s} := ∏_{k=0}^{m-1} (x + k · s)` from
@cite{odonnell-2015} eq 3.13. Generalizes the rising factorial:

- `stepPochhammer x 0 m = x^m` (constant step → power)
- `stepPochhammer x 1 m = x · (x+1) · … · (x+m-1)` (standard
  Pochhammer / rising factorial)
- `stepPochhammer x s 0 = 1` (empty product)

Used by `PitmanYor.partitionProb` with both step `s = 1` (block-size
factors) and step `s = a` (table-creation factor).
-/
noncomputable def stepPochhammer (x s : ℝ) (m : ℕ) : ℝ :=
  ∏ k : Fin m, (x + k.val * s)

/-- The empty step-product equals `1`. -/
@[simp]
theorem stepPochhammer_zero (x s : ℝ) : stepPochhammer x s 0 = 1 := by
  simp [stepPochhammer]

/--
A Pitman–Yor process @cite{odonnell-2015} §3.1.6 with discount
`a ∈ [0, 1]` and concentration `b ≥ -a`.

Sequentially: the first customer sits at table 1; the `(N+1)`-th
customer sits at occupied table `i` (current size `y_i`) with
probability `(y_i - a) / (N + b)`, or at a new table with
probability `(K · a + b) / (N + b)`, where `K` is the current number
of occupied tables. Higher discount `a` favors new tables.

Special cases:

- `discount = 0`: single-parameter Chinese Restaurant Process
  (the Dirichlet process).
- `discount = 1`: every customer sits at their own table.
-/
@[ext]
structure PitmanYor where
  /-- Discount parameter `a ∈ [0, 1]`. Higher values favor new tables. -/
  discount : ℝ
  /-- Concentration parameter `b ≥ -a`. -/
  concentration : ℝ
  /-- `0 ≤ discount`. -/
  discount_nonneg : 0 ≤ discount
  /-- `discount ≤ 1`. -/
  discount_le_one : discount ≤ 1
  /-- `-discount ≤ concentration`. -/
  concentration_ge : -discount ≤ concentration

namespace PitmanYor

variable (p : PitmanYor)

/--
Closed-form probability of a partition of `n` customers into tables
of sizes given by `q.parts`, under the Pitman–Yor process `p`. From
@cite{odonnell-2015} eq 3.14:

```
P(y | a, b) = [b + a]_{K-1, a} / [b + 1]_{N-1, 1}
              · ∏_{i=1}^{K} [1 - a]_{y_i - 1, 1}
```

where `K = q.parts.card` is the number of tables, `N = n` is the
total number of customers, and `y_1, …, y_K` are the table sizes.

The closed form depends only on the multiset of table sizes, not on
the order in which customers were seated. This **exchangeability** is
what makes adaptor grammars and fragment grammars (which marginalize
over seating orders) well-defined.
-/
noncomputable def partitionProb {n : ℕ} (q : Nat.Partition n) : ℝ :=
  stepPochhammer (p.concentration + p.discount) p.discount (q.parts.card - 1) /
    stepPochhammer (p.concentration + 1) 1 (n - 1) *
    (q.parts.map (fun y => stepPochhammer (1 - p.discount) 1 (y - 1))).prod

end PitmanYor

end ProbabilityTheory
