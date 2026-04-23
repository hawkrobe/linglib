import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

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

/-- A step-product is nonnegative when every factor is nonnegative.
    General-purpose lemma; PYP-specific factor-positivity is derived
    in `PitmanYor.partitionProb_nonneg`. -/
theorem stepPochhammer_nonneg (x s : ℝ) (m : ℕ)
    (h : ∀ k : Fin m, 0 ≤ x + (k.val : ℝ) * s) :
    0 ≤ stepPochhammer x s m := by
  unfold stepPochhammer
  exact Finset.prod_nonneg fun i _ => h i

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

/--
Pitman–Yor partition probabilities are nonnegative. Under the PYP
constraints (`0 ≤ a ≤ 1`, `b ≥ -a`), each `stepPochhammer` factor in
the closed form is nonnegative — both the table-creation factor
`[b+a]_{K-1, a}`, the customer-seating factor `[b+1]_{N-1, 1}`, and
each per-table block-size factor `[1-a]_{y_i-1, 1}` — and the
overall quotient × product preserves nonnegativity via mathlib's
`div_nonneg` / `mul_nonneg`. Used downstream by
`AdaptorGrammar.corpusProbGivenTables_nonneg`.
-/
theorem partitionProb_nonneg {n : ℕ} (q : Nat.Partition n) :
    0 ≤ p.partitionProb q := by
  have h_a_nn : 0 ≤ p.discount := p.discount_nonneg
  have h_a_le_1 : p.discount ≤ 1 := p.discount_le_one
  have h_b_ge : -p.discount ≤ p.concentration := p.concentration_ge
  have h_b_plus_a : 0 ≤ p.concentration + p.discount := by linarith
  have h_b_plus_1 : 0 ≤ p.concentration + 1 := by linarith
  have h_one_minus_a : 0 ≤ 1 - p.discount := by linarith
  -- Numerator: stepPochhammer (b+a) a (K-1) ≥ 0
  have h_num : 0 ≤ stepPochhammer (p.concentration + p.discount) p.discount
      (q.parts.card - 1) := by
    apply stepPochhammer_nonneg
    intro k
    have h_ka_nn : 0 ≤ (k.val : ℝ) * p.discount :=
      mul_nonneg (Nat.cast_nonneg _) h_a_nn
    linarith
  -- Denominator: stepPochhammer (b+1) 1 (n-1) ≥ 0
  have h_den : 0 ≤ stepPochhammer (p.concentration + 1) 1 (n - 1) := by
    apply stepPochhammer_nonneg
    intro k
    have h_k_nn : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
    nlinarith
  -- Per-table factor: stepPochhammer (1-a) 1 (y-1) ≥ 0 for each y
  have h_part : ∀ y ∈ q.parts, 0 ≤ stepPochhammer (1 - p.discount) 1 (y - 1) := by
    intro y _
    apply stepPochhammer_nonneg
    intro k
    have h_k_nn : (0 : ℝ) ≤ (k.val : ℝ) := Nat.cast_nonneg _
    nlinarith
  -- Multiset product of nonnegs is nonneg
  have h_prod : 0 ≤ (q.parts.map (fun y =>
      stepPochhammer (1 - p.discount) 1 (y - 1))).prod :=
    Multiset.prod_map_nonneg fun y hy => h_part y hy
  unfold partitionProb
  exact mul_nonneg (div_nonneg h_num h_den) h_prod

end PitmanYor

end ProbabilityTheory
