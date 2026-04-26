import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Pitman–Yor process

@cite{pitman-2006} @cite{odonnell-2015}

The Pitman–Yor process (PYP) is a two-parameter Bayesian non-parametric
distribution on partitions of `[n]`, generalising the Chinese Restaurant
Process (the one-parameter Dirichlet process). The mathematical reference
is @cite{pitman-2006} §3.2 (Saint-Flour lectures); the linguistic
application that motivates this file is @cite{odonnell-2015} §3.1.6
(memoization distribution for adaptor and fragment grammars in
`Theories/Morphology/FragmentGrammars/`).

## Naming convention

@cite{pitman-2006} writes parameters as `(α, θ)` with `α` = discount and
`θ` = concentration; @cite{odonnell-2015} writes `(a, b)` for the same
two. We use `(discount, concentration)` to match neither convention's
single letters but to be self-documenting.

## Main definitions

* `stepPochhammer x s m` — generalised step product
  `∏_{k=0}^{m-1} (x + k·s)` (@cite{pitman-2006} eq 3.7,
  @cite{odonnell-2015} eq 3.13). Specialises to the rising factorial
  `(ascPochhammer R m).eval x` at `s = 1` and to the geometric power
  `x^m` at `s = 0`.
* `PitmanYor` — the two-parameter family `(discount, concentration)`
  with `0 ≤ discount ≤ 1` and `concentration ≥ -discount`
  (@cite{pitman-2006} eq 3.5, second case).
* `PitmanYor.partitionProb` — the *exchangeable partition probability
  function* (EPPF) of @cite{pitman-2006} Theorem 3.2 (eq 3.6) /
  @cite{odonnell-2015} eq 3.14.

## What `partitionProb` actually computes

`partitionProb q` evaluates Pitman's EPPF formula
(@cite{pitman-2006} eq 3.6) at the multiset of block sizes `q.parts`.
The EPPF is, per @cite{pitman-2006} p. 39, the probability that the
random partition `Π_n` equals **any specific (set) partition of `[n]`**
whose blocks have sizes `(n_1, …, n_k)`. By the EPPF's symmetry, the
value depends only on the multiset of sizes — which is what makes the
`Nat.Partition n → ℝ` signature well-typed.

**`partitionProb q` is therefore the prob of one specific set partition
with multiset of block sizes `q.parts`, NOT the prob of the multiset
`q.parts` itself.** The two differ by the multiplicity factor

```
mult(q) = n! / (∏_{m ∈ q.parts} m! · ∏_{j} (q.parts.count j)!)
```

i.e. the number of set partitions of `[n]` whose block sizes are
`q.parts` (@cite{pitman-2006} eq 2.2 / `Nat.Partition.numSetPartitions`).

## Sum-to-1 identities

Pitman 2006 gives several equivalent normalisations of the EPPF:

```
(a) ∑_{Π : set partition of [n]} EPPF(block sizes of Π) = 1
                                                          @cite{pitman-2006} Thm 3.2
(b) ∑_{q : Nat.Partition n} mult(q) · partitionProb q = 1
                                                          @cite{pitman-2006} eq 2.2
(c) ∑_{compositions (n_1,…,n_k) of n} (n choose n_1,…,n_k)·1/k! · EPPF(n_1,…,n_k) = 1
                                                          @cite{pitman-2006} p. 42
```

We formalise (a) as `sum_partitionProb_set_eq_one`, summing over
`Finpartition (Finset.univ : Finset (Fin n))`. This is the form the
downstream `AdaptorGrammar` consumer needs (since AG's `Y` is a labeled
table assignment, equivalent to a set partition under the canonical
"tables labeled by order of creation" convention).

The **bare** sum `∑_{q : Nat.Partition n} partitionProb q` does NOT
equal 1 in general — every multiset appears once in the sum, but the
EPPF interpretation requires counting it `mult(q)` times. For example,
at `α = 0, θ = 1, n = 3` the bare sum is `2/3`.

## Limitations

* `partitionProb` returns `ℝ` rather than `PMF`. The downstream
  consumer `AdaptorGrammar.corpusProbGivenTables` is itself an
  ℝ-valued kernel (table assignments are latent, not marginalised),
  so the bare-ℝ form is what the consumer wants.
* The normalisation theorem `sum_partitionProb_set_eq_one`
  (@cite{pitman-2006} Thm 3.2) is stated as `sorry` below. The
  construction-style proof (build the EPPF as the marginal of the
  consistent Chinese Restaurant seating plan @cite{pitman-2006} §3.2)
  needs Markov-kernel infrastructure linglib does not yet have; the
  closed-form proof needs Vandermonde-style identities not yet in
  mathlib. Recorded as `sorry` per CLAUDE.md "prefer sorry over
  weakening."
* Reduction theorems (`discount = 0` ⇒ Chinese Restaurant Process /
  Dirichlet process @cite{pitman-2006} §3.2 case `(α=0, θ>0)`,
  `discount = 1` ⇒ all-singletons partition) require a CRP file
  (linglib has none) and are deferred.
-/

namespace Nat.Partition

/--
The number of distinct set partitions of `Fin n` whose multiset of
block cardinalities equals `q.parts`. By the standard combinatorial
formula (@cite{pitman-2006} eq 2.3 in implicit form):

```
mult(q) = n! / (∏_{m ∈ q.parts} m! · ∏_{j ∈ q.parts.toFinset} (q.parts.count j)!)
```

For example, `mult({1, 2}) = 3` (counts `{{1},{2,3}}`, `{{2},{1,3}}`,
`{{3},{1,2}}`); `mult({1, 1, 1}) = 1`; `mult({3}) = 1`.

The natural-number division is exact (the denominator divides `n!`
because both quantities count the same set of objects from different
angles).
-/
def numSetPartitions {n : ℕ} (q : Nat.Partition n) : ℕ :=
  n.factorial /
    (q.parts.map Nat.factorial).prod /
    ∏ j ∈ q.parts.toFinset, (q.parts.count j).factorial

/-- Extend a partition of `n` by a new singleton block of size 1,
    yielding a partition of `n + 1`. The combinatorial counterpart of
    "the next customer sits at a new (singleton) table" in the PYP
    seating plan (@cite{pitman-2006} §3.2). -/
def consOne {n : ℕ} (q : Nat.Partition n) : Nat.Partition (n + 1) where
  parts := q.parts.cons 1
  parts_pos := by
    intro i hi
    rw [Multiset.mem_cons] at hi
    rcases hi with rfl | h
    · exact Nat.one_pos
    · exact q.parts_pos h
  parts_sum := by
    rw [Multiset.sum_cons, q.parts_sum, Nat.add_comm]

@[simp] theorem consOne_parts {n : ℕ} (q : Nat.Partition n) :
    q.consOne.parts = q.parts.cons 1 := rfl

@[simp] theorem consOne_card {n : ℕ} (q : Nat.Partition n) :
    q.consOne.parts.card = q.parts.card + 1 := by
  simp [consOne_parts]

end Nat.Partition

namespace Finpartition

/--
Convert a set partition of `Fin n` (i.e., a `Finpartition` of
`Finset.univ : Finset (Fin n)`) to its block-size multiset
(`Nat.Partition n`). This is the projection that loses the set-partition
structure (which elements are in which block) and keeps only the
cardinalities.

Used by `AdaptorGrammar.pypFactor` to evaluate Pitman's EPPF
(`PitmanYor.partitionProb`) on a labeled table assignment, since the
EPPF formula depends only on block sizes.
-/
def toNatPartition {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) : Nat.Partition n where
  parts := P.parts.val.map Finset.card
  parts_pos := by
    intro i hi
    rw [Multiset.mem_map] at hi
    obtain ⟨B, hB, rfl⟩ := hi
    rw [Finset.card_pos]
    exact P.nonempty_of_mem_parts hB
  parts_sum := by
    rw [show (P.parts.val.map Finset.card).sum = ∑ B ∈ P.parts, B.card from rfl,
        P.sum_card_parts, Finset.card_univ, Fintype.card_fin]

end Finpartition

namespace ProbabilityTheory

/--
The *step Pochhammer* product
`[x]_{m, s} := ∏_{k=0}^{m-1} (x + k · s)` of @cite{pitman-2006} eq 3.7
(written there as `(x)_{m↑s}`) and @cite{odonnell-2015} eq 3.13.

Generalises the standard rising factorial in the step `s`:

* `stepPochhammer x 0 m = x ^ m` (geometric power; see
  `stepPochhammer_zero_step`).
* `stepPochhammer x 1 m = (ascPochhammer R m).eval x` (rising factorial;
  see `stepPochhammer_one_eq_ascPochhammer_eval` for the bridge to
  `Mathlib.RingTheory.Polynomial.Pochhammer`).
* `stepPochhammer x s 0 = 1` (empty product; see `stepPochhammer_zero`).

Used by `PitmanYor.partitionProb` with two values of the step:
`s = 1` (block-size factors) and `s = discount` (table-creation factor).
The latter — step-`discount` — is the defining generalisation of the
Pitman–Yor process over the one-parameter Dirichlet process / Chinese
Restaurant Process.
-/
def stepPochhammer {R : Type*} [CommSemiring R] (x s : R) (m : ℕ) : R :=
  ∏ k : Fin m, (x + k.val * s)

variable {R : Type*}

@[simp]
theorem stepPochhammer_zero [CommSemiring R] (x s : R) :
    stepPochhammer x s 0 = 1 := by
  simp [stepPochhammer]

theorem stepPochhammer_succ [CommSemiring R] (x s : R) (m : ℕ) :
    stepPochhammer x s (m + 1) = stepPochhammer x s m * (x + m * s) := by
  simp [stepPochhammer, Fin.prod_univ_castSucc]

/-- The step-`1` case is mathlib's rising factorial. Bridges the
    PYP file's notation to `Mathlib.RingTheory.Polynomial.Pochhammer`,
    so users grepping for `Pochhammer` find both names. -/
theorem stepPochhammer_one_eq_ascPochhammer_eval [CommSemiring R]
    (x : R) (m : ℕ) :
    stepPochhammer x 1 m = (ascPochhammer R m).eval x := by
  induction m with
  | zero => simp
  | succ n ih => rw [stepPochhammer_succ, ih, ascPochhammer_succ_eval, mul_one]

/-- The step-`0` case collapses to a power: `[x]_{m, 0} = x^m`. -/
theorem stepPochhammer_zero_step [CommSemiring R] (x : R) (m : ℕ) :
    stepPochhammer x 0 m = x ^ m := by
  simp [stepPochhammer, mul_zero, add_zero]

/-- Step product is nonnegative when every factor is nonnegative.
    General-purpose; the PYP-specific factor positivity lives in
    `PitmanYor.partitionProb_nonneg`. -/
theorem stepPochhammer_nonneg [CommSemiring R] [PartialOrder R]
    [IsOrderedRing R] (x s : R) (m : ℕ)
    (h : ∀ k : Fin m, 0 ≤ x + (k.val : R) * s) :
    0 ≤ stepPochhammer x s m :=
  Finset.prod_nonneg fun i _ => h i

/--
A *Pitman–Yor process* @cite{pitman-2006} §3.2 / @cite{odonnell-2015}
§3.1.6 with discount `α ∈ [0, 1]` and concentration `θ ≥ -α`
(@cite{pitman-2006} eq 3.5, second case; the first case `α = -κ < 0,
θ = mκ` for integer `m` is excluded — irrelevant for the linguistic
application here).

Sequential interpretation (@cite{pitman-2006} §3.2 `(α, θ)` seating
plan): the first customer sits at table 1; the `(N + 1)`-th customer
sits at occupied table `i` (current size `n_i`) with probability
`(n_i - α) / (N + θ)`, or at a new table with probability
`(K · α + θ) / (N + θ)`, where `K` is the current number of occupied
tables. Higher discount `α` favours new tables.

Boundary cases (degenerate but well-defined by the closed-form formula):

* `discount = 0`: reduces to the one-parameter Chinese Restaurant
  Process (Dirichlet process with parameter `θ`).
* `discount = 1`: every customer sits at a new table; `partitionProb`
  is `0` on any partition with a non-singleton block and `1` on the
  all-singletons partition.
* `concentration = -discount`: degenerate; `partitionProb` is `0` on
  any partition with `K ≥ 2` blocks.
-/
@[ext]
structure PitmanYor where
  /-- Discount parameter `α ∈ [0, 1]`. Higher values favour new tables. -/
  discount : ℝ
  /-- Concentration parameter `θ ≥ -α`. -/
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
The Pitman–Yor *exchangeable partition probability function* (EPPF)
of @cite{pitman-2006} Theorem 3.2 (eq 3.6) / @cite{odonnell-2015}
eq 3.14, evaluated at the multiset of block sizes `q.parts`:

```
EPPF(n_1, ..., n_K | α, θ) = [θ + α]_{K-1, α} · ∏_{i=1}^K [1 - α]_{n_i - 1, 1}
                             / [θ + 1]_{N - 1, 1}
```

where `K = q.parts.card` is the number of blocks and `N = n` is the
total number of elements.

**Semantics**: by @cite{pitman-2006} p. 39, this is the probability
that the random partition `Π_n` equals **any specific (set) partition
of `[n]`** with the given multiset of block sizes — NOT the
probability of the multiset itself. The two differ by the multiplicity
factor `n! / (∏ m_i! · ∏ count_j!)`. See the module docstring for the
three equivalent normalisation identities (Pitman 3.2 / 2.2 / p. 42).

The EPPF is symmetric in `(n_1, …, n_k)`, so the value is well-defined
as a function of the multiset `q.parts`. This is what makes the
`Nat.Partition n → ℝ` signature well-typed; it does not make
`partitionProb` a probability distribution on `Nat.Partition n` (it
isn't — see module docstring).

The `n - 1` and `q.parts.card - 1` terms use ℕ truncating subtraction.
This is intentional and correct on the boundary: at `n = 0` (and hence
the unique empty partition with `K = 0`), all three step factors
collapse to the empty product `1`, giving `EPPF = 1` — the vacuous
probability of the unique set partition of zero elements.
-/
noncomputable def partitionProb {n : ℕ} (q : Nat.Partition n) : ℝ :=
  stepPochhammer (p.concentration + p.discount) p.discount (q.parts.card - 1) /
    stepPochhammer (p.concentration + 1) 1 (n - 1) *
    (q.parts.map (fun y => stepPochhammer (1 - p.discount) 1 (y - 1))).prod

/-- Pitman–Yor partition probabilities are nonnegative. Each step
    factor in @cite{pitman-2006} eq 3.6 is nonnegative under the PYP
    constraints (`0 ≤ α ≤ 1`, `θ ≥ -α`), and the overall quotient and
    product preserve nonnegativity. Used downstream by
    `AdaptorGrammar.corpusProbGivenTables_nonneg`. -/
theorem partitionProb_nonneg {n : ℕ} (q : Nat.Partition n) :
    0 ≤ p.partitionProb q := by
  obtain ⟨a, b, ha_nn, ha_le, hba⟩ := p
  have h_b_plus_a : 0 ≤ b + a := by linarith
  have h_b_plus_1 : 0 ≤ b + 1 := by linarith
  have h_one_minus_a : 0 ≤ 1 - a := by linarith
  unfold partitionProb
  refine mul_nonneg (div_nonneg ?_ ?_) ?_
  · exact stepPochhammer_nonneg _ _ _ fun k => by positivity
  · exact stepPochhammer_nonneg _ _ _ fun k => by positivity
  · exact Multiset.prod_map_nonneg fun y _ =>
      stepPochhammer_nonneg _ _ _ fun k => by positivity

/-- Exchangeability is by construction: `partitionProb` reads only the
    multiset `q.parts`, never an underlying ordering. Stated for
    grep-discoverability — the proof is `rfl`. -/
theorem partitionProb_eq_of_parts_eq {n : ℕ} (q q' : Nat.Partition n)
    (h : q.parts = q'.parts) : p.partitionProb q = p.partitionProb q' := by
  unfold partitionProb; rw [h]

/-- **Cross-multiplied form of the seating-plan transition** for a new
    singleton block (@cite{pitman-2006} §3.2 (α, θ) seating plan,
    "new table" branch). The seating-plan probability of the (n+1)-th
    customer creating a new table is `(K · α + θ) / (n + θ)`, where K
    is the current number of blocks; this is the multiplicative
    counterpart, valid in all cases including `n = θ = 0`.

    Equivalent (modulo dividing both sides by `(n + θ)` when nonzero) to:
    `partitionProb q.consOne = partitionProb q · (K · α + θ) / (n + θ)`. -/
theorem partitionProb_consOne_mul {n : ℕ} (q : Nat.Partition n) :
    ((n : ℝ) + p.concentration) * p.partitionProb q.consOne =
      ((q.parts.card : ℝ) * p.discount + p.concentration) * p.partitionProb q := by
  -- Case-split on n. The match form keeps `q : Nat.Partition n` properly typed.
  match n, q with
  | 0, q =>
    -- n = 0: q is the unique empty partition, both sides reduce to θ.
    simp [partitionProb]
  | m + 1, q =>
    -- n = m + 1: q.parts is nonempty, so q.parts.card ≥ 1.
    have hK : q.parts.card ≠ 0 := by
      intro hc
      have hsum : q.parts.sum = 0 := by
        rw [Multiset.card_eq_zero.mp hc, Multiset.sum_zero]
      rw [q.parts_sum] at hsum; omega
    obtain ⟨K, hcard⟩ := Nat.exists_eq_succ_of_ne_zero hK
    -- Unfold and clear the new singleton's contribution (factor 1).
    simp only [partitionProb, Nat.Partition.consOne_parts,
               Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons,
               Nat.sub_self, stepPochhammer_zero, one_mul]
    rw [hcard]
    simp only [Nat.add_sub_cancel]
    -- Apply succ to expose (Kα + θ + α) and (m + 1 + θ) ratio factors.
    rw [stepPochhammer_succ (p.concentration + p.discount) p.discount K,
        stepPochhammer_succ (p.concentration + 1) 1 m]
    push_cast
    rw [mul_one]
    -- Two-tier case split: stepPochhammer (θ+1) 1 m may vanish; (1+m+θ) may vanish.
    by_cases hD : stepPochhammer (p.concentration + 1) 1 m = 0
    · -- D = 0: both partitionProb values vanish via x/0 = 0 convention.
      simp [hD]
    · by_cases hθ : (1 : ℝ) + (m : ℝ) + p.concentration = 0
      · -- Boundary: 1 + m + θ = 0. With PYP constraints
        -- (`-α ≤ θ`, `0 ≤ α ≤ 1`), this forces m = 0, α = 1, θ = -1, K = 0.
        -- Both LHS factor (m+1+θ) and RHS factor ((K+1)α+θ) reduce to 0.
        have h_α : p.discount = 1 := by
          have h_pyp1 : -p.discount ≤ p.concentration := p.concentration_ge
          have h_pyp2 : p.discount ≤ 1 := p.discount_le_one
          have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
          linarith
        have hm_eq : (m : ℝ) = 0 := by
          have h_pyp1 : -p.discount ≤ p.concentration := p.concentration_ge
          rw [h_α] at h_pyp1
          linarith
        have hm0 : m = 0 := by exact_mod_cast hm_eq
        have h_θ : p.concentration = -1 := by
          rw [hm0] at hθ; push_cast at hθ; linarith
        subst hm0
        have h_K_zero : K = 0 := by
          have h_card : q.parts.card = 1 := by
            rw [Nat.Partition.partition_one_parts q]; rfl
          omega
        subst h_K_zero
        rw [h_α, h_θ]
        push_cast
        ring
      · -- Generic case: both denominators nonzero, clear via field_simp + ring.
        have h1 : (p.concentration + 1 + (m : ℝ)) ≠ 0 := by
          intro h; apply hθ; linarith
        field_simp [hD, h1]
        ring

/--
**Pitman 2006 Theorem 3.2.** The EPPF is a probability mass function
on the set of set partitions of `[n]`:

```
∑_{P : Finpartition (Finset.univ : Finset (Fin n))}
    partitionProb P.toNatPartition = 1
```

This is the form the downstream `AdaptorGrammar` consumer needs (since
AG's `Y` is a labeled table assignment, equivalent to a set partition
under the canonical "tables labeled by order of creation" convention).

**Status: unproven.** Construction-style proof (@cite{pitman-2006}
§3.2 (α, θ) seating plan): build the seating plan as a consistent
sequence of kernels
```
Finpartition (Finset.univ : Finset (Fin n)) →
  PMF (Finpartition (Finset.univ : Finset (Fin (n + 1))))
```
where the kernel adds element `n` either as a new singleton block
(prob `(K·α + θ) / (n + θ)`) or to an existing block of size `m`
(prob `(m - α) / (n + θ)`). Prove by induction on `n` that the
marginal at step `n` is `partitionProb P.toNatPartition`. Conclude
sum-to-1 from `PMF.tsum_coe`. Multi-day formalisation project;
recorded as `sorry` per CLAUDE.md "prefer sorry over weakening".

The equivalent multiset form (@cite{pitman-2006} eq 2.2)
```
∑_{q : Nat.Partition n} (q.numSetPartitions : ℝ) · partitionProb q = 1
```
follows from this theorem by the bijection
`Finpartition · ≃ Σ q : Nat.Partition n, {P | P.toNatPartition = q}`,
where the fiber over `q` has cardinality `q.numSetPartitions`.
-/
theorem sum_partitionProb_set_eq_one {n : ℕ} :
    ∑ P : Finpartition (Finset.univ : Finset (Fin n)),
        p.partitionProb P.toNatPartition = 1 := by
  sorry

end PitmanYor

end ProbabilityTheory
