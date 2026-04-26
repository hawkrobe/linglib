import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
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

/-- Replace one occurrence of `m` (a block of size `m`) with `m + 1`,
    yielding a partition of `n + 1`. The combinatorial counterpart of
    "the next customer joins an existing table of size `m`" in the
    PYP seating plan (@cite{pitman-2006} §3.2). -/
def replaceMem {n : ℕ} (q : Nat.Partition n) (m : ℕ) (hm : m ∈ q.parts) :
    Nat.Partition (n + 1) where
  parts := (q.parts.erase m).cons (m + 1)
  parts_pos := by
    intro i hi
    rw [Multiset.mem_cons] at hi
    rcases hi with rfl | h
    · exact Nat.succ_pos m
    · exact q.parts_pos (Multiset.mem_of_mem_erase h)
  parts_sum := by
    have h := Multiset.sum_erase hm
    have h2 := q.parts_sum
    rw [Multiset.sum_cons]; omega

@[simp] theorem replaceMem_parts {n : ℕ} (q : Nat.Partition n) (m : ℕ) (hm : m ∈ q.parts) :
    (q.replaceMem m hm).parts = (q.parts.erase m).cons (m + 1) := rfl

@[simp] theorem replaceMem_card {n : ℕ} (q : Nat.Partition n) (m : ℕ) (hm : m ∈ q.parts) :
    (q.replaceMem m hm).parts.card = q.parts.card := by
  rw [replaceMem_parts, Multiset.card_cons, Multiset.card_erase_of_mem hm,
      Nat.pred_eq_sub_one]
  have hpos : 0 < q.parts.card := Multiset.card_pos_iff_exists_mem.mpr ⟨m, hm⟩
  omega

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

namespace OrderedFinpartition

/--
Convert an ordered set partition of `Fin n` (mathlib's `OrderedFinpartition n`,
parts ordered by greatest element) to its block-size multiset
(`Nat.Partition n`). This is the projection that drops the part-ordering
data and keeps only the multiset of block cardinalities.

Used by `PitmanYor.partitionProb` evaluation: the EPPF formula depends
only on block sizes, so the OrderedFinpartition's specific ordering is
irrelevant — but the structure gives us mathlib's `extendEquiv` which
matches Pitman's seating-plan recursion exactly.
-/
def toNatPartition {n : ℕ} (c : OrderedFinpartition n) : Nat.Partition n where
  parts := (Finset.univ : Finset (Fin c.length)).val.map c.partSize
  parts_pos := by
    intro i hi
    rw [Multiset.mem_map] at hi
    obtain ⟨k, _, rfl⟩ := hi
    exact c.partSize_pos k
  parts_sum := by
    have h1 : Fintype.card ((i : Fin c.length) × Fin (c.partSize i))
              = Fintype.card (Fin n) :=
      Fintype.card_congr c.equivSigma
    rw [Fintype.card_fin, Fintype.card_sigma] at h1
    show (∑ i : Fin c.length, c.partSize i) = n
    convert h1 using 1
    simp [Fintype.card_fin]

@[simp] theorem toNatPartition_parts {n : ℕ} (c : OrderedFinpartition n) :
    c.toNatPartition.parts = (Finset.univ : Finset (Fin c.length)).val.map c.partSize := rfl

theorem partSize_mem_toNatPartition {n : ℕ} (c : OrderedFinpartition n) (k : Fin c.length) :
    c.partSize k ∈ c.toNatPartition.parts := by
  rw [toNatPartition_parts]
  exact Multiset.mem_map.mpr ⟨k, Finset.mem_univ_val k, rfl⟩

/-- Mathlib's `OrderedFinpartition.extendLeft` (= "add new singleton block")
    corresponds to `Nat.Partition.consOne` at the multiset level. -/
theorem extendLeft_toNatPartition {n : ℕ} (c : OrderedFinpartition n) :
    c.extendLeft.toNatPartition = c.toNatPartition.consOne := by
  apply Nat.Partition.ext
  show (Finset.univ : Finset (Fin (c.length + 1))).val.map (Fin.cons 1 c.partSize) =
       (1 : ℕ) ::ₘ (Finset.univ : Finset (Fin c.length)).val.map c.partSize
  rw [Fin.univ_succ]
  simp [Multiset.map_cons, Function.comp_def, Fin.cons_succ]

/-- Mathlib's `OrderedFinpartition.extendMiddle k` (= "extend block k by 1
    element") corresponds to `Nat.Partition.replaceMem (partSize k)` at the
    multiset level. -/
theorem extendMiddle_toNatPartition {n : ℕ} (c : OrderedFinpartition n)
    (k : Fin c.length) :
    (c.extendMiddle k).toNatPartition =
      c.toNatPartition.replaceMem (c.partSize k) (c.partSize_mem_toNatPartition k) := by
  apply Nat.Partition.ext
  show (Finset.univ : Finset (Fin c.length)).val.map
        (Function.update c.partSize k (c.partSize k + 1)) =
       (((Finset.univ : Finset (Fin c.length)).val.map c.partSize).erase
        (c.partSize k)).cons (c.partSize k + 1)
  have hk_mem : k ∈ (Finset.univ : Finset (Fin c.length)).val := Finset.mem_univ_val k
  have h_erase_map : (Finset.univ.val.erase k).map
        (Function.update c.partSize k (c.partSize k + 1))
      = (Finset.univ.val.erase k).map c.partSize := by
    apply Multiset.map_congr rfl
    intro i hi
    apply Function.update_of_ne
    rintro rfl
    exact (Finset.univ : Finset (Fin c.length)).nodup.notMem_erase hi
  conv_lhs => rw [show (Finset.univ : Finset (Fin c.length)).val =
                    k ::ₘ (Finset.univ : Finset (Fin c.length)).val.erase k from
                  (Multiset.cons_erase hk_mem).symm]
  rw [Multiset.map_cons, Function.update_self, h_erase_map,
      Multiset.map_erase_of_mem c.partSize _ hk_mem]

end OrderedFinpartition

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
§3.1.6 with discount `α ∈ [0, 1]` and concentration `θ > -α`
(@cite{pitman-2006} eq 3.5, second case; the first case `α = -κ < 0,
θ = mκ` for integer `m` is excluded — irrelevant for the linguistic
application here).

Sequential interpretation (@cite{pitman-2006} §3.2 `(α, θ)` seating
plan): the first customer sits at table 1; the `(N + 1)`-th customer
sits at occupied table `i` (current size `n_i`) with probability
`(n_i - α) / (N + θ)`, or at a new table with probability
`(K · α + θ) / (N + θ)`, where `K` is the current number of occupied
tables. Higher discount `α` favours new tables.

The constraint `θ > -α` is **strict** (matching @cite{pitman-2006}
eq 3.5). The boundary `θ = -α` is degenerate: the closed-form formula
has `0/0` ratios that Lean's `x/0 = 0` convention resolves to `0`,
giving `partitionProb = 0` for partitions with `K ≥ 2` blocks but
mathematically should give the all-elements-together-or-singleton
limit. Since this boundary is a separate (degenerate) distribution
not a regular PYP, we exclude it here.

Boundary cases (well-defined under the strict constraint):

* `discount = 0`: reduces to the one-parameter Chinese Restaurant
  Process (Dirichlet process with parameter `θ > 0`).
* `discount = 1`: every customer sits at a new table; `partitionProb`
  is `0` on any partition with a non-singleton block (formula has
  `1 - α = 0` factor) and equals 1 on the all-singletons partition.
-/
@[ext]
structure PitmanYor where
  /-- Discount parameter `α ∈ [0, 1]`. Higher values favour new tables. -/
  discount : ℝ
  /-- Concentration parameter `θ > -α` (strict, per @cite{pitman-2006} eq 3.5). -/
  concentration : ℝ
  /-- `0 ≤ discount`. -/
  discount_nonneg : 0 ≤ discount
  /-- `discount ≤ 1`. -/
  discount_le_one : discount ≤ 1
  /-- `-discount < concentration`. -/
  concentration_gt : -discount < concentration

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
    -- The leading factor (m + 1 + θ) is positive: with the strict constraint
    -- θ > -α ≥ -1 and m + 1 ≥ 1, we have m + 1 + θ > 0.
    have hθ_pos : (0 : ℝ) < (m : ℝ) + 1 + p.concentration := by
      have h_pyp_strict : -p.discount < p.concentration := p.concentration_gt
      have h_pyp_le_one : p.discount ≤ 1 := p.discount_le_one
      have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
      linarith
    have hθ_ne : (1 : ℝ) + (m : ℝ) + p.concentration ≠ 0 := by linarith
    -- Case-split on the inner stepPochhammer denominator only.
    by_cases hD : stepPochhammer (p.concentration + 1) 1 m = 0
    · -- D = 0: both partitionProb values vanish via x/0 = 0 convention.
      simp [hD]
    · have h1 : (p.concentration + 1 + (m : ℝ)) ≠ 0 := by
        intro h; apply hθ_ne; linarith
      field_simp [hD, h1]
      ring

/-- **Cross-multiplied form of the seating-plan transition** for joining
    an existing block of size `m` (@cite{pitman-2006} §3.2 (α, θ) seating
    plan, "join occupied table" branch). The seating-plan probability of
    the (n+1)-th customer joining an existing table of size `m` is
    `(m - α) / (n + θ)`; this is the multiplicative counterpart.

    Equivalent (modulo dividing by `(n + θ)`) to:
    `partitionProb (q.replaceMem m hm) = partitionProb q · (m - α) / (n + θ)`. -/
theorem partitionProb_replaceMem_mul {n : ℕ} (q : Nat.Partition n) (m : ℕ)
    (hm : m ∈ q.parts) :
    ((n : ℝ) + p.concentration) * p.partitionProb (q.replaceMem m hm) =
      ((m : ℝ) - p.discount) * p.partitionProb q := by
  have hm_pos : 0 < m := q.parts_pos hm
  have hn_pos : 0 < n := by
    have hle : m ≤ n := q.le_of_mem_parts hm
    omega
  -- Strict θ > -α ≥ -1 ⇒ n + θ > 0 for n ≥ 1.
  have hθ_pos : (0 : ℝ) < (n : ℝ) + p.concentration := by
    have h1 : -p.discount < p.concentration := p.concentration_gt
    have h2 : p.discount ≤ 1 := p.discount_le_one
    have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
    linarith
  obtain ⟨m_n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_pos.ne'
  obtain ⟨m_block, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm_pos.ne'
  simp only [partitionProb, Nat.Partition.replaceMem_parts, Nat.Partition.replaceMem_card,
             Nat.add_sub_cancel, Nat.succ_eq_add_one]
  rw [Multiset.map_cons, Multiset.prod_cons]
  -- Extract the m-th block factor on the RHS via cons_erase.
  conv_rhs =>
    rw [show q.parts = (q.parts.erase (m_block + 1)).cons (m_block + 1) from
        (Multiset.cons_erase hm).symm]
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
  rw [Multiset.card_cons]
  simp only [Nat.add_sub_cancel]
  -- Apply succ to expose the (m - α) and (m_n + 1 + θ) ratio factors.
  rw [stepPochhammer_succ (1 - p.discount) 1 m_block,
      stepPochhammer_succ (p.concentration + 1) 1 m_n]
  by_cases hD : stepPochhammer (p.concentration + 1) 1 m_n = 0
  · simp [hD]
  · push_cast
    rw [mul_one]
    have h_denom : (1 : ℝ) + (m_n : ℝ) + p.concentration ≠ 0 := by
      have := hθ_pos; push_cast at this; linarith
    have h1 : (p.concentration + 1 + (m_n : ℝ)) ≠ 0 := by
      intro h; apply h_denom; linarith
    field_simp [hD, h1]
    ring

/-- Helper: sum of `OrderedFinpartition.partSize` over all part-indices
    equals `n`. Follows from the cardinality of the bijection
    `Σ k, Fin (partSize k) ≃ Fin n`. -/
theorem _root_.OrderedFinpartition.sum_partSize_eq {n : ℕ} (c : OrderedFinpartition n) :
    (∑ k : Fin c.length, c.partSize k) = n := by
  have h1 : Fintype.card ((i : Fin c.length) × Fin (c.partSize i))
            = Fintype.card (Fin n) :=
    Fintype.card_congr c.equivSigma
  rw [Fintype.card_fin, Fintype.card_sigma] at h1
  convert h1 using 1
  simp [Fintype.card_fin]

/-- **The Pitman-Yor seating-plan addition rule** (@cite{pitman-2006} eq 2.9
    for the (α, θ) EPPF). Summing the partition probabilities over all
    "ways to seat the (n+1)-th customer" recovers the partition probability
    of the predecessor. Proved via Lemmas A (`partitionProb_consOne_mul`)
    and B (`partitionProb_replaceMem_mul`) plus the arithmetic identity
    `(K · α + θ) + ∑_k (partSize k - α) = n + θ`. -/
theorem partitionProb_extend_sum (n : ℕ) (c : OrderedFinpartition n) :
    p.partitionProb c.extendLeft.toNatPartition +
        ∑ k : Fin c.length, p.partitionProb (c.extendMiddle k).toNatPartition =
      p.partitionProb c.toNatPartition := by
  match n, c with
  | 0, c =>
    rw [Subsingleton.elim c (default : OrderedFinpartition 0)]
    show p.partitionProb _ + ∑ _k, _ =
        p.partitionProb (default : OrderedFinpartition 0).toNatPartition
    simp [OrderedFinpartition.extendLeft_toNatPartition, partitionProb,
          Subsingleton.elim (default : OrderedFinpartition 0).toNatPartition
            (default : Nat.Partition 0),
          default, Nat.Partition.indiscrete, Nat.Partition.consOne]
  | n + 1, c =>
    have hθ_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) + p.concentration := by
      have h1 : -p.discount < p.concentration := p.concentration_gt
      have h2 : p.discount ≤ 1 := p.discount_le_one
      push_cast; linarith
    apply mul_left_cancel₀ hθ_pos.ne'
    rw [mul_add, OrderedFinpartition.extendLeft_toNatPartition,
        partitionProb_consOne_mul]
    have hcard : c.toNatPartition.parts.card = c.length := by
      show (Multiset.map c.partSize (Finset.univ : Finset (Fin c.length)).val).card
            = c.length
      simp [Multiset.card_map, Finset.card_univ, Fintype.card_fin]
    rw [hcard, Finset.mul_sum]
    conv_lhs =>
      enter [2, 2, k]
      rw [OrderedFinpartition.extendMiddle_toNatPartition c k,
          partitionProb_replaceMem_mul]
    rw [← Finset.sum_mul, ← add_mul]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have hsum : (∑ k : Fin c.length, ((c.partSize k : ℕ) : ℝ)) = ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast OrderedFinpartition.sum_partSize_eq c
    push_cast at hsum ⊢
    linarith

/--
**Pitman 2006 Theorem 3.2.** The EPPF is a probability mass function
on the set of set partitions of `[n]`, expressed via mathlib's
`OrderedFinpartition n` (canonical labeling by greatest element):

```
∑_{c : OrderedFinpartition n} partitionProb c.toNatPartition = 1
```

The proof is by induction on `n` using mathlib's
`OrderedFinpartition.extendEquiv` — the bijection
`(c : OrderedFinpartition n) × Option (Fin c.length) ≃
  OrderedFinpartition (n + 1)` — to decompose the sum.
The inductive step is `partitionProb_extend_sum`, which combines
Lemma A (`partitionProb_consOne_mul`) and Lemma B
(`partitionProb_replaceMem_mul`) with the arithmetic identity
`(K · α + θ) + ∑_k (partSize k - α) = n + θ`.

`OrderedFinpartition` carries a specific canonical ordering of parts
(by greatest element), but `partitionProb` depends only on the
block-size multiset, so this is the right sample space: each set
partition of `[n]` corresponds to exactly one `OrderedFinpartition n`.
-/
theorem sum_partitionProb_ord_eq_one (n : ℕ) :
    ∑ c : OrderedFinpartition n, p.partitionProb c.toNatPartition = 1 := by
  induction n with
  | zero =>
    rw [Fintype.sum_unique]
    show p.partitionProb (default : OrderedFinpartition 0).toNatPartition = 1
    rw [Subsingleton.elim (default : OrderedFinpartition 0).toNatPartition
        (default : Nat.Partition 0)]
    simp [partitionProb, default, Nat.Partition.indiscrete]
  | succ n ih =>
    rw [← Equiv.sum_comp (OrderedFinpartition.extendEquiv n), Fintype.sum_sigma]
    have h_inner : ∀ c : OrderedFinpartition n,
        ∑ opt : Option (Fin c.length),
          p.partitionProb ((OrderedFinpartition.extendEquiv n) ⟨c, opt⟩).toNatPartition =
          p.partitionProb c.toNatPartition := by
      intro c
      rw [Fintype.sum_option]
      simp only [OrderedFinpartition.extendEquiv, Equiv.coe_fn_mk,
                 OrderedFinpartition.extend]
      exact partitionProb_extend_sum p n c
    rw [Finset.sum_congr rfl (fun c _ => h_inner c)]
    exact ih

end PitmanYor

end ProbabilityTheory
