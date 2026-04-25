import Linglib.Core.Probability.PolyaUrn
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Dirichlet–multinomial distribution

@cite{odonnell-2015}

The count-vector PMF associated with a `PolyaUrn`. Sequentially: the
distribution of `(x_1, …, x_K)` after drawing `N` times from the
urn, where `x_i` counts how often color `i` was drawn. By
Dirichlet–Categorical conjugacy, equivalently obtained by sampling
`θ ~ Dirichlet(π)` and then `(x_1, …, x_K) ~ Multinomial(N; θ)` and
integrating out `θ`.

Closed-form mass at `x : α → ℕ` with `∑ i, x i = N`:

```
P(x | π) = (N! / ∏ x_i!) · Γ(Σ π) / Γ(Σ π + N) · ∏ Γ(π_i + x_i) / Γ(π_i)
```

The first factor is the multinomial coefficient (number of draw
sequences realizing the count vector `x`); the rest is
`PolyaUrn.seqProb x` (the per-sequence likelihood, defined in the
sibling file `PolyaUrn.lean`).

## Two-tier mathlib pattern

Mirrors `Mathlib.Probability.Distributions.Poisson.Basic`'s
`poissonPMFReal` + `poissonPMF`: a raw-`ℝ` closed form `pmfReal` and
a proper `PMF (α → ℕ)` wrapper `pmf` constructed directly from a
`HasSum` proof.

## Status

Normalization (`pmfReal_hasSum_one`) is fully discharged. The two key
combinatorial lemmas are proved by induction on `N` via `Fin.snoc`
decomposition:

1. `multinomCount_mul_prod_factorial`: the multinomial counting identity
   `#{seq | count seq = x} · ∏ x_i! = N!`. Step `N+1` partitions sequences
   by their last element via `multinomCount_snoc_fiber`.
2. `exists_seq_count_eq`: every count vector with `Σ = N` is realized by
   some sequence, by IH-induction (decrement at some `c` with `x c > 0`,
   then snoc).

Candidate to upstream to mathlib alongside a proper
`Mathlib/Probability/Distributions/Dirichlet.lean` /
`DirichletMultinomial.lean`.

## Why split from `PolyaUrn.lean`

Downstream consumers (`Theories/Morphology/FragmentGrammars/DMPCFG`,
`AdaptorGrammar`, `FragmentGrammar`) consume only
`PolyaUrn.seqProb` — a corpus IS a labeled derivation sequence, not
a draw from the unlabeled-count distribution. Bundling the PMF
machinery into `PolyaUrn.lean` would force every consumer of
`seqProb` to pay the `Probability.ProbabilityMassFunction.Basic`
import cost (~10s of olean loading via `MeasureTheory.Measure.Dirac`).
Mathlib analog: `Distributions/Poisson/Basic.lean` is distinct from
`Distributions/Poisson/Variance.lean` for the same import-discipline
reason.

## Why we avoid `PMF.ofFinset` + `Finset.piAntidiag` + `Nat.multinomial`

Each lives in a heavier mathlib file
(`ProbabilityMassFunction.Constructions`, `Algebra.Order.Antidiag.Pi`,
`Data.Nat.Choose.Multinomial`) and we don't need them: the PMF can
be built directly from a `HasSum` (mathlib's `PMF.ofFinset` is
itself just `⟨_, hasSum_sum_of_ne_finset_zero ...⟩`), the support
characterization fits as an inline `if ∑ i, x i = N then _ else 0`,
and the multinomial coefficient is just `(∑ i, x i)! / ∏ i, (x i)!`
written out. Mathlib's Poisson takes the same approach
(`⟨ENNReal.ofReal ∘ poissonPMFReal r, _⟩`).

The labeled→unlabeled `.map` to `PMF (Nat.Partition N)` is deferred
to a future file (would import `Combinatorics.Enumerative.Partition`
and `ProbabilityMassFunction.Monad` for `.map`).

## Main definitions

- `DirichletMultinomial.pmfReal` — closed-form mass at a count
  vector, as a raw `ℝ` (= multinomial coefficient · `seqProb`).
- `DirichletMultinomial.pmf` — the distribution as a proper
  `PMF (α → ℕ)`, supported on count vectors summing to `N`.
  `pmfReal_hasSum_one` discharges the HasSum chain via the multinomial
  counting identity + count-vector surjectivity (both proved in this file).
-/

namespace ProbabilityTheory

namespace DirichletMultinomial

variable {α : Type*} [Fintype α] (u : PolyaUrn α)

/-- Dirichlet–multinomial closed-form mass at a count vector, as a
raw `ℝ`. The multinomial coefficient `(∑ x_i)! / ∏ (x_i!)` counts
how many draw sequences realize the count vector `x`; multiplying
by `PolyaUrn.seqProb x` gives the count-vector mass. For `x`
summing to `N`, this equals
`(N! / ∏ x_i!) · Γ(Σ π) / Γ(Σ π + N) · ∏ Γ(π_i + x_i) / Γ(π_i)` —
the standard Dirichlet–multinomial mass. -/
noncomputable def pmfReal (x : α → ℕ) : ℝ :=
  ((∑ i, x i).factorial : ℝ) / (∏ i, (x i).factorial : ℝ) * u.seqProb x

theorem pmfReal_nonneg [Nonempty α] (x : α → ℕ) :
    0 ≤ pmfReal u x := by
  unfold pmfReal
  refine mul_nonneg (div_nonneg (Nat.cast_nonneg _) ?_) (u.seqProb_pos x).le
  exact_mod_cast (Finset.univ.prod (fun i => (x i).factorial)).zero_le

/-- Helper: the count vector function from sequences `Fin N → α`. -/
private def countVec [DecidableEq α] {N : ℕ} (seq : Fin N → α) : α → ℕ :=
  fun c => (Finset.univ.filter (seq · = c)).card

/-- The set of count vectors realized by sequences `Fin N → α`. -/
private noncomputable def countVectors [DecidableEq α] (N : ℕ) : Finset (α → ℕ) :=
  (Finset.univ : Finset (Fin N → α)).image countVec

/-- Each count vector in the image of `countVec` sums to `N`. -/
private theorem mem_countVectors [DecidableEq α] {N : ℕ} {x : α → ℕ}
    (hx : x ∈ countVectors (α := α) N) : ∑ i, x i = N := by
  obtain ⟨seq, _, rfl⟩ := Finset.mem_image.mp hx
  exact PolyaUrn.sum_counts_eq_length (α := α) seq

/-- Number of sequences `Fin N → α` mapping to a given count vector. -/
private noncomputable def multinomCount [DecidableEq α] (x : α → ℕ) (N : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin N → α)).filter (fun seq => countVec seq = x)).card

/-- Snoc-decomposition fiber: sequences with count vector `x` whose last
element is `c` are in bijection with sequences of length `N` with count
`update x c (x c - 1)`. -/
private lemma multinomCount_snoc_fiber [DecidableEq α] {N : ℕ}
    (x : α → ℕ) (c : α) (hxc : 0 < x c) :
    ((Finset.univ : Finset (Fin (N+1) → α)).filter
      (fun seq => countVec (N := N+1) seq = x ∧ seq (Fin.last N) = c)).card =
    multinomCount (α := α) (Function.update x c (x c - 1)) N := by
  -- Bijection: seq ↔ Fin.init seq via Fin.snoc with last element c.
  -- Both sides count sequences of length N with count = update x c (x c - 1).
  apply Finset.card_bij (fun (seq : Fin (N+1) → α) _ => Fin.init seq)
  · -- Maps to: init seq has the correct count vector.
    intro seq hseq
    rw [Finset.mem_filter] at hseq
    obtain ⟨_, hcount, hlast⟩ := hseq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    funext d
    show ((Finset.univ : Finset (Fin N)).filter
      (fun i => Fin.init seq i = d)).card = Function.update x c (x c - 1) d
    -- Use snoc_count_eq style identity reversed.
    -- count_{N+1} seq d = count_N (init seq) d + (if seq (last) = d then 1 else 0)
    have card_eq : ∀ (M : ℕ) (g : Fin M → α),
        ((Finset.univ : Finset (Fin M)).filter (fun i => g i = d)).card =
          ∑ i : Fin M, if g i = d then 1 else 0 := by
      intro M g
      rw [Finset.card_filter]
    have hcount_d := congrFun hcount d
    show ((Finset.univ : Finset (Fin N)).filter
      (fun i => Fin.init seq i = d)).card = Function.update x c (x c - 1) d
    rw [card_eq]
    have hnplus1 : ((Finset.univ : Finset (Fin (N+1))).filter
        (fun i => seq i = d)).card = x d := hcount_d
    rw [card_eq] at hnplus1
    rw [Fin.sum_univ_castSucc] at hnplus1
    show ∑ i : Fin N, (if Fin.init seq i = d then (1:ℕ) else 0) =
      Function.update x c (x c - 1) d
    -- Convert if (Fin.init seq i = d) to if (seq (castSucc i) = d) using Fin.init_def
    have h_init_eq : ∀ i : Fin N, (Fin.init seq i : α) = seq (Fin.castSucc i) := by
      intro i
      rfl
    have h_lhs_eq : ∑ i : Fin N, (if Fin.init seq i = d then (1:ℕ) else 0) =
        ∑ i : Fin N, (if seq (Fin.castSucc i) = d then (1:ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [h_init_eq i]
    rw [h_lhs_eq]
    by_cases hcd : d = c
    · subst hcd
      -- seq (last N) = d holds, so the if-clause adds 1.
      rw [if_pos hlast] at hnplus1
      have hxd_d : Function.update x d (x d - 1) d = x d - 1 := Function.update_self _ _ _
      rw [hxd_d]
      omega
    · -- seq (last N) = c ≠ d, so the if-clause adds 0.
      have hneq : seq (Fin.last N) ≠ d := by
        intro h
        apply hcd
        rw [← h, hlast]
      rw [if_neg hneq] at hnplus1
      have hxd_d : Function.update x c (x c - 1) d = x d := by
        rw [Function.update_of_ne hcd]
      rw [hxd_d]
      omega
  · -- Injectivity: if Fin.init seq1 = Fin.init seq2, then seq1 = seq2 (since both end in c).
    intro s1 hs1 s2 hs2 hinit
    rw [Finset.mem_filter] at hs1 hs2
    obtain ⟨_, _, hl1⟩ := hs1
    obtain ⟨_, _, hl2⟩ := hs2
    funext i
    by_cases hi : i = Fin.last N
    · subst hi
      rw [hl1, hl2]
    · have : i = (Fin.castSucc ⟨i.val, lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt)
                  (fun h => hi (Fin.eq_of_val_eq h))⟩) := by
        rfl
      rw [this]
      have := congrFun hinit ⟨i.val, lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt)
                  (fun h => hi (Fin.eq_of_val_eq h))⟩
      exact this
  · -- Surjectivity: every seq' : Fin N → α with count = update x c (x c - 1) is in the image.
    intro seq' hseq'
    rw [Finset.mem_filter] at hseq'
    obtain ⟨_, hcount'⟩ := hseq'
    refine ⟨Fin.snoc (α := fun _ => α) seq' c, ?_, ?_⟩
    · -- Show snoc seq' c is in the source filter set.
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, Fin.snoc_last _ _⟩
      funext d
      show ((Finset.univ : Finset (Fin (N+1))).filter
        (fun i => Fin.snoc (α := fun _ => α) seq' c i = d)).card = x d
      have card_eq : ∀ (M : ℕ) (g : Fin M → α),
          ((Finset.univ : Finset (Fin M)).filter (fun i => g i = d)).card =
            ∑ i : Fin M, if g i = d then 1 else 0 := by
        intro M g
        rw [Finset.card_filter]
      rw [card_eq, Fin.sum_univ_castSucc]
      have hcount'_d : ((Finset.univ : Finset (Fin N)).filter
          (fun i => seq' i = d)).card = Function.update x c (x c - 1) d := congrFun hcount' d
      have card_seq'_eq : ∑ i : Fin N, (if seq' i = d then (1:ℕ) else 0) =
          ((Finset.univ : Finset (Fin N)).filter (fun i => seq' i = d)).card := by
        rw [Finset.card_filter]
      by_cases hcd : d = c
      · subst hcd
        simp only [Fin.snoc_castSucc, Fin.snoc_last, if_true]
        rw [card_seq'_eq, hcount'_d]
        rw [Function.update_self _ _ _]
        omega
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [if_neg (fun h => hcd h.symm), add_zero]
        rw [card_seq'_eq, hcount'_d]
        rw [Function.update_of_ne hcd]
    · -- Show Fin.init (Fin.snoc seq' c) = seq'.
      exact Fin.init_snoc _ _

/-- The multinomial counting identity: for count vectors with `Σ x = N`, the
number of sequences `Fin N → α` mapping to `x` times `∏ x_i!` equals `N!`.
This is the combinatorial heart of the Dirichlet–multinomial normalization.

Proved by induction on `N` via the `Fin.snoc` decomposition: at step `N+1`,
sequences with count `x` partition by their last element `c` (which must
have `x c > 0`), each fiber having size `multinomCount (update x c (x c - 1)) N`. -/
private theorem multinomCount_mul_prod_factorial [DecidableEq α]
    (x : α → ℕ) (N : ℕ) (hx : ∑ i, x i = N) :
    multinomCount (α := α) x N * ∏ i, (x i).factorial = N.factorial := by
  induction N generalizing x with
  | zero =>
    -- Σ x = 0 forces x = 0 everywhere. multinomCount 0 0 = 1 (the empty function),
    -- ∏ 0!= 1, 0! = 1.
    have hzero : ∀ c, x c = 0 := by
      intro c
      have := Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset α)) (f := x) (fun i _ => Nat.zero_le _)
      exact this.mp hx c (Finset.mem_univ _)
    have hprod : ∏ i, (x i).factorial = 1 := by
      rw [Finset.prod_eq_one]
      intro i _
      rw [hzero i]
      rfl
    have hcount : multinomCount (α := α) x 0 = 1 := by
      show ((Finset.univ : Finset (Fin 0 → α)).filter (fun seq => countVec seq = x)).card = 1
      rw [Finset.card_eq_one]
      refine ⟨Fin.elim0, ?_⟩
      ext seq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro _
        funext i
        exact Fin.elim0 i
      · intro h
        subst h
        funext c
        show ((Finset.univ : Finset (Fin 0)).filter (fun i => Fin.elim0 i = c)).card = x c
        rw [hzero c]
        rw [Finset.card_eq_zero]
        apply Finset.eq_empty_of_forall_notMem
        intro i _
        exact Fin.elim0 i
    rw [hcount, hprod]
    rfl
  | succ N ih =>
    -- Partition sequences by their last element (call it the "tail" color).
    -- Only colors c with x c > 0 contribute (sequences ending in c with count x
    -- exist iff x c > 0).
    -- The fiber at color c has size multinomCount (update x c (x c - 1)) N.
    -- S = ⋃_c { seq ∈ S : seq (last) = c }, and these are disjoint.
    have hS_eq : ((Finset.univ : Finset (Fin (N+1) → α)).filter
        (fun seq => countVec (N := N+1) seq = x)).card = ∑ c : α,
        ((Finset.univ : Finset (Fin (N+1) → α)).filter
          (fun seq => countVec (N := N+1) seq = x ∧ seq (Fin.last N) = c)).card := by
      -- Use Finset.card_eq_sum_card_fiberwise with the map seq ↦ seq (Fin.last N).
      rw [Finset.card_eq_sum_card_fiberwise (f := fun seq : Fin (N+1) → α => seq (Fin.last N))
        (t := (Finset.univ : Finset α)) (fun seq _ => Finset.mem_univ _)]
      apply Finset.sum_congr rfl
      intro c _
      congr 1
      ext seq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- Apply the fiber bijection lemma to each c with x c > 0.
    -- For c with x c = 0, the fiber is empty.
    have hfiber_empty : ∀ c, x c = 0 →
        ((Finset.univ : Finset (Fin (N+1) → α)).filter
          (fun seq => countVec (N := N+1) seq = x ∧ seq (Fin.last N) = c)).card = 0 := by
      intro c hxc
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro seq hseq
      rw [Finset.mem_filter] at hseq
      obtain ⟨_, hcount, hlast⟩ := hseq
      have hcount_c := congrFun hcount c
      have hpos : 0 < ((Finset.univ : Finset (Fin (N+1))).filter (fun i => seq i = c)).card := by
        rw [Finset.card_pos]
        exact ⟨Fin.last N, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlast⟩⟩
      have heq : ((Finset.univ : Finset (Fin (N+1))).filter (fun i => seq i = c)).card = x c :=
        hcount_c
      rw [heq, hxc] at hpos
      exact absurd hpos (lt_irrefl _)
    have hfiber_pos : ∀ c, 0 < x c →
        ((Finset.univ : Finset (Fin (N+1) → α)).filter
          (fun seq => countVec (N := N+1) seq = x ∧ seq (Fin.last N) = c)).card =
          multinomCount (α := α) (Function.update x c (x c - 1)) N := by
      intro c hxc
      exact multinomCount_snoc_fiber x c hxc
    -- Now combine: multinomCount.card · ∏ (x i)! = Σ_c {if x c > 0 then multinomCount (update x c (x c - 1)) N · ∏ (x i)! else 0}.
    have hSc : multinomCount (α := α) x (N+1) * ∏ i, (x i).factorial =
        ∑ c : α, if 0 < x c then
          multinomCount (α := α) (Function.update x c (x c - 1)) N * ∏ i, (x i).factorial
          else 0 := by
      show ((Finset.univ : Finset (Fin (N+1) → α)).filter
        (fun seq => countVec seq = x)).card * _ = _
      rw [hS_eq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro c _
      by_cases hxc : 0 < x c
      · rw [hfiber_pos c hxc, if_pos hxc]
      · have hxc0 : x c = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hxc)
        rw [hfiber_empty c hxc0, if_neg hxc, zero_mul]
    -- For each c with x c > 0, evaluate the IH-product:
    -- multinomCount (update x c (x c - 1)) N · ∏ (x i)! = (x c) · N!
    have hterm : ∀ c, 0 < x c →
        multinomCount (α := α) (Function.update x c (x c - 1)) N * ∏ i, (x i).factorial =
        x c * N.factorial := by
      intro c hxc
      -- Apply IH: multinomCount (update x c (x c - 1)) N · ∏ (update x c (x c - 1) i)! = N!
      have hsum_upd : ∑ i, (Function.update x c (x c - 1)) i = N := by
        have hsplit_x : ∑ i, x i =
            x c + ∑ i ∈ (Finset.univ : Finset α).erase c, x i := by
          have := Finset.sum_erase_add (Finset.univ : Finset α) x (Finset.mem_univ c)
          linarith
        have hsplit_x' : ∑ i, (Function.update x c (x c - 1)) i =
            (Function.update x c (x c - 1)) c +
              ∑ i ∈ (Finset.univ : Finset α).erase c, (Function.update x c (x c - 1)) i := by
          have := Finset.sum_erase_add (Finset.univ : Finset α)
            (Function.update x c (x c - 1)) (Finset.mem_univ c)
          linarith
        have h_erase_eq : ∑ i ∈ (Finset.univ : Finset α).erase c,
            (Function.update x c (x c - 1)) i =
            ∑ i ∈ (Finset.univ : Finset α).erase c, x i := by
          apply Finset.sum_congr rfl
          intro i hi
          have hic : i ≠ c := Finset.ne_of_mem_erase hi
          rw [Function.update_of_ne hic]
        rw [hsplit_x', Function.update_self, h_erase_eq]
        omega
      have hih := ih (Function.update x c (x c - 1)) hsum_upd
      -- Decompose ∏ (x i)! = (x c)! · ∏_{i ≠ c} (x i)!
      have hprod_x : ∏ i, ((x i).factorial) =
          (x c).factorial * ∏ i ∈ (Finset.univ : Finset α).erase c, (x i).factorial := by
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c)]
        ring
      have hprod_xupd : ∏ i, ((Function.update x c (x c - 1)) i).factorial =
          (x c - 1).factorial * ∏ i ∈ (Finset.univ : Finset α).erase c, (x i).factorial := by
        rw [← Finset.prod_erase_mul (a := c) _ _ (Finset.mem_univ c)]
        have h1 : (Function.update x c (x c - 1) c).factorial = (x c - 1).factorial := by
          rw [Function.update_self]
        have h2 : ∏ i ∈ (Finset.univ : Finset α).erase c,
            ((Function.update x c (x c - 1)) i).factorial =
            ∏ i ∈ (Finset.univ : Finset α).erase c, (x i).factorial := by
          apply Finset.prod_congr rfl
          intro i hi
          have hic : i ≠ c := Finset.ne_of_mem_erase hi
          rw [Function.update_of_ne hic]
        rw [h1, h2]
        ring
      -- (x c)! = (x c) · (x c - 1)!
      have hxc_factorial : (x c).factorial = x c * (x c - 1).factorial := by
        cases hk : x c with
        | zero => omega
        | succ k =>
          show (k + 1).factorial = (k + 1) * (k + 1 - 1).factorial
          rw [Nat.factorial_succ]
          simp
      calc multinomCount (α := α) (Function.update x c (x c - 1)) N * ∏ i, (x i).factorial
          = multinomCount (α := α) (Function.update x c (x c - 1)) N *
              ((x c).factorial * ∏ i ∈ (Finset.univ : Finset α).erase c, (x i).factorial) := by
                rw [hprod_x]
        _ = multinomCount (α := α) (Function.update x c (x c - 1)) N *
              (x c * (x c - 1).factorial *
                ∏ i ∈ (Finset.univ : Finset α).erase c, (x i).factorial) := by
                rw [hxc_factorial]
        _ = x c * (multinomCount (α := α) (Function.update x c (x c - 1)) N *
              ((x c - 1).factorial *
                ∏ i ∈ (Finset.univ : Finset α).erase c, (x i).factorial)) := by ring
        _ = x c * (multinomCount (α := α) (Function.update x c (x c - 1)) N *
              ∏ i, ((Function.update x c (x c - 1)) i).factorial) := by
                rw [hprod_xupd]
        _ = x c * N.factorial := by rw [hih]
    -- Substitute hterm into hSc.
    rw [hSc]
    have hsum_eq : (∑ c : α, if 0 < x c then
          multinomCount (α := α) (Function.update x c (x c - 1)) N * ∏ i, (x i).factorial
          else 0) =
        ∑ c : α, x c * N.factorial := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases hxc : 0 < x c
      · rw [if_pos hxc, hterm c hxc]
      · have hxc0 : x c = 0 := Nat.eq_zero_of_le_zero (Nat.not_lt.mp hxc)
        rw [if_neg hxc, hxc0, zero_mul]
    rw [hsum_eq, ← Finset.sum_mul, hx, Nat.factorial_succ]

/-- `seqProb` depends only on the count vector. -/
private theorem seqProb_eq_of_countVec [DecidableEq α] [Nonempty α]
    (x : α → ℕ) (N : ℕ) (seq : Fin N → α) (h : countVec seq = x) :
    u.seqProb (countVec seq) = u.seqProb x := by rw [h]

/-- Surjectivity-of-count: every count vector with `Σ = N` is realized by
some sequence `Fin N → α`. Construction by induction on `N` via `Fin.snoc`:
at step `N+1`, pick some color `c` with `x c > 0` (exists because `Σ x > 0`),
apply IH to `Function.update x c (x c - 1)` (which sums to `N`), then snoc `c`. -/
private theorem exists_seq_count_eq [DecidableEq α] (N : ℕ) (x : α → ℕ)
    (hx : ∑ i, x i = N) :
    ∃ seq : Fin N → α, countVec (N := N) seq = x := by
  induction N generalizing x with
  | zero =>
    -- Σ x = 0 forces x = 0; the empty function realizes it.
    refine ⟨Fin.elim0, ?_⟩
    funext c
    have hxc : x c = 0 := by
      have := Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset α)) (f := x) (fun i _ => Nat.zero_le _)
      have h0 : ∀ i ∈ (Finset.univ : Finset α), x i = 0 :=
        this.mp hx
      exact h0 c (Finset.mem_univ _)
    rw [hxc]
    show ((Finset.univ : Finset (Fin 0)).filter _).card = 0
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_of_forall_notMem
    intro i _
    exact Fin.elim0 i
  | succ N ih =>
    -- Find some color `c` with `x c > 0` (exists because Σ x = N+1 > 0).
    have hsum_pos : 0 < ∑ i, x i := by rw [hx]; exact Nat.succ_pos _
    have hex : ∃ c, 0 < x c := by
      by_contra h
      have h' : ∀ c, ¬ 0 < x c := fun c hc => h ⟨c, hc⟩
      have hzero : ∑ i, x i = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact Nat.eq_zero_of_le_zero (Nat.not_lt.mp (h' i))
      omega
    obtain ⟨c, hc⟩ := hex
    -- Decrement x at c: x' = update x c (x c - 1).
    set x' : α → ℕ := Function.update x c (x c - 1) with hx'_def
    have hsum_x' : ∑ i, x' i = N := by
      have hsplit : ∑ i, x i =
          x c + ∑ i ∈ (Finset.univ : Finset α).erase c, x i := by
        have := Finset.sum_erase_add (Finset.univ : Finset α) x (Finset.mem_univ c)
        linarith
      have hsplit' : ∑ i, x' i =
          x' c + ∑ i ∈ (Finset.univ : Finset α).erase c, x' i := by
        have := Finset.sum_erase_add (Finset.univ : Finset α) x' (Finset.mem_univ c)
        linarith
      have h_erase : ∑ i ∈ (Finset.univ : Finset α).erase c, x' i =
          ∑ i ∈ (Finset.univ : Finset α).erase c, x i := by
        apply Finset.sum_congr rfl
        intro i hi
        have hic : i ≠ c := Finset.ne_of_mem_erase hi
        show Function.update x c (x c - 1) i = x i
        rw [Function.update_of_ne hic]
      have hxc' : x' c = x c - 1 := Function.update_self _ _ _
      rw [hsplit', hxc', h_erase]
      omega
    -- Apply IH to x'.
    obtain ⟨seq', hseq'⟩ := ih x' hsum_x'
    refine ⟨Fin.snoc (α := fun _ => α) seq' c, ?_⟩
    -- Show count vector of (snoc seq' c) equals x.
    funext d
    have h_seq'_d : ((Finset.univ : Finset (Fin N)).filter
        (fun i => seq' i = d)).card = x' d := congrFun hseq' d
    have card_seq'_eq : ∑ i : Fin N, (if seq' i = d then (1:ℕ) else 0) =
        ((Finset.univ : Finset (Fin N)).filter (fun i => seq' i = d)).card := by
      rw [Finset.card_filter]
    show ((Finset.univ : Finset (Fin (N+1))).filter
        (fun i => Fin.snoc (α := fun _ => α) seq' c i = d)).card = x d
    rw [Finset.card_filter, Fin.sum_univ_castSucc]
    by_cases hcd : d = c
    · subst hcd
      simp only [Fin.snoc_castSucc, Fin.snoc_last, if_true]
      rw [card_seq'_eq, h_seq'_d]
      have h_x'd : x' d = x d - 1 := Function.update_self _ _ _
      rw [h_x'd]
      omega
    · simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [if_neg (fun h => hcd h.symm), add_zero]
      rw [card_seq'_eq, h_seq'_d]
      show x' d = x d
      rw [hx'_def, Function.update_of_ne hcd]

/-- Every x with `Σ x = N` lies in `countVectors N`. -/
private theorem mem_countVectors_of_sum_eq [DecidableEq α] {N : ℕ} {x : α → ℕ}
    (hx : ∑ i, x i = N) : x ∈ countVectors (α := α) N := by
  obtain ⟨seq, hseq⟩ := exists_seq_count_eq N x hx
  exact Finset.mem_image.mpr ⟨seq, Finset.mem_univ _, hseq⟩

/-- The total Real-valued sum `∑ x ∈ countVectors N, pmfReal u x = 1`.
Follows from `PolyaUrn.sum_seqProb_eq_one` by fiberwise regrouping
(sequences → count vectors) and the multinomial counting identity. -/
private theorem sum_pmfReal_eq_one [DecidableEq α] [Nonempty α] (N : ℕ) :
    (∑ x ∈ countVectors (α := α) N, pmfReal u x) = 1 := by
  -- Step 1: `∑ seq, seqProb (count seq) = 1` is given. Note that `countVec`
  -- here is the same as the inline `fun c => ...` in `sum_seqProb_eq_one`.
  have h_seq_sum :
      (∑ seq : Fin N → α, u.seqProb (countVec (N := N) seq)) = 1 :=
    u.sum_seqProb_eq_one N
  -- Step 2: regroup the sequence sum by count vector via `sum_fiberwise`.
  have h_fiber :
      (∑ seq : Fin N → α, u.seqProb (countVec (N := N) seq)) =
        ∑ x ∈ countVectors (α := α) N,
          ∑ seq ∈ (Finset.univ : Finset (Fin N → α)).filter
              (fun s => countVec (N := N) s = x),
            u.seqProb (countVec (N := N) seq) := by
    refine (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin N → α)))
      (t := countVectors (α := α) N)
      (g := fun seq => countVec (N := N) seq)
      (f := fun seq => u.seqProb (countVec (N := N) seq))
      (fun seq _ => Finset.mem_image.mpr ⟨seq, Finset.mem_univ _, rfl⟩)).symm
  -- Step 3: in each fiber, `seqProb (count seq) = seqProb x`, so the inner sum is
  -- `(card of fiber) · seqProb x = multinomCount x N · seqProb x`.
  have h_inner : ∀ x ∈ countVectors (α := α) N,
      (∑ seq ∈ (Finset.univ : Finset (Fin N → α)).filter
          (fun s => countVec (N := N) s = x),
          u.seqProb (countVec (N := N) seq)) =
        (multinomCount (α := α) x N : ℝ) * u.seqProb x := by
    intro x _
    have hcong : ∀ seq ∈ (Finset.univ : Finset (Fin N → α)).filter
                  (fun s => countVec (N := N) s = x),
          u.seqProb (countVec (N := N) seq) = u.seqProb x := by
      intro seq hseq
      rw [(Finset.mem_filter.mp hseq).2]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, nsmul_eq_mul]
    rfl
  rw [h_fiber, Finset.sum_congr rfl h_inner] at h_seq_sum
  -- Step 4: rewrite each `multinomCount x N · seqProb x = pmfReal u x` using
  -- the multinomial counting identity.
  have h_pmf : ∀ x ∈ countVectors (α := α) N,
      (multinomCount (α := α) x N : ℝ) * u.seqProb x = pmfReal u x := by
    intro x hx
    have hxN : ∑ i, x i = N := mem_countVectors hx
    unfold pmfReal
    rw [hxN]
    have hkey := multinomCount_mul_prod_factorial (α := α) x N hxN
    have h_prod_pos : (0 : ℝ) < ∏ i, ((x i).factorial : ℝ) := by
      have : (0 : ℕ) < ∏ i, (x i).factorial :=
        Finset.prod_pos (fun i _ => Nat.factorial_pos _)
      exact_mod_cast this
    have h_prod_ne : (∏ i, ((x i).factorial : ℝ)) ≠ 0 := h_prod_pos.ne'
    have hcast : ((multinomCount (α := α) x N : ℝ) * ∏ i, ((x i).factorial : ℝ)) =
        (N.factorial : ℝ) := by
      have h := congrArg (Nat.cast (R := ℝ)) hkey
      push_cast at h
      convert h using 1
    have hmult_eq : (multinomCount (α := α) x N : ℝ) =
        (N.factorial : ℝ) / ∏ i, ((x i).factorial : ℝ) := by
      field_simp
      linarith
    rw [hmult_eq]
  rw [Finset.sum_congr rfl h_pmf] at h_seq_sum
  exact h_seq_sum

/--
**Dirichlet–multinomial normalization.** The closed-form mass sums
to `1` over count vectors of any fixed total `N` (zero elsewhere).

Proof structure (sequence-based, not Dirichlet-integration-based):

1. `PolyaUrn.sum_seqProb_eq_one`: per-sequence likelihood sums to 1
   over `Fin N → α` (already proved).
2. `Finset.sum_fiberwise_of_maps_to`: regroup the sequence sum by count
   vector; the inner sum over each fiber gives `(card of fiber) · seqProb x`.
3. `multinomCount_mul_prod_factorial` (sorried): `card of fiber = N!/∏x_i!`,
   matching `pmfReal x = (N!/∏x_i!) · seqProb x`.
4. `exists_seq_count_eq` (sorried): every x with `Σ = N` lies in the count
   image, so the function vanishes outside this finite set.
5. `hasSum_sum_of_ne_finset_zero` + `ENNReal.ofReal_sum_of_nonneg`: lift the
   real-valued finite-sum result to the desired `HasSum` over ENNReal.

Both sorries are routine combinatorial constructions on `Fin N → α`
(induction on `N` via `Fin.snocEquiv`, list-based enumeration of `α`).
-/
theorem pmfReal_hasSum_one [DecidableEq α] [Nonempty α] (N : ℕ) :
    HasSum (fun x : α → ℕ =>
      if ∑ i, x i = N then ENNReal.ofReal (pmfReal u x) else 0) 1 := by
  classical
  -- Step A: the function vanishes outside the finite set `countVectors N`
  -- (combining `mem_countVectors_of_sum_eq` with the if-condition).
  have h_zero : ∀ x ∉ countVectors (α := α) N,
      (if ∑ i, x i = N then ENNReal.ofReal (pmfReal u x) else 0) = 0 := by
    intro x hx
    by_cases hsum : ∑ i, x i = N
    · exfalso; exact hx (mem_countVectors_of_sum_eq hsum)
    · simp [hsum]
  -- Step B: Real-sum result lifted to ENNReal.
  have h_sum_real : (∑ x ∈ countVectors (α := α) N, pmfReal u x) = 1 :=
    sum_pmfReal_eq_one u N
  -- Step C: assemble HasSum from finite support and the Real sum.
  -- Use `hasSum_sum_of_ne_finset_zero`: HasSum f (Σ x ∈ s, f x) when f x = 0 ∉ s.
  have h_hassum : HasSum (fun x : α → ℕ =>
      if ∑ i, x i = N then ENNReal.ofReal (pmfReal u x) else 0)
      (∑ x ∈ countVectors (α := α) N,
        if ∑ i, x i = N then ENNReal.ofReal (pmfReal u x) else 0) :=
    hasSum_sum_of_ne_finset_zero h_zero
  -- Step D: simplify the finite sum: in countVectors N, every x has Σ = N,
  -- so the if-branch reduces to `ENNReal.ofReal (pmfReal u x)`.
  have h_simp :
      (∑ x ∈ countVectors (α := α) N,
        (if ∑ i, x i = N then ENNReal.ofReal (pmfReal u x) else 0)) =
      ∑ x ∈ countVectors (α := α) N, ENNReal.ofReal (pmfReal u x) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [if_pos (mem_countVectors hx)]
  rw [h_simp] at h_hassum
  -- Step E: ENNReal.ofReal of a finset sum of nonnegatives = ofReal sum.
  have h_ofReal_sum :
      (∑ x ∈ countVectors (α := α) N, ENNReal.ofReal (pmfReal u x)) =
        ENNReal.ofReal (∑ x ∈ countVectors (α := α) N, pmfReal u x) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro x _
    exact pmfReal_nonneg u x
  rw [h_ofReal_sum, h_sum_real] at h_hassum
  simpa using h_hassum

/--
The Dirichlet–multinomial distribution as a proper `PMF (α → ℕ)`,
supported on count vectors summing to `N`.

Constructed directly from `HasSum` (mirroring mathlib's Poisson
`⟨ENNReal.ofReal ∘ poissonPMFReal r, _⟩`) rather than via heavier
`PMF.ofFinset` / `Finset.piAntidiag` machinery — see file docstring.
-/
noncomputable def pmf [DecidableEq α] [Nonempty α] (N : ℕ) : PMF (α → ℕ) :=
  ⟨fun x => if ∑ i, x i = N then ENNReal.ofReal (pmfReal u x) else 0,
   pmfReal_hasSum_one u N⟩

/-- Closed-form value at a count vector summing to `N`. -/
@[simp]
theorem pmf_apply [DecidableEq α] [Nonempty α] (N : ℕ) (x : α → ℕ)
    (hx : ∑ i, x i = N) :
    pmf u N x = ENNReal.ofReal (pmfReal u x) := by
  show (if ∑ i, x i = N then _ else 0) = _
  exact if_pos hx

/-- Outside its support (count vectors that don't sum to `N`), the
    Dirichlet–multinomial PMF is zero. -/
theorem pmf_apply_of_sum_ne [DecidableEq α] [Nonempty α]
    (N : ℕ) (x : α → ℕ) (hx : ∑ i, x i ≠ N) :
    pmf u N x = 0 := by
  show (if ∑ i, x i = N then _ else 0) = _
  exact if_neg hx

end DirichletMultinomial

end ProbabilityTheory
