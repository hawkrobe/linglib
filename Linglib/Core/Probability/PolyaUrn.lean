import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Pólya urn (per-sequence likelihood)

@cite{odonnell-2015}

A *Pólya urn* over an alphabet `α` is a sequential sampling
scheme governed by strictly-positive pseudo-counts
`π : α → ℝ`. The first draw is categorical with weights
`π_i / Σ π`; the `(N + 1)`-th draw conditional on previous counts
`x_1, …` is categorical with weights `(π_i + x_i) / (Σ π + Σ x)` — a
preferential-attachment dynamic, finite-`K` variant of the
power-law-tail dynamic that the Pitman–Yor process exhibits in the
unbounded-alphabet limit.

By Dirichlet–Categorical conjugacy, drawing `θ ~ Dirichlet(π)` then
sampling i.i.d. from `Categorical(θ)` and integrating out `θ` yields
the same exchangeable sequence law (the de Finetti representation
theorem guarantees that *some* mixing measure exists; identifying it
as Dirichlet is conjugacy + integration). The probability of any
specific draw sequence with counts `x_1, …, x_K` has the closed form
of @cite{odonnell-2015} eq 3.7 (-- UNVERIFIED: section/equation
number from memory; verify against PDF):

```
P(seq | π) = Γ(Σ π) / Γ(Σ π + Σ x)  ·  ∏ Γ(π_i + x_i) / Γ(π_i)
```

This file gives only the closed-form per-sequence likelihood
`seqProb` — the form fragment-grammar consumers in
`Theories/Morphology/FragmentGrammars/` actually use (a corpus IS a
labeled derivation sequence, not a draw from the unlabeled-count
distribution). The corresponding count-vector PMF — the
"Dirichlet–multinomial distribution" — lives in the sibling file
`DirichletMultinomial.lean`, which carries the heavier
`Probability.ProbabilityMassFunction.Basic` import (transitively
~10s of olean loading via `MeasureTheory.Measure.Dirac`).

The sequential sampler itself is not formalized — only the closed
form is needed by downstream constructions.

## Type-polymorphic alphabet

The alphabet `α` is an arbitrary type; operations require
`[Fintype α]` (so that `∑ i, ...` and `∏ i, ...` are well-defined),
and theorems requiring positivity of the total pseudo-count
additionally need `[Nonempty α]`. The previous `Fin K`-indexed shape
is the special case `α = Fin K` (with `[NeZero K]` equivalent to
`[Nonempty (Fin K)]`); the polymorphic shape composes cleanly with
`Finset`-restricted alphabets needed by per-LHS PCFG factors.

## Relationship to `PitmanYor`

The Pólya urn is often described as the "finite-K Chinese Restaurant
Process". This is correct sequentially but misleading
distributionally: the labeled count distribution
`DirichletMultinomial.pmf` (sibling file) is *not* equal at any
finite `K` to the partition distribution `PitmanYor.partitionProb`
at `discount = 0`. The two agree only in the limit `K → ∞` with
symmetric pseudo-counts `π_i = b/K` (Blackwell & MacQueen 1973;
Ferguson 1973). The bridge is therefore a limit theorem, not a
finite equality, and is not yet formalized — the labeled→unlabeled
`.map` pushforward to `PMF (Nat.Partition N)` (the natural target
type for such a bridge) is also deferred.

## Main definitions

- `PolyaUrn α` — pseudo-counts on `α` (the Dirichlet hyperparameters).
- `PolyaUrn.total` — the sum `Σ π_i`.
- `PolyaUrn.seqProb` — closed-form per-sequence likelihood
  (eq 3.7 of @cite{odonnell-2015}, depending only on counts).

## References

- @cite{odonnell-2015} — Pólya-urn closed form for DMPCFG (-- UNVERIFIED:
  §3.1.3 eq 3.7 from memory; verify against PDF).
- Blackwell, D. & MacQueen, J. B. (1973). "Ferguson distributions via
  Pólya urn schemes". *The Annals of Statistics* 1(2): 353–355.
- Ferguson, T. S. (1973). "A Bayesian analysis of some nonparametric
  problems". *The Annals of Statistics* 1(2): 209–230.
-/

namespace ProbabilityTheory

open Real

/--
A Pólya urn scheme over the alphabet `α`, parameterized by
strictly-positive pseudo-counts. In the de Finetti representation
the pseudo-counts are the Dirichlet hyperparameters: i.i.d. draws
from `Categorical(θ)` for `θ ~ Dirichlet(pseudo)` have the same
exchangeable sequence law as the Pólya urn.
-/
@[ext]
structure PolyaUrn (α : Type*) where
  /-- Per-color pseudo-count (the Dirichlet hyperparameter). -/
  pseudo : α → ℝ
  /-- Pseudo-counts are strictly positive. -/
  pseudo_pos : ∀ i, 0 < pseudo i

namespace PolyaUrn

variable {α : Type*} [Fintype α] (u : PolyaUrn α)

/-- The total pseudo-count `Σ π_i`. Strictly positive when `α` is nonempty. -/
def total : ℝ := ∑ i, u.pseudo i

theorem total_pos [Nonempty α] : 0 < u.total :=
  Finset.sum_pos (fun i _ => u.pseudo_pos i) Finset.univ_nonempty

/--
Closed-form *per-sequence likelihood* (not the count PMF — see
`DirichletMultinomial.pmfReal` for that): probability that a draw
sequence with counts `x` was emitted by the urn `u`.

```
P(seq | π) = Γ(Σ π) / Γ(Σ π + Σ x)  ·  ∏ Γ(π_i + x_i) / Γ(π_i)
```

Depends only on the counts (not the order), which is what makes the
recursive stochastic equations defining DMPCFG, adaptor grammars, and
fragment grammars in `Theories.Morphology.FragmentGrammars.*`
well-defined as marginals over draw order — *partition
exchangeability* in the EPPF sense, distinct from but implied by
exchangeability proper of the joint sequence law.

To convert to the count-vector PMF, multiply by the multinomial
coefficient `(∑ x_i)! / ∏ (x_i!)`. See `DirichletMultinomial`.
-/
noncomputable def seqProb (x : α → ℕ) : ℝ :=
  Gamma u.total / Gamma (u.total + ∑ i, (x i : ℝ)) *
    ∏ i, Gamma (u.pseudo i + x i) / Gamma (u.pseudo i)

/-- The empty count vector — no draws — has per-sequence likelihood `1`. -/
theorem seqProb_zero [Nonempty α] :
    u.seqProb (fun _ => 0) = 1 := by
  unfold seqProb
  simp only [Nat.cast_zero, Finset.sum_const_zero, add_zero]
  rw [div_self (Gamma_pos_of_pos u.total_pos).ne', one_mul]
  apply Finset.prod_eq_one
  intro i _
  exact div_self (Gamma_pos_of_pos (u.pseudo_pos i)).ne'

/--
**Pólya urn predictive recurrence.** Incrementing the count at color `c`
by 1 multiplies `seqProb` by the Pólya predictive factor
`(π_c + x_c) / (Σπ + Σx)`:

```
seqProb (x with x_c := x_c + 1) = seqProb x · (π_c + x_c) / (Σπ + Σx)
```

This is the discrete-time recursion underlying the Dirichlet–Multinomial
normalization. Proof: unfold `seqProb`, apply `Real.Gamma_add_one` at
both `Σπ + Σx` (denominator) and `π_c + x_c` (the c-th factor in the
product), and let the other terms cancel.
-/
theorem seqProb_succ [Nonempty α] [DecidableEq α] (x : α → ℕ) (c : α) :
    u.seqProb (Function.update x c (x c + 1)) =
      u.seqProb x * (u.pseudo c + x c) / (u.total + ∑ i, (x i : ℝ)) := by
  -- ## Proof strategy
  --
  -- LHS = Γ(Σπ) / Γ(Σπ + Σx + 1) · Γ(π_c + x_c + 1) / Γ(π_c) · ∏_{i≠c} Γ(π_i+x_i)/Γ(π_i)
  -- Apply `Real.Gamma_add_one` at the (Σπ + Σx + 1) denominator and at the
  -- (π_c + x_c + 1) c-th product factor, then field_simp + ring.
  -- Setup: positivity facts, abbreviations.
  have h_total_pos : 0 < u.total := u.total_pos
  have h_x_nn : (0 : ℝ) ≤ ∑ i, (x i : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have h_pseudo_c_pos : 0 < u.pseudo c := u.pseudo_pos c
  have h_xc_nn : (0 : ℝ) ≤ (x c : ℝ) := Nat.cast_nonneg _
  have h_S_pos : 0 < u.total + ∑ i, (x i : ℝ) := by linarith
  have h_S_ne : u.total + ∑ i, (x i : ℝ) ≠ 0 := h_S_pos.ne'
  have h_pc_pos : 0 < u.pseudo c + (x c : ℝ) := by linarith
  have h_pc_ne : u.pseudo c + (x c : ℝ) ≠ 0 := h_pc_pos.ne'
  -- Step 1: rewrite the sum over the updated function as ∑ x + 1.
  -- Strategy: cast Function.update through Nat.cast, then use sum_update_of_mem.
  have h_sum_update : (∑ i, ((Function.update x c (x c + 1)) i : ℝ)) =
      (∑ i, (x i : ℝ)) + 1 := by
    have heq : (fun i => ((Function.update x c (x c + 1)) i : ℝ)) =
        Function.update (fun i => (x i : ℝ)) c ((x c : ℝ) + 1) := by
      funext i
      by_cases hi : i = c
      · subst hi; simp
      · simp [hi]
    rw [show (∑ i, ((Function.update x c (x c + 1)) i : ℝ)) =
          ∑ i, (Function.update (fun i => (x i : ℝ)) c ((x c : ℝ) + 1)) i by rw [heq]]
    rw [Finset.sum_update_of_mem (Finset.mem_univ c)]
    have hsplit : (∑ i, (x i : ℝ)) =
        (x c : ℝ) + ∑ i ∈ Finset.univ \ {c}, (x i : ℝ) := by
      have hh := Finset.sum_update_of_mem (Finset.mem_univ c)
        (f := fun i => (x i : ℝ)) (b := (x c : ℝ))
      -- hh : ∑ i, Function.update (...) c (x c) i = (x c) + ∑ i ∈ univ \ {c}, x i
      -- LHS reduces to ∑ i, (x i : ℝ) since updating with the original value is the function.
      have hupd : (fun i => Function.update (fun i => (x i : ℝ)) c ((x c : ℝ)) i) =
          (fun i => (x i : ℝ)) := by
        funext i; by_cases hi : i = c
        · subst hi; simp
        · simp [hi]
      rw [hupd] at hh
      linarith
    linarith
  -- Step 2: rewrite the product over the updated function.
  -- Pull out the c-th factor (at the updated value) using prod_update_of_mem.
  have h_prod_update :
      (∏ i, Gamma (u.pseudo i + (Function.update x c (x c + 1)) i) / Gamma (u.pseudo i)) =
        (Gamma (u.pseudo c + ((x c : ℝ) + 1)) / Gamma (u.pseudo c)) *
          ∏ i ∈ Finset.univ \ {c}, Gamma (u.pseudo i + x i) / Gamma (u.pseudo i) := by
    have heq : (fun i => Gamma (u.pseudo i + (Function.update x c (x c + 1)) i) / Gamma (u.pseudo i)) =
        Function.update
          (fun i => Gamma (u.pseudo i + (x i : ℝ)) / Gamma (u.pseudo i))
          c
          (Gamma (u.pseudo c + ((x c : ℝ) + 1)) / Gamma (u.pseudo c)) := by
      funext i
      by_cases hi : i = c
      · rw [hi]
        have hcast : ((x c + 1 : ℕ) : ℝ) = (x c : ℝ) + 1 := by push_cast; ring
        simp [hcast]
      · simp [hi]
    rw [show (∏ i, Gamma (u.pseudo i + (Function.update x c (x c + 1)) i) / Gamma (u.pseudo i)) =
          ∏ i, (Function.update
                  (fun i => Gamma (u.pseudo i + (x i : ℝ)) / Gamma (u.pseudo i))
                  c
                  (Gamma (u.pseudo c + ((x c : ℝ) + 1)) / Gamma (u.pseudo c))) i by rw [heq]]
    exact Finset.prod_update_of_mem (Finset.mem_univ c) _ _
  -- Step 3: similarly pull out the c-th factor for `seqProb x`.
  have h_prod_x :
      (∏ i, Gamma (u.pseudo i + x i) / Gamma (u.pseudo i)) =
        (Gamma (u.pseudo c + x c) / Gamma (u.pseudo c)) *
          ∏ i ∈ Finset.univ \ {c}, Gamma (u.pseudo i + x i) / Gamma (u.pseudo i) := by
    have := Finset.prod_update_of_mem (Finset.mem_univ c)
      (f := fun i => Gamma (u.pseudo i + (x i : ℝ)) / Gamma (u.pseudo i))
      (b := Gamma (u.pseudo c + (x c : ℝ)) / Gamma (u.pseudo c))
    -- LHS of `this`: ∏ x ∈ univ, Function.update f c (f c) x = ∏ x ∈ univ, f x
    rw [show (fun i => Function.update
              (fun i => Gamma (u.pseudo i + (x i : ℝ)) / Gamma (u.pseudo i))
              c
              (Gamma (u.pseudo c + (x c : ℝ)) / Gamma (u.pseudo c)) i) =
          (fun i => Gamma (u.pseudo i + (x i : ℝ)) / Gamma (u.pseudo i)) from ?_] at this
    · exact this
    · funext i
      by_cases hi : i = c
      · subst hi; simp
      · simp [hi]
  -- Step 4: apply Gamma_add_one to the two (... + 1) Gammas.
  have h_S_ne_for_gamma : u.total + ∑ i, (x i : ℝ) ≠ 0 := h_S_ne
  have h_gamma_S :
      Gamma (u.total + ((∑ i, (x i : ℝ)) + 1)) =
        (u.total + ∑ i, (x i : ℝ)) * Gamma (u.total + ∑ i, (x i : ℝ)) := by
    have : u.total + ((∑ i, (x i : ℝ)) + 1) = (u.total + ∑ i, (x i : ℝ)) + 1 := by ring
    rw [this, Real.Gamma_add_one h_S_ne_for_gamma]
  have h_gamma_pc :
      Gamma (u.pseudo c + ((x c : ℝ) + 1)) =
        (u.pseudo c + (x c : ℝ)) * Gamma (u.pseudo c + (x c : ℝ)) := by
    have : u.pseudo c + ((x c : ℝ) + 1) = (u.pseudo c + (x c : ℝ)) + 1 := by ring
    rw [this, Real.Gamma_add_one h_pc_ne]
  -- Step 5: assemble. Unfold seqProb on both sides.
  unfold seqProb
  rw [h_sum_update, h_prod_update, h_prod_x, h_gamma_S, h_gamma_pc]
  -- Now both sides should match after field_simp + ring.
  -- Goal shape:
  --   Γ(Σπ) / ((Σπ+Σx) * Γ(Σπ+Σx)) * ((π_c+x_c) * Γ(π_c+x_c) / Γ(π_c) * P)
  --   = Γ(Σπ) / Γ(Σπ+Σx) * (Γ(π_c+x_c) / Γ(π_c) * P) * (π_c + x_c) / (Σπ+Σx)
  -- where P = prod over univ \ {c}.
  have hΓ_S_ne : Gamma (u.total + ∑ i, (x i : ℝ)) ≠ 0 :=
    (Gamma_pos_of_pos h_S_pos).ne'
  have hΓ_pc_ne : Gamma (u.pseudo c) ≠ 0 := (Gamma_pos_of_pos h_pseudo_c_pos).ne'
  field_simp

omit [Fintype α] in
/-- Count-vector identity: appending color `c` to a length-`N` sequence
increments the count at `c` by 1 and leaves other counts unchanged. -/
private lemma snoc_count_eq [DecidableEq α] {N : ℕ}
    (seq' : Fin N → α) (c : α) :
    (fun d => (Finset.univ.filter (fun i : Fin (N+1) => Fin.snoc seq' c i = d)).card) =
      Function.update (fun d => (Finset.univ.filter (fun i : Fin N => seq' i = d)).card) c
        ((Finset.univ.filter (fun i : Fin N => seq' i = c)).card + 1) := by
  funext d
  have card_eq : ∀ (M : ℕ) (g : Fin M → α),
      ((Finset.univ : Finset (Fin M)).filter (fun i => g i = d)).card =
        ∑ i : Fin M, if g i = d then 1 else 0 := by
    intro M g
    rw [Finset.card_filter]
  by_cases hcd : d = c
  · subst hcd
    rw [Function.update_self, card_eq, card_eq, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, if_true]
  · rw [Function.update_of_ne hcd, card_eq, card_eq, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [if_neg (fun h => hcd h.symm), add_zero]

/-- The total count of a length-`N` sequence equals `N`. -/
lemma sum_counts_eq_length [DecidableEq α] {N : ℕ}
    (seq : Fin N → α) :
    ∑ d : α, ((Finset.univ : Finset (Fin N)).filter (fun i => seq i = d)).card = N := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ i : Fin N, ∑ d : α, (if seq i = d then 1 else 0 : ℕ) = 1 := by
    intro i
    rw [Finset.sum_eq_single (seq i)]
    · simp
    · intros b _ hb; rw [if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [this]
  simp

/-- `seqProb` summed over all length-`N` sequences equals 1. The Polya urn
defines a probability distribution over sequences; this identity says the
total mass is 1. Proved by induction on `N` using `seqProb_succ`. -/
theorem sum_seqProb_eq_one [Nonempty α] [DecidableEq α] (N : ℕ) :
    (∑ seq : Fin N → α, u.seqProb (fun c => (Finset.univ.filter (seq · = c)).card)) = 1 := by
  induction N with
  | zero =>
    -- Only one sequence: `Fin.elim0`. Show its count vector is `fun _ => 0`,
    -- then close via `seqProb_zero`.
    have hcounts : ∀ (seq : Fin 0 → α),
        (fun c => ((Finset.univ : Finset (Fin 0)).filter (seq · = c)).card) =
          (fun _ : α => 0) := by
      intro seq
      funext c
      have : ((Finset.univ : Finset (Fin 0)).filter (fun i => seq i = c)) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro i; exact Fin.elim0 i
      rw [this, Finset.card_empty]
    have hunique : (Finset.univ : Finset (Fin 0 → α)) = {Fin.elim0} := by
      rw [Finset.eq_singleton_iff_unique_mem]
      refine ⟨Finset.mem_univ _, fun seq _ => ?_⟩
      funext i; exact Fin.elim0 i
    rw [hunique, Finset.sum_singleton, hcounts, u.seqProb_zero]
  | succ N ih =>
    -- Decompose `Fin (N+1) → α` via `Fin.snocEquiv` (prefix + last element).
    have step1 :
        (∑ seq : Fin (N+1) → α,
            u.seqProb (fun c => (Finset.univ.filter (seq · = c)).card)) =
        ∑ p : α × (Fin N → α),
            u.seqProb (fun c =>
              (Finset.univ.filter
                ((Fin.snoc p.2 p.1 : Fin (N+1) → α) · = c)).card) := by
      apply Fintype.sum_equiv
        (Fin.snocEquiv (fun _ : Fin (N+1) => α) :
          α × (Fin N → α) ≃ (Fin (N+1) → α)).symm
      intro seq
      congr 1
      funext c
      congr 1
      apply Finset.filter_congr
      intro i _
      have hsnoc : Fin.snoc (((Fin.snocEquiv (fun _ : Fin (N+1) => α)).symm seq).2)
            (((Fin.snocEquiv (fun _ : Fin (N+1) => α)).symm seq).1) = seq := by
        show Fin.snoc (Fin.init seq) (seq (Fin.last N)) = seq
        exact Fin.snoc_init_self seq
      rw [hsnoc]
    rw [step1, Fintype.sum_prod_type]
    -- Apply `snoc_count_eq` to rewrite the count of `Fin.snoc seq' c` as
    -- `Function.update (count seq') c (count seq' c + 1)`.
    have step2 : ∀ (c : α) (seq' : Fin N → α),
        u.seqProb (fun d => (Finset.univ.filter
            ((Fin.snoc seq' c : Fin (N+1) → α) · = d)).card) =
        u.seqProb (Function.update
            (fun d => (Finset.univ.filter (seq' · = d)).card) c
            ((Finset.univ.filter (seq' · = c)).card + 1)) := by
      intro c seq'
      rw [snoc_count_eq seq' c]
    simp_rw [step2]
    -- Apply the predictive recurrence `seqProb_succ`.
    simp_rw [u.seqProb_succ]
    -- Replace `∑ i, count seq' i` by `N` via `sum_counts_eq_length`.
    have step3 : ∀ (seq' : Fin N → α),
        (∑ i, ((fun d => (Finset.univ.filter (seq' · = d)).card) i : ℝ)) = N := by
      intro seq'
      rw [show (∑ i, ((fun d => (Finset.univ.filter (seq' · = d)).card) i : ℝ)) =
            ((∑ i, (Finset.univ.filter (seq' · = i)).card : ℕ) : ℝ) by push_cast; rfl]
      congr 1
      exact_mod_cast sum_counts_eq_length seq'
    simp_rw [step3]
    -- Swap the outer-c and inner-seq' sums, then sum the predictive factor
    -- `(π_c + count seq' c) / (total + N)` over `c` to get 1.
    rw [Finset.sum_comm]
    have step4 : ∀ (seq' : Fin N → α),
        (∑ c : α, u.seqProb (fun d => (Finset.univ.filter (seq' · = d)).card) *
              (u.pseudo c + ((Finset.univ.filter (seq' · = c)).card : ℝ)) /
              (u.total + N)) =
          u.seqProb (fun d => (Finset.univ.filter (seq' · = d)).card) := by
      intro seq'
      have h_total_pos : 0 < u.total := u.total_pos
      have h_denom_pos : 0 < u.total + (N : ℝ) := by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg _
        linarith
      have h_denom_ne : u.total + (N : ℝ) ≠ 0 := h_denom_pos.ne'
      rw [show (∑ c : α, u.seqProb (fun d => (Finset.univ.filter (seq' · = d)).card) *
                  (u.pseudo c + ((Finset.univ.filter (seq' · = c)).card : ℝ)) /
                  (u.total + N)) =
              u.seqProb (fun d => (Finset.univ.filter (seq' · = d)).card) *
                (∑ c : α, (u.pseudo c + ((Finset.univ.filter (seq' · = c)).card : ℝ))) /
                (u.total + N) from ?_]
      · have sum_eq :
            (∑ c : α, (u.pseudo c + ((Finset.univ.filter (seq' · = c)).card : ℝ))) =
              u.total + N := by
          rw [Finset.sum_add_distrib]
          rw [show (∑ c : α, ((Finset.univ.filter (seq' · = c)).card : ℝ)) = (N : ℝ) from ?_]
          · rfl
          · exact_mod_cast sum_counts_eq_length seq'
        rw [sum_eq]
        field_simp
      · rw [Finset.mul_sum, ← Finset.sum_div]
    simp_rw [step4]
    exact ih

/--
Per-sequence Pólya likelihood is strictly positive on nonempty
alphabets. Used by downstream consumers (`DMPCFG`, `AdaptorGrammar`)
to derive nonnegativity of corpus probabilities.
-/
theorem seqProb_pos [Nonempty α] (x : α → ℕ) :
    0 < u.seqProb x := by
  have h_total_pos : 0 < u.total := u.total_pos
  have h_x_nn : (0 : ℝ) ≤ ∑ i, (x i : ℝ) :=
    Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
  have hΓ_num_pos : 0 < Gamma u.total := Gamma_pos_of_pos h_total_pos
  have hΓ_den_pos : 0 < Gamma (u.total + ∑ i, (x i : ℝ)) :=
    Gamma_pos_of_pos (by linarith)
  have hRatio_pos :
      0 < Gamma u.total / Gamma (u.total + ∑ i, (x i : ℝ)) :=
    div_pos hΓ_num_pos hΓ_den_pos
  have hProd_pos :
      0 < ∏ i, Gamma (u.pseudo i + x i) / Gamma (u.pseudo i) := by
    apply Finset.prod_pos
    intro i _
    have h_psi_pos : 0 < u.pseudo i := u.pseudo_pos i
    have h_xi_nn : (0 : ℝ) ≤ (x i : ℝ) := Nat.cast_nonneg _
    refine div_pos (Gamma_pos_of_pos ?_) (Gamma_pos_of_pos h_psi_pos)
    linarith
  unfold seqProb
  exact mul_pos hRatio_pos hProd_pos

-- Symmetric Polya urn: convenience constructor

variable [Nonempty α]

omit [Nonempty α] in
/-- Construct a symmetric Polya urn with concentration `c` on every color.
The Dirichlet-conjugate prior `Dirichlet(c, c, …, c)` underlying any
"all colors equally a priori" scheme. -/
def symmetric (c : ℝ) (hc : 0 < c) : PolyaUrn α where
  pseudo _ := c
  pseudo_pos _ := hc

-- Predictive distribution: P(next draw = i | observed counts)

/-- The Polya predictive: probability that the next draw is color `i`,
given observed counts. Closed form
`(π_i + counts i) / (∑ π_j + ∑ counts)` follows from the ratio
`seqProb (counts + e_i) / seqProb counts` via `Γ(z+1) = z · Γ(z)`. -/
noncomputable def predictive (u : PolyaUrn α) (counts : α → ℕ) (i : α) : ℝ :=
  (u.pseudo i + counts i) / (u.total + ∑ j, (counts j : ℝ))

omit [Nonempty α] in
/-- The Polya predictive at zero counts is `pseudo i / total` —
proportional to the pseudo-counts. -/
theorem predictive_zero (u : PolyaUrn α) (i : α) :
    u.predictive (fun _ => 0) i = u.pseudo i / u.total := by
  unfold predictive
  simp only [Nat.cast_zero, add_zero, Finset.sum_const_zero]

/-- For a symmetric urn, the predictive at zero counts is uniform `1/K`. -/
theorem predictive_zero_symmetric (c : ℝ) (hc : 0 < c) (i : α) :
    (symmetric (α := α) c hc).predictive (fun _ => 0) i =
      1 / (Fintype.card α : ℝ) := by
  rw [predictive_zero]
  simp only [symmetric, total]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Polya predictive monotonicity: a color with a higher previous count
gets higher predictive probability (the "rich get richer" /
preferential-attachment property). -/
theorem predictive_mono [DecidableEq α] (u : PolyaUrn α)
    (counts₁ counts₂ : α → ℕ) (i : α)
    (h_eq : ∀ j ≠ i, counts₁ j = counts₂ j)
    (h_le : counts₁ i ≤ counts₂ i) :
    u.predictive counts₁ i ≤ u.predictive counts₂ i := by
  unfold predictive
  set a₁ : ℝ := u.pseudo i + counts₁ i
  set S₁ : ℝ := ∑ j, (counts₁ j : ℝ)
  set S₂ : ℝ := ∑ j, (counts₂ j : ℝ)
  have hSnonneg : ∀ (counts : α → ℕ), 0 ≤ ∑ j, (counts j : ℝ) :=
    fun _ => Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hb₁_pos : 0 < u.total + S₁ := by linarith [u.total_pos, hSnonneg counts₁]
  have hδ : S₂ - S₁ = (counts₂ i : ℝ) - (counts₁ i : ℝ) := by
    simp only [S₁, S₂]
    rw [← Finset.sum_sub_distrib]
    have hpoint : ∀ j,
        ((counts₂ j : ℝ) - (counts₁ j : ℝ)) =
          if j = i then (counts₂ i : ℝ) - (counts₁ i : ℝ) else 0 := by
      intro j
      by_cases hji : j = i
      · rw [hji, if_pos rfl]
      · rw [if_neg hji, h_eq j hji, sub_self]
    rw [Finset.sum_congr rfl (fun j _ => hpoint j), Finset.sum_ite_eq' Finset.univ i]
    simp
  have hδ_nonneg : 0 ≤ (counts₂ i : ℝ) - (counts₁ i : ℝ) := by
    have : (counts₁ i : ℝ) ≤ counts₂ i := by exact_mod_cast h_le
    linarith
  have hcounts₁_le_sum : (counts₁ i : ℝ) ≤ S₁ := by
    simp only [S₁]
    exact Finset.single_le_sum (f := fun j => (counts₁ j : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ i)
  have hpseudo_le_total : u.pseudo i ≤ u.total := by
    simp only [total]
    exact Finset.single_le_sum (f := u.pseudo)
      (fun j _ => (u.pseudo_pos j).le) (Finset.mem_univ i)
  have h_a₁_le_b₁ : a₁ ≤ u.total + S₁ := by simp only [a₁]; linarith
  have h_a₂ : u.pseudo i + ↑(counts₂ i) =
      a₁ + ((counts₂ i : ℝ) - (counts₁ i : ℝ)) := by simp only [a₁]; ring
  have h_b₂ : u.total + S₂ = (u.total + S₁) + ((counts₂ i : ℝ) - (counts₁ i : ℝ)) := by
    have := hδ; linarith
  rw [h_a₂, h_b₂]
  set δ : ℝ := (counts₂ i : ℝ) - (counts₁ i : ℝ)
  have hb₁δ_pos : 0 < u.total + S₁ + δ := by linarith
  rw [div_le_div_iff₀ hb₁_pos hb₁δ_pos]
  nlinarith [h_a₁_le_b₁, hδ_nonneg]

end PolyaUrn

end ProbabilityTheory
