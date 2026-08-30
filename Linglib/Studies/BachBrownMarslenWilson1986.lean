import Linglib.Features.VerbCluster
import Linglib.Data.Examples.BachBrownMarslenWilson1986
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Bach, Brown & Marslen-Wilson (1986): crossed vs nested dependencies

Standard Dutch orders clause-final verb clusters in crossed serial correspondence
with their argument NPs (NP₁ NP₂ NP₃ V₁ V₂ V₃); Standard German nests them
(NP₁ NP₂ NP₃ V₃ V₂ V₁). Three groups of 30 subjects (Dutch, German/Infinitive,
German/Participle) rated matched Test sentences and right-branching Paraphrase
controls for comprehensibility and answered probe questions about NP–verb
pairings. At one level of embedding the languages do not differ; from two levels
on, Dutch is reliably easier on both measures. Since a push-down store parses
nested but not crossed dependencies, the crossed pattern being *easier* rules
out the push-down stack as the universal basis of human parsing, confirming
[evers-1975]'s conjecture.

## The integration model

The paper argues informally that crossed orders let the hearer connect each NP
to the matrix structure as soon as its verb arrives, while nested orders keep
every NP unintegrated until the whole cluster has been heard. This file makes
that argument formal over the `Features.VerbClusterBinding` permutation: NP `i`
is matrix-integrated after `k` verbs iff every verb on the control chain from
its verb to the matrix verb has been heard (`integratedCount`); the cumulative
cost over a cluster of `n` verbs (`totalIntegrationCost`) is `n(n−1)/2` for the
crossed binding and `n(n−1)` for the nested one (`cost_gap`: the gap equals the
whole crossed cost). The gap is 1 at two verbs and grows quadratically —
matching the observed Level-2 parity and Level-3 divergence. The cost model is
this file's formalization of the paper's informal argument, not the paper's own
mathematics.

## Empirical results

Measured means stay in prose. Test-sentence comprehensibility (Table 1, 9-point
scale, 1 = easy) rises from 1.16 at Level 1 to 2.58, 5.80, 7.86 at Levels 2–4;
the Paraphrase controls rise only to 2.16, 4.01, 5.82, so the syntactic
Test−Paraphrase difference grows 0.42 → 1.78 → 2.04. German/Participle does not
differ from Dutch at Level 2 but does at Level 3 (F₂(1,17) = 3.705, p = 0.07);
German/Infinitive carries a baseline disadvantage at every level. Comprehension
accuracy (Table 3, max 2) at Level 3: Dutch 1.17 vs German 0.89 and 0.79. By NP
position (Tables 4–5), the middle NP2 is hardest for every group, and Dutch
shows zero Test−Paraphrase deficit on the most deeply embedded NP3 (the German
groups show 0.41 and 0.36): the Dutch hearer integrates NP3's late-arriving verb
into an already-built matrix structure, while for the German hearer V₃ arrives
first and its proposition floats unrooted until the cluster ends.

## References

* [bach-brown-marslen-wilson-1986]: Crossed and nested dependencies in German
  and Dutch: A psycholinguistic study. *Language and Cognitive Processes* 1.
* [evers-1975]: The transformational cycle in Dutch and German.
* [bresnan-etal-1982]: Cross-serial dependencies in Dutch.
-/

namespace BachBrownMarslenWilson1986

open Features (VerbClusterBinding)
open Features.VerbClusterBinding (identity reverse isProjective identity_not_projective
  reverse_is_projective)

variable {n : ℕ}

/-! ### The incremental integration model -/

/-- NPs matrix-integrated after `k` verbs heard: NP `i` counts iff every verb on
the control chain from its verb `V_{σ i}` up to the matrix verb `V_{σ 0}` has
been heard, i.e. `max (σ 0) (σ i) < k`. For the crossed binding this is
`min k n`; for the nested one it is `0` until the whole cluster is heard. -/
def integratedCount (σ : VerbClusterBinding n) (k : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | m + 1 =>
    let matrix := (σ ⟨0, by omega⟩).val
    (List.range (m + 1)).countP λ i =>
      if hi : i < m + 1 then
        Nat.max matrix (σ ⟨i, hi⟩).val < k
      else false

/-- NPs still awaiting matrix-connected integration after `k` verbs. -/
def unintegratedCount (σ : VerbClusterBinding n) (k : ℕ) : ℕ :=
  n - integratedCount σ k

private theorem countP_dite_lt_range (n k : ℕ) :
    (List.range n).countP (λ i => if _ : i < n then decide (i < k) else false) = min k n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, List.countP_cons, List.countP_nil]
    simp only [show m < m + 1 from by omega, dite_true]
    have : (List.range m).countP (λ i => if _ : i < m + 1 then decide (i < k) else false) =
           (List.range m).countP (λ i => if _ : i < m then decide (i < k) else false) := by
      apply List.countP_congr; intro i hi; simp only [List.mem_range] at hi
      simp [show i < m from hi, show i < m + 1 from by omega]
    rw [this, ih]; by_cases h : m < k <;> simp [h] <;> omega

/-- Crossed integration: `min k n` NPs are integrated after `k` verbs. -/
theorem identity_integratedCount (k : ℕ) :
    integratedCount (identity n) k = min k n := by
  cases n with
  | zero => simp [integratedCount]
  | succ m => simp only [integratedCount, identity, Equiv.refl_apply, Fin.val_mk]
              exact countP_dite_lt_range (m + 1) k

private theorem reverse_max_eq (m i : ℕ) (hi : i < m + 1) :
    Nat.max (m + 1 - 1 - 0) (m + 1 - 1 - i) = m := by
  simp only [Nat.add_sub_cancel, Nat.sub_zero]
  exact Nat.max_eq_left (by omega)

/-- Nested integration: nothing integrates until all `n` verbs are heard. -/
theorem reverse_integratedCount (k : ℕ) :
    integratedCount (reverse n) k = if k ≥ n then n else 0 := by
  cases n with
  | zero => simp [integratedCount]
  | succ m =>
    simp only [integratedCount, Features.VerbClusterBinding.reverse, Equiv.coe_fn_mk, Fin.val_mk]
    by_cases hk : k ≥ m + 1
    · rw [if_pos hk]
      have hall : ∀ i ∈ List.range (m + 1),
          (if _ : i < m + 1 then
            decide (Nat.max (m + 1 - 1 - 0) (m + 1 - 1 - i) < k) else false) = true := by
        intro i hi; simp only [List.mem_range] at hi
        simp only [show i < m + 1 from hi, dite_true, decide_eq_true_eq]
        rw [reverse_max_eq m i hi]; omega
      have h := List.countP_eq_length.mpr hall
      rw [List.length_range] at h; exact h
    · rw [if_neg hk]
      apply List.countP_eq_zero.mpr
      intro i hi; simp only [List.mem_range] at hi
      simp only [show i < m + 1 from hi, dite_true, decide_eq_true_eq]
      rw [reverse_max_eq m i hi]; omega

theorem identity_unintegratedCount (k : ℕ) :
    unintegratedCount (identity n) k = n - min k n := by
  simp [unintegratedCount, identity_integratedCount]

theorem reverse_unintegratedCount (k : ℕ) :
    unintegratedCount (reverse n) k = if k ≥ n then 0 else n := by
  simp only [unintegratedCount, reverse_integratedCount]; split <;> omega

/-! ### Cumulative cost and its closed forms -/

/-- Cumulative unintegrated NPs across the cluster: after each verb `k + 1`,
how many NPs still float without a matrix connection. -/
def totalIntegrationCost (σ : VerbClusterBinding n) : ℕ :=
  ∑ k ∈ Finset.range n, unintegratedCount σ (k + 1)

/-- The crossed (Dutch) cluster costs `n(n−1)/2`: one NP integrates per verb. -/
theorem totalIntegrationCost_identity (n : ℕ) :
    totalIntegrationCost (identity n) = n * (n - 1) / 2 := by
  unfold totalIntegrationCost
  have h : ∀ k ∈ Finset.range n, unintegratedCount (identity n) (k + 1) = n - 1 - k := by
    intro k hk
    have hkn := Finset.mem_range.mp hk
    rw [identity_unintegratedCount, Nat.min_eq_left (by omega)]
    omega
  rw [Finset.sum_congr rfl h, Finset.sum_range_reflect (λ j => j) n]
  have h2 := Finset.sum_range_id_mul_two n
  omega

/-- The nested (German) cluster costs `n(n−1)`: all `n` NPs float until the
last verb. -/
theorem totalIntegrationCost_reverse (n : ℕ) :
    totalIntegrationCost (reverse n) = n * (n - 1) := by
  unfold totalIntegrationCost
  cases n with
  | zero => simp
  | succ m =>
    have h : ∀ k ∈ Finset.range m, unintegratedCount (reverse (m + 1)) (k + 1) = m + 1 := by
      intro k hk
      have hkm := Finset.mem_range.mp hk
      rw [reverse_unintegratedCount, if_neg (by omega)]
    rw [Finset.sum_range_succ, Finset.sum_const_nat h, Finset.card_range,
        reverse_unintegratedCount, if_pos (by omega)]
    have := Nat.mul_comm m (m + 1)
    simp only [Nat.add_sub_cancel]
    omega

/-- Nested costs exactly twice crossed, at every cluster size. -/
theorem reverse_eq_two_mul_identity (n : ℕ) :
    totalIntegrationCost (reverse n) = 2 * totalIntegrationCost (identity n) := by
  rw [totalIntegrationCost_identity, totalIntegrationCost_reverse]
  have h2 := Finset.sum_range_id_mul_two n
  omega

/-- Crossed is strictly cheaper as soon as the cluster has two verbs. -/
theorem crossed_lt_nested (hn : 2 ≤ n) :
    totalIntegrationCost (identity n) < totalIntegrationCost (reverse n) := by
  rw [totalIntegrationCost_identity, totalIntegrationCost_reverse]
  have h : 0 < n * (n - 1) := Nat.mul_pos (by omega) (by omega)
  omega

/-- The absolute gap equals the whole crossed cost `n(n−1)/2` — 1 at two verbs
(where the experiment finds no Dutch–German difference), 3 at three, 6 at four
(where the Dutch advantage is large). -/
theorem cost_gap (n : ℕ) :
    totalIntegrationCost (reverse n) - totalIntegrationCost (identity n) =
      totalIntegrationCost (identity n) := by
  rw [reverse_eq_two_mul_identity]; omega

/-- The experiment's Levels 2–4 (clusters of 2–4 verbs), instantiating the
closed forms: crossed costs 1, 3, 6; nested costs 2, 6, 12. -/
theorem level_costs :
    (totalIntegrationCost (identity 2), totalIntegrationCost (identity 3),
      totalIntegrationCost (identity 4)) = (1, 3, 6) ∧
    (totalIntegrationCost (reverse 2), totalIntegrationCost (reverse 3),
      totalIntegrationCost (reverse 4)) = (2, 6, 12) := by
  simp [totalIntegrationCost_identity, totalIntegrationCost_reverse]

/-! ### The stack argument -/

/-- The formal side of the paper's argument against the push-down store: the
nested (German) binding is projective — the pattern a push-down store can parse
— while the crossed (Dutch) binding is not ([bresnan-etal-1982]). The
processing facts run the other way: the non-projective pattern is the cheap
one, so parsing difficulty does not track stack-parsability. -/
theorem nonprojective_is_cheaper (hn : 2 ≤ n) :
    isProjective (identity n) = false ∧ isProjective (reverse n) = true ∧
    totalIntegrationCost (identity n) < totalIntegrationCost (reverse n) :=
  ⟨identity_not_projective hn, reverse_is_projective, crossed_lt_nested hn⟩

end BachBrownMarslenWilson1986
