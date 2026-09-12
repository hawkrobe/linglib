import Linglib.Core.Computability.ContextFreeGrammar.Probabilistic
import Linglib.Core.Probability.PolyaUrn
import Mathlib.Data.ENNReal.BigOperators

/-!
# Dirichlet priors on probabilistic context-free grammars

A Dirichlet PCFG over `G` is a Dirichlet prior on the rule distribution at each nonterminal,
given by a positive pseudo-count for every rule. Integrating the rule weights out, the
probability of a corpus is a product over nonterminals of Pólya-urn likelihoods of the corpus
rule counts, so derivation trees are exchangeable but not independent: the corpus probability
does not factorise over sub-corpora as `PCFG.corpusProb` does. The posterior given a corpus is
again a Dirichlet PCFG, with pseudo-counts raised by the corpus rule counts, and the posterior
predictive rule distribution is the PCFG of normalised posterior pseudo-counts.

## Main definitions

* `DirichletPCFG G`: positive pseudo-counts on the rules of `G`.
* `DirichletPCFG.lhsUrn`, `DirichletPCFG.lhsFactor`, `DirichletPCFG.corpusProb`: the Pólya urn
  at a nonterminal, its likelihood of the corpus counts there, and the corpus probability.
* `DirichletPCFG.posterior`: the conjugate update by a corpus.
* `DirichletPCFG.predictive`, `DirichletPCFG.predictivePCFG`: the posterior predictive
  probability of a rule, as a real and as a PCFG.
* `DirichletPCFG.posteriorMode`: the mode of the posterior Dirichlet, defined in the interior of
  the simplex.

## Main results

* `DirichletPCFG.predictive_lt_iff_of_same_lhs`, `DirichletPCFG.posteriorMode_lt_iff_of_same_lhs`:
  at a shared nonterminal both estimators order rules by posterior pseudo-count, so they agree
  (`DirichletPCFG.predictive_lt_iff_posteriorMode_lt`).
* `DirichletPCFG.predictivePCFG_posterior`: the posterior predictive PCFG of a corpus is the prior
  predictive PCFG of the posterior.

## References

* [johnson-griffiths-goldwater-2007]
* [kurihara-sato-2006]
-/

open Real ProbabilityTheory

/-- A Dirichlet prior on the rule distributions of `G`: a positive pseudo-count for every rule
of the grammar. -/
@[ext]
structure DirichletPCFG {T : Type*} [DecidableEq T] (G : ContextFreeGrammar T)
    [DecidableEq G.NT] where
  /-- The Dirichlet pseudo-count of a rule. -/
  pseudo : ContextFreeRule T G.NT → ℝ
  /-- Pseudo-counts are positive on the rules of the grammar. -/
  pseudo_pos : ∀ r ∈ G.rules, 0 < pseudo r

namespace DirichletPCFG

variable {T : Type*} [DecidableEq T] {G : ContextFreeGrammar T} [DecidableEq G.NT]

open DerivationTree (corpusRuleCount corpusRuleCount_zero corpusRuleCount_add)

variable (M : DirichletPCFG G)

/-- The Pólya urn over the rules with left-hand side `a`, with `M`'s pseudo-counts. -/
noncomputable def lhsUrn (a : G.NT) : PolyaUrn (G.RulesWithLHS a) where
  pseudo := λ ⟨r, _⟩ => M.pseudo r
  pseudo_pos := λ ⟨r, hr⟩ => M.pseudo_pos r (Finset.mem_filter.mp hr).1

/-- The corpus counts of the rules with left-hand side `a`. -/
def lhsCounts (a : G.NT) (D : Multiset (DerivationTree T G.NT)) : G.RulesWithLHS a → ℕ :=
  λ ⟨r, _⟩ => corpusRuleCount r D

/-- The Pólya-urn likelihood of the corpus counts at nonterminal `a`. -/
noncomputable def lhsFactor (a : G.NT) (D : Multiset (DerivationTree T G.NT)) : ℝ :=
  (M.lhsUrn a).seqProb (lhsCounts a D)

/-- The probability of a corpus with the rule weights integrated out: the product over the
nonterminals the grammar expands of the Pólya-urn likelihood there. -/
noncomputable def corpusProb (D : Multiset (DerivationTree T G.NT)) : ℝ :=
  ∏ a ∈ G.rules.image (·.input), M.lhsFactor a D

omit [DecidableEq T] in
theorem nonempty_rulesWithLHS_of_mem_image {a : G.NT} (ha : a ∈ G.rules.image (·.input)) :
    Nonempty (G.RulesWithLHS a) :=
  let ⟨r, hr, hra⟩ := Finset.mem_image.mp ha
  ⟨r, Finset.mem_filter.mpr ⟨hr, hra⟩⟩

theorem lhsFactor_pos {a : G.NT} (ha : a ∈ G.rules.image (·.input))
    (D : Multiset (DerivationTree T G.NT)) : 0 < M.lhsFactor a D :=
  have := nonempty_rulesWithLHS_of_mem_image ha
  (M.lhsUrn a).seqProb_pos _

theorem corpusProb_nonneg (D : Multiset (DerivationTree T G.NT)) : 0 ≤ M.corpusProb D :=
  Finset.prod_nonneg λ _ ha => (M.lhsFactor_pos ha D).le

@[simp]
theorem lhsCounts_zero (a : G.NT) : lhsCounts (G := G) a 0 = λ _ => 0 := by
  funext ⟨r, _⟩
  simp [lhsCounts]

@[simp]
theorem lhsFactor_zero (a : G.NT) [Nonempty (G.RulesWithLHS a)] : M.lhsFactor a 0 = 1 := by
  rw [lhsFactor, lhsCounts_zero]
  exact (M.lhsUrn a).seqProb_zero

@[simp]
theorem corpusProb_zero : M.corpusProb 0 = 1 :=
  Finset.prod_eq_one λ _ ha =>
    have := nonempty_rulesWithLHS_of_mem_image ha
    M.lhsFactor_zero _

/-! ### Conjugate update -/

/-- The posterior given a corpus: each rule's pseudo-count grows by its corpus count. -/
noncomputable def posterior (D : Multiset (DerivationTree T G.NT)) : DirichletPCFG G where
  pseudo r := M.pseudo r + corpusRuleCount r D
  pseudo_pos r hr := add_pos_of_pos_of_nonneg (M.pseudo_pos r hr) (Nat.cast_nonneg _)

@[simp]
theorem posterior_zero : M.posterior 0 = M := by
  ext r
  simp [posterior]

theorem posterior_add (D₁ D₂ : Multiset (DerivationTree T G.NT)) :
    M.posterior (D₁ + D₂) = (M.posterior D₁).posterior D₂ := by
  ext r
  simp [posterior, corpusRuleCount_add, add_assoc]

/-! ### Posterior predictive rule distribution -/

/-- The posterior predictive probability of rule `r` at its left-hand side given a corpus, the
posterior mean of its weight: its posterior pseudo-count over the total at that nonterminal. -/
noncomputable def predictive (r : ContextFreeRule T G.NT) (D : Multiset (DerivationTree T G.NT)) :
    ℝ :=
  (M.pseudo r + corpusRuleCount r D) /
    ∑ r' ∈ G.rules.filter (·.input = r.input), (M.pseudo r' + corpusRuleCount r' D)

theorem predictive_denom_pos {a : G.NT} [hne : Nonempty (G.RulesWithLHS a)]
    (D : Multiset (DerivationTree T G.NT)) :
    0 < ∑ r' ∈ G.rules.filter (·.input = a), (M.pseudo r' + (corpusRuleCount r' D : ℝ)) := by
  obtain ⟨⟨r₀, hr₀⟩⟩ := hne
  have hpos : ∀ r' ∈ G.rules.filter (·.input = a), 0 < M.pseudo r' + (corpusRuleCount r' D : ℝ) :=
    λ r' hr' => add_pos_of_pos_of_nonneg (M.pseudo_pos r' (Finset.mem_filter.mp hr').1)
      (Nat.cast_nonneg _)
  exact Finset.sum_pos' (λ r' hr' => (hpos r' hr').le) ⟨r₀, hr₀, hpos r₀ hr₀⟩

theorem predictive_pos {r : ContextFreeRule T G.NT} (hr : r ∈ G.rules)
    (D : Multiset (DerivationTree T G.NT)) : 0 < M.predictive r D :=
  have : Nonempty (G.RulesWithLHS r.input) := ⟨⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩⟩⟩
  div_pos (add_pos_of_pos_of_nonneg (M.pseudo_pos r hr) (Nat.cast_nonneg _))
    (M.predictive_denom_pos D)

theorem predictive_nonneg {r : ContextFreeRule T G.NT} (hr : r ∈ G.rules)
    (D : Multiset (DerivationTree T G.NT)) : 0 ≤ M.predictive r D :=
  (M.predictive_pos hr D).le

/-- With no data the predictive probability is the normalised prior pseudo-count. -/
@[simp]
theorem predictive_zero (r : ContextFreeRule T G.NT) :
    M.predictive r 0 = M.pseudo r / ∑ r' ∈ G.rules.filter (·.input = r.input), M.pseudo r' := by
  simp [predictive]

/-- At a shared left-hand side, predictive probabilities order rules by posterior pseudo-count. -/
theorem predictive_lt_iff_of_same_lhs {r r' : ContextFreeRule T G.NT} (hr' : r' ∈ G.rules)
    (h : r.input = r'.input) {D : Multiset (DerivationTree T G.NT)} :
    M.predictive r D < M.predictive r' D ↔
      M.pseudo r + corpusRuleCount r D < M.pseudo r' + corpusRuleCount r' D := by
  have : Nonempty (G.RulesWithLHS r'.input) := ⟨⟨r', Finset.mem_filter.mpr ⟨hr', rfl⟩⟩⟩
  unfold predictive
  rw [h]
  exact div_lt_div_iff_of_pos_right (M.predictive_denom_pos D)

theorem sum_predictive_eq_one {a : G.NT} [Nonempty (G.RulesWithLHS a)]
    (D : Multiset (DerivationTree T G.NT)) :
    ∑ r ∈ G.rules.filter (·.input = a), M.predictive r D = 1 := by
  rw [Finset.sum_congr rfl λ r hr => by
        rw [predictive, (Finset.mem_filter.mp hr).2], ← Finset.sum_div]
  exact div_self (M.predictive_denom_pos D).ne'

/-- The posterior predictive PCFG: the predictive probability of each rule of the grammar. -/
noncomputable def predictivePCFG (D : Multiset (DerivationTree T G.NT)) : PCFG G where
  weight r := if r ∈ G.rules then ENNReal.ofReal (M.predictive r D) else 0
  weight_nonneg _ := zero_le
  weight_eq_zero_of_not_mem _ hr := if_neg hr
  sum_weight a ha := by
    have := nonempty_rulesWithLHS_of_mem_image ha
    rw [Finset.sum_congr rfl λ r hr => if_pos (Finset.mem_filter.mp hr).1,
      ← ENNReal.ofReal_sum_of_nonneg λ r hr => M.predictive_nonneg (Finset.mem_filter.mp hr).1 D,
      M.sum_predictive_eq_one D, ENNReal.ofReal_one]

theorem predictivePCFG_weight {r : ContextFreeRule T G.NT} (hr : r ∈ G.rules)
    (D : Multiset (DerivationTree T G.NT)) :
    (M.predictivePCFG D).weight r = ENNReal.ofReal (M.predictive r D) :=
  if_pos hr

/-- Conditioning on a corpus and then taking the prior predictive is taking the posterior
predictive. -/
theorem predictivePCFG_posterior (D : Multiset (DerivationTree T G.NT)) :
    (M.posterior D).predictivePCFG 0 = M.predictivePCFG D := by
  ext r
  simp [predictivePCFG, predictive, posterior]

/-! ### Posterior mode

The mode of the posterior Dirichlet at a nonterminal lies in the interior of the simplex when
every posterior pseudo-count there exceeds `1`, and is then `(π_r + x_r - 1) / ∑ (π_r' + x_r' - 1)`.
Where it is defined it orders rules exactly as the predictive probability does. -/

/-- The mode of the posterior Dirichlet weight of rule `r`, `0` by the division convention
outside the interior regime `M.PosteriorModeInterior r.input D`. -/
noncomputable def posteriorMode (r : ContextFreeRule T G.NT)
    (D : Multiset (DerivationTree T G.NT)) : ℝ :=
  (M.pseudo r + corpusRuleCount r D - 1) /
    ∑ r' ∈ G.rules.filter (·.input = r.input), (M.pseudo r' + corpusRuleCount r' D - 1)

/-- The posterior mode at nonterminal `a` lies in the interior of the simplex: every posterior
pseudo-count there exceeds `1`. -/
def PosteriorModeInterior (a : G.NT) (D : Multiset (DerivationTree T G.NT)) : Prop :=
  ∀ r ∈ G.rules.filter (·.input = a), 1 < M.pseudo r + corpusRuleCount r D

theorem posteriorMode_denom_pos {a : G.NT} [hne : Nonempty (G.RulesWithLHS a)]
    (D : Multiset (DerivationTree T G.NT)) (h : M.PosteriorModeInterior a D) :
    0 < ∑ r' ∈ G.rules.filter (·.input = a), (M.pseudo r' + (corpusRuleCount r' D : ℝ) - 1) := by
  obtain ⟨⟨r₀, hr₀⟩⟩ := hne
  exact Finset.sum_pos' (λ r' hr' => by linarith [h r' hr']) ⟨r₀, hr₀, by linarith [h r₀ hr₀]⟩

theorem posteriorMode_pos {r : ContextFreeRule T G.NT} (hr : r ∈ G.rules)
    (D : Multiset (DerivationTree T G.NT)) (h : M.PosteriorModeInterior r.input D) :
    0 < M.posteriorMode r D :=
  have : Nonempty (G.RulesWithLHS r.input) := ⟨⟨r, Finset.mem_filter.mpr ⟨hr, rfl⟩⟩⟩
  div_pos (by linarith [h r (Finset.mem_filter.mpr ⟨hr, rfl⟩)]) (M.posteriorMode_denom_pos D h)

theorem posteriorMode_lt_iff_of_same_lhs {r r' : ContextFreeRule T G.NT} (hr' : r' ∈ G.rules)
    (h : r.input = r'.input) {D : Multiset (DerivationTree T G.NT)}
    (hint : M.PosteriorModeInterior r'.input D) :
    M.posteriorMode r D < M.posteriorMode r' D ↔
      M.pseudo r + corpusRuleCount r D < M.pseudo r' + corpusRuleCount r' D := by
  have : Nonempty (G.RulesWithLHS r'.input) := ⟨⟨r', Finset.mem_filter.mpr ⟨hr', rfl⟩⟩⟩
  unfold posteriorMode
  rw [h, div_lt_div_iff_of_pos_right (M.posteriorMode_denom_pos D hint)]
  exact ⟨λ h => by linarith, λ h => by linarith⟩

/-- Where the posterior mode is defined, it orders rules at a shared left-hand side exactly as
the predictive probability does. -/
theorem predictive_lt_iff_posteriorMode_lt {r r' : ContextFreeRule T G.NT} (hr' : r' ∈ G.rules)
    (h : r.input = r'.input) {D : Multiset (DerivationTree T G.NT)}
    (hint : M.PosteriorModeInterior r'.input D) :
    M.predictive r D < M.predictive r' D ↔ M.posteriorMode r D < M.posteriorMode r' D := by
  rw [M.predictive_lt_iff_of_same_lhs hr' h, M.posteriorMode_lt_iff_of_same_lhs hr' h hint]

end DirichletPCFG
