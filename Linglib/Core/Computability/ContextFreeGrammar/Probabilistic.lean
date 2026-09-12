import Linglib.Core.Computability.ContextFreeGrammar.Tree
import Linglib.Core.Computability.ContextFreeGrammar.Weighted
import Mathlib.Data.ENNReal.Inv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Probabilistic context-free grammars

A probabilistic context-free grammar (PCFG) over `G` is a weight on the rules of `G` that sums
to one over the rules expanding each nonterminal. The probability of a derivation tree is the
product of the weights of the rules it applies, and the probability of a corpus, a multiset of
derivation trees, is the product over its trees, so the corpus probability factorises over
disjoint sub-corpora. Over valid trees it also collects into a product over the grammar's rules
of the rule weight raised to the corpus count of that rule.

## Main definitions

* `PCFG G`: a `WeightedCFG G ℝ≥0∞` vanishing off the grammar and normalised at each nonterminal
  the grammar expands.
* `PCFG.derivProb`, `PCFG.corpusProb`: the probability of a derivation tree, a
  `RoseTree (Symbol T G.NT)`, and of a corpus.
* `PCFG.uniform`: the uniform rule distribution at every nonterminal.

## Main results

* `PCFG.corpusProb_add`: corpus probability is multiplicative over disjoint corpora.
* `PCFG.corpusProb_eq_prod_pow_count`: over valid trees, corpus probability is the product of
  rule weights raised to corpus rule counts.

## Implementation notes

Weights are `ℝ≥0∞`, the scalar of `MeasureTheory.Measure`, and a rule outside the grammar has
weight `0`, so a tree applying such a rule has probability `0`. Whether the tree probabilities
of a PCFG sum to one, tightness in the sense of [booth-thompson-1973] and [chi-1999], is not
addressed here: `derivProb` is a weight on trees, not yet a measure.

## References

* [booth-thompson-1973]
* [chi-1999]
-/

open scoped ENNReal

/-- A probabilistic context-free grammar over `G`: a rule weight vanishing off the grammar and
summing to one over the rules with each left-hand side the grammar expands. -/
@[ext]
structure PCFG {T : Type*} (G : ContextFreeGrammar T) [DecidableEq G.NT]
    extends WeightedCFG G ℝ≥0∞ where
  /-- Rules outside the grammar have weight `0`. -/
  weight_eq_zero_of_not_mem : ∀ r ∉ G.rules, weight r = 0
  /-- Weights sum to one over the rules with each left-hand side the grammar expands. -/
  sum_weight : ∀ a ∈ G.rules.image (·.input), ∑ r ∈ G.rules.filter (·.input = a), weight r = 1

namespace PCFG

variable {T : Type*} {G : ContextFreeGrammar T} [DecidableEq G.NT] (W : PCFG G)

attribute [simp] weight_eq_zero_of_not_mem

/-- The weight of a node from its symbol and the symbols of its children: the rule weight at a
nonterminal, `1` at a childless terminal and `0` at a terminal with children. -/
noncomputable def symbolWeight : Symbol T G.NT → List (Symbol T G.NT) → ℝ≥0∞
  | .nonterminal A, syms => W.weight ⟨A, syms⟩
  | .terminal _, [] => 1
  | .terminal _, _ :: _ => 0

@[simp] theorem symbolWeight_nonterminal (A : G.NT) (syms : List (Symbol T G.NT)) :
    W.symbolWeight (.nonterminal A) syms = W.weight ⟨A, syms⟩ := rfl

@[simp] theorem symbolWeight_terminal_nil (a : T) : W.symbolWeight (.terminal a) [] = 1 := rfl

@[simp] theorem symbolWeight_terminal_cons (a : T) (s : Symbol T G.NT)
    (syms : List (Symbol T G.NT)) : W.symbolWeight (.terminal a) (s :: syms) = 0 := rfl

/-- The probability of a derivation tree: the product over its nodes of the weight of the rule
applied there. -/
noncomputable def derivProb (t : RoseTree (Symbol T G.NT)) : ℝ≥0∞ :=
  (t.offspring.map fun p => W.symbolWeight p.1 p.2).prod

theorem derivProb_node (s : Symbol T G.NT) (cs : List (RoseTree (Symbol T G.NT))) :
    W.derivProb (RoseTree.node s cs) =
      W.symbolWeight s (cs.map RoseTree.value) * (cs.map W.derivProb).prod := by
  simp only [derivProb, RoseTree.offspring_node, List.map_cons, List.prod_cons, List.map_flatten,
    List.prod_flatten, List.map_map, Function.comp_def]
  rfl

/-- The probability of a corpus: the product of the probabilities of its derivation trees. -/
noncomputable def corpusProb (D : Multiset (RoseTree (Symbol T G.NT))) : ℝ≥0∞ :=
  (D.map W.derivProb).prod

@[simp]
theorem corpusProb_zero : W.corpusProb 0 = 1 := by
  simp [corpusProb]

/-- Corpus probability is multiplicative over disjoint corpora: derivation trees are independent
under a PCFG, in contrast to `DirichletPCFG.corpusProb`. -/
theorem corpusProb_add (D₁ D₂ : Multiset (RoseTree (Symbol T G.NT))) :
    W.corpusProb (D₁ + D₂) = W.corpusProb D₁ * W.corpusProb D₂ := by
  simp [corpusProb]

theorem sum_weight_le_one (A : G.NT) : ∑ r ∈ G.rules.filter (·.input = A), W.weight r ≤ 1 := by
  by_cases hA : A ∈ G.rules.image (·.input)
  · exact (W.sum_weight A hA).le
  · rw [Finset.sum_eq_zero fun r hr => (hA (Finset.mem_image.mpr
      ⟨r, (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2⟩)).elim]
    exact zero_le_one

section

variable [DecidableEq T]

/-- The probability of a valid derivation tree is the product over the grammar's rules of the
rule weight raised to the number of applications of that rule in the tree. -/
theorem derivProb_eq_prod_pow_ruleCount {t : RoseTree (Symbol T G.NT)} (ht : t.ValidFor G) :
    W.derivProb t = ∏ r ∈ G.rules, W.weight r ^ RoseTree.ruleCount r t := by
  induction ht with
  | terminal a => simp [RoseTree.leaf, derivProb_node, RoseTree.ruleCount_node_terminal]
  | nonterminal A cs hrule hcs ih =>
    simp only [derivProb_node, RoseTree.ruleCount_node_nonterminal, pow_add,
      Finset.prod_mul_distrib, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq', if_pos hrule,
      symbolWeight_nonterminal]
    congr 1
    clear hrule hcs
    induction cs with
    | nil => simp
    | cons c cs ihl =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add, Finset.prod_mul_distrib]
      rw [ih c (List.mem_cons_self ..), ihl λ c' hc' => ih c' (List.mem_cons_of_mem _ hc')]

/-- Over valid derivation trees, corpus probability is the product over the grammar's rules of
the rule weight raised to the corpus count of that rule. -/
theorem corpusProb_eq_prod_pow_count (D : Multiset (RoseTree (Symbol T G.NT)))
    (h : ∀ t ∈ D, t.ValidFor G) :
    W.corpusProb D = ∏ r ∈ G.rules, W.weight r ^ RoseTree.corpusRuleCount r D := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons t D ih =>
    rw [← Multiset.singleton_add, corpusProb_add,
      ih λ t' ht' => h t' (Multiset.mem_cons_of_mem ht')]
    simp only [corpusProb, Multiset.map_singleton, Multiset.prod_singleton,
      RoseTree.corpusRuleCount_add, pow_add, Finset.prod_mul_distrib,
      W.derivProb_eq_prod_pow_ruleCount (h t (Multiset.mem_cons_self t D)),
      RoseTree.corpusRuleCount_singleton]

/-- The uniform PCFG: at every nonterminal, the uniform distribution over its rules. -/
noncomputable def uniform : PCFG G where
  weight r := if r ∈ G.rules then ((G.rules.filter (·.input = r.input)).card : ℝ≥0∞)⁻¹ else 0
  weight_nonneg _ := zero_le
  weight_eq_zero_of_not_mem _ hr := if_neg hr
  sum_weight a ha := by
    obtain ⟨r₀, hr₀, hra⟩ := Finset.mem_image.mp ha
    have hcard :
        ((G.rules.filter λ r : ContextFreeRule T G.NT => r.input = a).card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨r₀, Finset.mem_filter.mpr ⟨hr₀, hra⟩⟩).ne'
    rw [Finset.sum_congr rfl
        (g := λ _ => ((G.rules.filter λ r : ContextFreeRule T G.NT => r.input = a).card : ℝ≥0∞)⁻¹)
        λ r hr => by rw [if_pos (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2],
      Finset.sum_const, nsmul_eq_mul, ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top _)]

noncomputable instance : Inhabited (PCFG G) := ⟨uniform⟩

end

end PCFG
