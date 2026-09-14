/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Data.List.Infix
import Mathlib.Probability.ConditionalProbability

/-!
# Prefix probabilities of a generative process

A generative process is a probability measure over complete structures together with their
yields, and it induces probabilities on strings: the prefix probability of a string is the mass
of the structures whose yield extends it ([stolcke-1995]'s prefix probability, computed there by
Earley parsing), and the conditional probability of the next word is the process conditioned on
the prefix, at the structures consistent with the extended prefix. This is the shared input of
surprisal theory: [hale-2001] defines word difficulty as the log-ratio of successive prefix
probabilities, and [levy-2008] proves that ratio equals the relative entropy of the induced
belief update.

## Main definitions

* `consistent`: the structures whose yield extends a prefix.
* `nextProb`: the induced conditional probability of the next word.

## References

* [stolcke-1995]
* [hale-2001]
* [levy-2008]
-/

namespace Processing.Expectation

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

variable {T W : Type*}

/-- The complete structures whose yield extends the prefix `ws`. -/
def consistent (str : T → List W) (ws : List W) : Set T := {t | ws <+: str t}

@[simp] theorem consistent_nil (str : T → List W) : consistent str [] = Set.univ :=
  Set.eq_univ_of_forall λ _ => List.nil_prefix

/-- Longer prefixes select fewer structures. -/
theorem consistent_anti (str : T → List W) {ws ws' : List W} (h : ws <+: ws') :
    consistent str ws' ⊆ consistent str ws :=
  λ _ ht => h.trans ht

variable [MeasurableSpace T] (P : Measure T) (str : T → List W)

theorem measurableSet_consistent [DiscreteMeasurableSpace T] (ws : List W) :
    MeasurableSet (consistent str ws) :=
  .of_discrete

/-- The conditional probability of the next word `w` after the prefix `ws` under the process
`P`: the process conditioned on the prefix, at the structures consistent with the extended
prefix. -/
noncomputable def nextProb (ws : List W) (w : W) : ℝ≥0∞ :=
  P[consistent str (ws ++ [w]) | consistent str ws]

/-- The next-word probability as a ratio of prefix probabilities. -/
theorem nextProb_eq_div [DiscreteMeasurableSpace T] (ws : List W) (w : W) :
    nextProb P str ws w = P (consistent str (ws ++ [w])) / P (consistent str ws) := by
  rw [nextProb, cond_apply (measurableSet_consistent str ws),
    Set.inter_eq_right.mpr (consistent_anti str (List.prefix_append ws [w])), div_eq_mul_inv,
    mul_comm]

end Processing.Expectation
