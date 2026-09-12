/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.InformationTheory.KullbackLeibler.Cond
import Linglib.Processing.Expectation.LanguageModel
import Linglib.Processing.Expectation.PrefixProbability

/-!
# Levy (2008): Expectation-Based Syntactic Comprehension

This file formalizes the resource-allocation theory of processing difficulty of [levy-2008].
A comprehender maintains a probability distribution over the complete structures consistent
with the input so far, the prior conditioned on consistency with the prefix (`posterior`),
and the difficulty of a word is the relative entropy of the updated distribution with respect
to the old one. Incremental update equals direct conditioning (`posterior_incremental`), and
the paper's central result is that the difficulty so defined is exactly the word's surprisal
(`klDiv_posterior_eq_surprisal`), [hale-2001]'s measure, for any generative process over
structures. Surprisal is therefore a causal bottleneck: processes agreeing on conditional
word probabilities incur identical difficulty whatever their structures (`bottleneck`), and
the difficulty may be read through any language model matching those probabilities
(`klDiv_posterior_eq_lm_surprisal`).

## Implementation notes

Structures live in an arbitrary discrete measurable space, covering the paper's normally
infinite structure set; the generative process is the prefix substrate's `PMF`, conditioned
as a measure, and the prefix apparatus (`consistent`, `prefixMass`, `nextProb`) is
`Processing.Expectation.PrefixProbability`. The prior is fixed throughout, matching the
paper's caveat that the equivalence holds only when extra-sentential context does not change
while the word is processed.

## References

* [levy-2008]
* [hale-2001]
-/

namespace Levy2008

open InformationTheory MeasureTheory ProbabilityTheory
open Processing.LanguageModel Processing.Expectation
open scoped ENNReal ProbabilityTheory

variable {T W : Type*} [MeasurableSpace T] [DiscreteMeasurableSpace T]

/-- `Pᵢ` (eq. (3)): the comprehender's distribution over complete structures
    given the prefix — the prior conditioned on consistency. -/
noncomputable def posterior (P : PMF T) (str : T → List W) (ws : List W) : Measure T :=
  P.toMeasure[|consistent str ws]

variable (P : PMF T) (str : T → List W) (ws : List W) (w : W)

/-- The prior's mass on the structures consistent with a prefix is the prefix
    probability. -/
theorem toMeasure_consistent : P.toMeasure (consistent str ws) = prefixMass P str ws :=
  P.toMeasure_apply .of_discrete

/-- Incremental update equals direct conditioning (eqs. (5)–(8)): conditioning
    the current posterior on consistency with the extended prefix is
    conditioning the prior on the extended prefix directly. -/
theorem posterior_incremental :
    (posterior P str ws)[|consistent str (ws ++ [w])] = posterior P str (ws ++ [w]) := by
  rw [posterior, posterior, cond_cond_eq_cond_inter .of_discrete .of_discrete,
    Set.inter_eq_right.mpr (consistent_anti str (List.prefix_append ws [w]))]

/-- The posterior's mass on the structures consistent with the next word is
    the induced conditional word probability. -/
theorem posterior_consistent_append :
    posterior P str ws (consistent str (ws ++ [w])) = nextProb P str ws w := by
  rw [posterior, cond_apply .of_discrete,
    Set.inter_eq_right.mpr (consistent_anti str (List.prefix_append ws [w])),
    toMeasure_consistent, toMeasure_consistent, nextProb, div_eq_mul_inv, mul_comm]

/-- The paper's eq. (4): the relative entropy of the updated distribution over
    structures with respect to the pre-update distribution is the surprisal of
    the word that triggered the update. -/
theorem klDiv_posterior_eq_surprisal (h : prefixMass P str (ws ++ [w]) ≠ 0) :
    klDiv (posterior P str (ws ++ [w])) (posterior P str ws)
      = ENNReal.ofReal (-Real.log (nextProb P str ws w).toReal) := by
  have hws : prefixMass P str ws ≠ 0 := λ h0 =>
    h (le_zero_iff.mp ((prefixMass_anti P str (List.prefix_append ws [w])).trans_eq h0))
  have : IsProbabilityMeasure (posterior P str ws) :=
    cond_isProbabilityMeasure ((toMeasure_consistent P str ws).trans_ne hws)
  rw [← posterior_incremental, klDiv_cond_self _ .of_discrete, posterior_consistent_append]
  rw [posterior_consistent_append, nextProb]
  exact ENNReal.div_ne_zero.mpr ⟨h, ne_top_of_le_ne_top ENNReal.one_ne_top
    ((prefixMass_anti P str (List.nil_prefix)).trans_eq (prefixMass_nil P str))⟩

/-- The update difficulty read through any language model that matches the
    process's conditional word probabilities is that model's surprisal. -/
theorem klDiv_posterior_eq_lm_surprisal (lm : LangModel W)
    (hlm : lm.nextProb ws w = nextProb P str ws w) (h : prefixMass P str (ws ++ [w]) ≠ 0) :
    klDiv (posterior P str (ws ++ [w])) (posterior P str ws)
      = ENNReal.ofReal (lm.surprisal ws w) := by
  rw [klDiv_posterior_eq_surprisal P str ws w h, LangModel.surprisal, hlm]

/-- The causal bottleneck (§2.3, Fig. 1b): two generative processes assigning
    the same conditional word probability incur the same update difficulty,
    regardless of their structural representations. -/
theorem bottleneck {T' : Type*} [MeasurableSpace T'] [DiscreteMeasurableSpace T']
    (P' : PMF T') (str' : T' → List W)
    (hagree : nextProb P str ws w = nextProb P' str' ws w)
    (h : prefixMass P str (ws ++ [w]) ≠ 0) (h' : prefixMass P' str' (ws ++ [w]) ≠ 0) :
    klDiv (posterior P str (ws ++ [w])) (posterior P str ws)
      = klDiv (posterior P' str' (ws ++ [w])) (posterior P' str' ws) := by
  rw [klDiv_posterior_eq_surprisal P str ws w h, klDiv_posterior_eq_surprisal P' str' ws w h',
    hagree]

end Levy2008
