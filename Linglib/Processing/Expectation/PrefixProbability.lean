/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.List.Infix

/-!
# Prefix probabilities of a generative process

A generative process — a distribution `P : PMF T` over complete structures
together with their yields `str : T → List W` — induces probabilities on
strings: `prefixMass` is the total mass of the structures whose yield extends
a given prefix ([stolcke-1995]'s prefix probability, computed there by Earley
parsing), and `nextProb` the conditional word probability it induces. This is
the shared input type of surprisal theory: [hale-2001] defines word difficulty
as the log-ratio of successive prefix probabilities, and [levy-2008] proves
that ratio equals the relative entropy of the induced belief update
(`Studies/Hale2001.lean`, `Studies/Levy2008.lean`).

## Main definitions

* `consistent` — the structures whose yield extends a prefix.
* `prefixMass` — the prefix probability.
* `nextProb` — the induced conditional word probability.

## Main results

* `consistent_anti`, `prefixMass_anti` — longer prefixes select fewer
  structures and less mass.
* `prefixMass_nil` — the empty prefix has mass one.
-/

namespace Processing.Expectation

open scoped ENNReal

variable {T W : Type*}

/-- The complete structures whose yield extends the prefix `ws`. -/
def consistent (str : T → List W) (ws : List W) : Set T := {t | ws <+: str t}

/-- Longer prefixes select fewer structures. -/
theorem consistent_anti (str : T → List W) {ws ws' : List W} (h : ws <+: ws') :
    consistent str ws' ⊆ consistent str ws :=
  fun _ ht => h.trans ht

/-- The prefix probability: total mass of the structures whose yield extends
    the prefix. -/
noncomputable def prefixMass (P : PMF T) (str : T → List W) (ws : List W) : ℝ≥0∞ :=
  ∑' t, (consistent str ws).indicator P t

@[simp] theorem prefixMass_nil (P : PMF T) (str : T → List W) :
    prefixMass P str [] = 1 := by
  have huniv : consistent str [] = Set.univ :=
    Set.eq_univ_of_forall fun t => List.nil_prefix
  rw [prefixMass, huniv, Set.indicator_univ, P.tsum_coe]

/-- Longer prefixes carry less mass. -/
theorem prefixMass_anti (P : PMF T) (str : T → List W) {ws ws' : List W}
    (h : ws <+: ws') : prefixMass P str ws' ≤ prefixMass P str ws :=
  ENNReal.tsum_le_tsum fun t =>
    Set.indicator_le_indicator_of_subset (consistent_anti str h) (fun _ => zero_le) t

/-- The conditional probability of the next word induced by the generative
    process. -/
noncomputable def nextProb (P : PMF T) (str : T → List W) (ws : List W) (w : W) : ℝ≥0∞ :=
  prefixMass P str (ws ++ [w]) / prefixMass P str ws

end Processing.Expectation
