/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.MeasureTheory.Constructions.Option
public import Mathlib.Data.List.Infix
public import Mathlib.Probability.ConditionalProbability

/-!
# Prefix probabilities of a generative process

A generative process is a probability measure over complete structures together with their
yields, and it induces probabilities on strings: the prefix probability of a string is the mass
of the structures whose yield extends it ([stolcke-1995]'s prefix probability, computed there by
Earley parsing), and the conditional probability of the next word is the process conditioned on
the prefix, at the structures consistent with the extended prefix. The law of the next word
reads the conditioned process at the position after the prefix, with `none` where the yield
ends there, and a word's surprisal is its surprisal under this law. This is the shared input of
surprisal theory: [hale-2001] defines word difficulty as the log-ratio of successive prefix
probabilities, and [levy-2008] proves that ratio equals the relative entropy of the induced
belief update.

## Main definitions

* `consistent`: the structures whose yield extends a prefix.
* `nextProb`: the induced conditional probability of the next word.
* `nextWord`: the law of the next word, `none` for the end of the yield.

## Main results

* `nextProb_eq_div`: the next-word probability as a ratio of prefix probabilities.
* `nextWord_singleton_some`, `nextWord_singleton_none`: the law of the next word gives each word
  its conditional probability and the end the probability that the yield is the prefix.
* `cond_consistent_append`: the chain rule for conditional prefix probabilities.

## References

* [stolcke-1995]
* [hale-2001]
* [levy-2008]
-/

@[expose] public section

namespace Surprisal

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

variable {T W : Type*}

/-- The complete structures whose yield extends the prefix `ws`. -/
def consistent (str : T → List W) (ws : List W) : Set T := {t | ws <+: str t}

@[simp] theorem consistent_nil (str : T → List W) : consistent str [] = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ List.nil_prefix

/-- Longer prefixes select fewer structures. -/
theorem consistent_anti (str : T → List W) {ws ws' : List W} (h : ws <+: ws') :
    consistent str ws' ⊆ consistent str ws :=
  fun _ ht ↦ h.trans ht

/-- A list extends `ws ++ [w]` exactly when it extends `ws` and has `w` right after it. -/
private theorem append_singleton_prefix_iff {ws l : List W} {w : W} :
    ws ++ [w] <+: l ↔ ws <+: l ∧ l[ws.length]? = some w := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨(List.prefix_append ws [w]).trans (List.prefix_append _ r), by simp⟩
  · rintro ⟨⟨r, rfl⟩, h⟩
    cases r with
    | nil => simp at h
    | cons x r => simp at h; subst h; exact ⟨r, by simp⟩

/-- A list extending `ws` ends there exactly when it has nothing after it. -/
private theorem getElem?_length_eq_none_iff {ws l : List W} (h : ws <+: l) :
    l[ws.length]? = none ↔ l = ws := by
  rw [List.getElem?_eq_none_iff]
  exact ⟨fun hl ↦ (h.eq_of_length (le_antisymm h.length_le hl)).symm, fun hl ↦ hl ▸ le_rfl⟩

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

/-- The chain rule: the probability of extending a prefix by `xs ++ ys` is the probability of
extending it by `xs` times the probability of then extending by `ys`. -/
theorem cond_consistent_append [DiscreteMeasurableSpace T] [IsFiniteMeasure P] (ws xs ys : List W) :
    P[consistent str (ws ++ xs ++ ys) | consistent str ws] =
      P[consistent str (ws ++ xs) | consistent str ws] *
        P[consistent str (ws ++ xs ++ ys) | consistent str (ws ++ xs)] := by
  have hB := consistent_anti str (List.prefix_append ws xs)
  have hA := consistent_anti str (List.prefix_append (ws ++ xs) ys)
  simp only [cond_apply (measurableSet_consistent str _), Set.inter_eq_right.mpr hA,
    Set.inter_eq_right.mpr hB, Set.inter_eq_right.mpr (hA.trans hB)]
  by_cases h0 : P (consistent str (ws ++ xs)) = 0
  · rw [h0, measure_mono_null hA h0]; simp
  · rw [mul_assoc, ← mul_assoc (P _), ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]

/-- The law of what follows the prefix `ws`: the process conditioned on the prefix, read at the
position after it, with `none` where the yield ends. -/
noncomputable def nextWord [MeasurableSpace W] (ws : List W) : Measure (Option W) :=
  (P[|consistent str ws]).map fun t ↦ (str t)[ws.length]?

variable [MeasurableSpace W] [DiscreteMeasurableSpace T] [MeasurableSingletonClass W]

/-- The law of the next word gives a word its conditional probability. -/
theorem nextWord_singleton_some (ws : List W) (w : W) :
    nextWord P str ws {some w} = nextProb P str ws w := by
  rw [nextWord, Measure.map_apply .of_discrete (measurableSet_singleton _), nextProb,
    cond_apply (measurableSet_consistent str ws), cond_apply (measurableSet_consistent str ws)]
  congr 2
  ext t
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, consistent,
    Set.mem_ofPred_eq, append_singleton_prefix_iff]
  exact ⟨fun h ↦ ⟨h.1, h⟩, fun h ↦ h.2⟩

/-- The law of the next word gives the end of the yield the probability that the yield is the
prefix. -/
theorem nextWord_singleton_none (ws : List W) :
    nextWord P str ws {none} = P[{t | str t = ws} | consistent str ws] := by
  rw [nextWord, Measure.map_apply .of_discrete (measurableSet_singleton _),
    cond_apply (measurableSet_consistent str ws), cond_apply (measurableSet_consistent str ws)]
  congr 2
  ext t
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, consistent,
    Set.mem_ofPred_eq]
  exact and_congr_right getElem?_length_eq_none_iff

end Surprisal
