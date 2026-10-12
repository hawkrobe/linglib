/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.InformationTheory.Surprisal
public import Linglib.Processing.Surprisal.PrefixProbability

/-!
# Hale (2001): A Probabilistic Earley Parser as a Psycholinguistic Model

This file formalizes the linking hypothesis of [hale-2001]. Cognitive load is the total probability
of the structural analyses the input so far has disconfirmed (section 4): for a consistent grammar,
the effort spent on a prefix is one minus its prefix probability, `disconfirmed`, and word-by-word
reading time is proportional to the log of the ratio of the prefix probability before the word to
the one after it, the word's surprisal (`surprisal_nextWord_eq_log_div`), where the prefix
probability is [stolcke-1995]'s, computed by a probabilistic Earley parser that is
strong-competence, frequency-sensitive, and eager (Principles 1 to 3). The parser computes every
parse, so the theory is one of total parallelism (section 3): garden-pathing needs no reanalysis and
happens exactly at words where the disconfirmed analyses comprise most of the probability mass
(`log_le_surprisal_nextWord`), which is how the paper reads the spike at *fell* in *the horse raced
past the barn fell*, where grammar (1) puts the prefix probability before the word at more than ten
times the one after it (section 6.1), and the subject and object relative asymmetry of grammar (3)
(section 6.3). The two levels of the linking hypothesis agree, since prefix-level load only grows
along a sentence (`disconfirmed_mono`) and word-level surprisals telescope to the negative log of
the sentence's prefix mass (`totalSurprisal_nil_eq`).

## Implementation notes

The demonstrations' numerics, grammars (1) to (3) and the reading-time figures, require
Stolcke's Earley chart over recursive probabilistic context-free grammars and await an Earley
substrate; the theorems here are the grammar-independent content of the linking hypothesis,
stated for any probability measure over structures with string yields.

The paper defines a word's surprisal as the log ratio of prefix probabilities. Here it is the
library's surprisal of the word under the law of the next word, `Surprisal.nextWord`, the
negative log of its conditional probability, and the paper's ratio is a theorem about it.

## References

* [hale-2001]
* [stolcke-1995]
* [levy-2008]
-/

@[expose] public section

namespace Hale2001

open InformationTheory MeasureTheory Surprisal
open scoped ENNReal

variable {T W : Type*} [MeasurableSpace T] (P : Measure T) (str : T → List W) (ws : List W)
  (w : W)

/-- Prefix-level cognitive load (section 4): the total probability of the analyses the prefix
has disconfirmed. -/
noncomputable def disconfirmed : ℝ≥0∞ := 1 - P (consistent str ws)

/-- Disconfirmed mass grows along a sentence: an extension has disconfirmed at least what its
prefix has, so prefix-level load never decreases. -/
theorem disconfirmed_mono {ws ws' : List W} (h : ws <+: ws') :
    disconfirmed P str ws ≤ disconfirmed P str ws' :=
  tsub_le_tsub_left (measure_mono (consistent_anti str h)) 1

variable [MeasurableSpace W]

/-- The surprisals of the words of `rest`, read one by one after the prefix `acc`. -/
noncomputable def totalSurprisal : List W → List W → ℝ
  | _, [] => 0
  | acc, w :: rest => surprisal (nextWord P str acc) (some w) + totalSurprisal (acc ++ [w]) rest

variable [DiscreteMeasurableSpace T] [MeasurableSingletonClass W]

/-- Word-level cognitive load (section 4): a word's surprisal is the log of the ratio of the
prefix probability before the word to the prefix probability after it. -/
theorem surprisal_nextWord_eq_log_div :
    surprisal (nextWord P str ws) (some w) =
      Real.log (P.real (consistent str ws) / P.real (consistent str (ws ++ [w]))) := by
  rw [surprisal, measureReal_def, nextWord_singleton_some, nextProb_eq_div, ENNReal.toReal_div,
    ← Real.log_inv, inv_div]
  rfl

/-- Surprisal in disconfirmation form: the log of one plus the ratio of the mass disconfirmed
at the word to the mass surviving it. -/
theorem surprisal_nextWord_eq_log_one_add (ha : 0 < P.real (consistent str (ws ++ [w]))) :
    surprisal (nextWord P str ws) (some w) =
      Real.log (1 + (P.real (consistent str ws) - P.real (consistent str (ws ++ [w])))
        / P.real (consistent str (ws ++ [w]))) := by
  rw [surprisal_nextWord_eq_log_div]
  congr 1
  field_simp
  ring

/-- Garden-pathing (section 6.1): if the mass disconfirmed at a word is at least `k` times
the surviving mass, the word's surprisal is at least `log (1 + k)`; difficulty spikes exactly
where the disconfirmable analyses comprise a great amount of probability. -/
theorem log_le_surprisal_nextWord {k : ℝ} (hk : 0 ≤ k)
    (ha : 0 < P.real (consistent str (ws ++ [w])))
    (hdis : k * P.real (consistent str (ws ++ [w])) ≤
      P.real (consistent str ws) - P.real (consistent str (ws ++ [w]))) :
    Real.log (1 + k) ≤ surprisal (nextWord P str ws) (some w) := by
  rw [surprisal_nextWord_eq_log_one_add P str ws w ha]
  refine Real.log_le_log (by linarith) ?_
  have hdiv : k ≤ (P.real (consistent str ws) - P.real (consistent str (ws ++ [w])))
      / P.real (consistent str (ws ++ [w])) :=
    (le_div_iff₀ ha).mpr hdis
  linarith

/-! ### Load along a sentence -/

variable [IsProbabilityMeasure P]

omit [MeasurableSpace W] [DiscreteMeasurableSpace T] [MeasurableSingletonClass W] in
/-- No analysis has been disconfirmed before any input is seen. -/
@[simp] theorem disconfirmed_nil : disconfirmed P str [] = 0 := by
  simp [disconfirmed]

omit [MeasurableSpace W] [DiscreteMeasurableSpace T] [MeasurableSingletonClass W] in
/-- A prefix of a prefix with positive mass has positive mass. -/
private theorem real_consistent_pos_of_prefix {ws ws' : List W} (h : ws <+: ws')
    (hpos : 0 < P.real (consistent str ws')) : 0 < P.real (consistent str ws) :=
  hpos.trans_le (measureReal_mono (consistent_anti str h))

/-- Word surprisals telescope: reading `rest` after `acc` costs the log of the ratio of the
masses before and after, whenever the whole string has positive mass. -/
theorem totalSurprisal_eq {acc rest : List W}
    (hpos : 0 < P.real (consistent str (acc ++ rest))) :
    totalSurprisal P str acc rest =
      Real.log (P.real (consistent str acc)) -
        Real.log (P.real (consistent str (acc ++ rest))) := by
  induction rest generalizing acc with
  | nil => simp [totalSurprisal]
  | cons w rest ih =>
    rw [totalSurprisal]
    have hpos' : 0 < P.real (consistent str (acc ++ [w] ++ rest)) := by
      rwa [List.append_assoc, List.singleton_append]
    have h₁ : 0 < P.real (consistent str (acc ++ [w])) :=
      real_consistent_pos_of_prefix P str (List.prefix_append _ rest) hpos'
    have h₀ : 0 < P.real (consistent str acc) :=
      real_consistent_pos_of_prefix P str (List.prefix_append acc [w]) h₁
    rw [ih hpos', List.append_assoc, List.singleton_append, surprisal_nextWord_eq_log_div,
      Real.log_div h₀.ne' h₁.ne']
    ring

/-- The linking hypothesis at the sentence level (section 4): the total surprisal of a sentence
is the negative log of its prefix mass, the whole disconfirmed mass paid out word by word. -/
theorem totalSurprisal_nil_eq {ws : List W} (hpos : 0 < P.real (consistent str ws)) :
    totalSurprisal P str [] ws = -Real.log (P.real (consistent str ws)) := by
  rw [totalSurprisal_eq P str (by simpa using hpos), consistent_nil, probReal_univ]
  simp

end Hale2001
