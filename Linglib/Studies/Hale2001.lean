/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Processing.Expectation.PrefixProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Hale (2001): A Probabilistic Earley Parser as a Psycholinguistic Model

This file formalizes the linking hypothesis of [hale-2001]. Cognitive load is the total
probability of the structural analyses the input so far has disconfirmed (section 4): for a
consistent grammar, the effort spent on a prefix is one minus its prefix probability,
`disconfirmed`, and word-by-word reading time is proportional to the log of the ratio of the
prefix probability before the word to the one after it, the word's surprisal, `surprisal`,
where the prefix probability is [stolcke-1995]'s, computed by a probabilistic Earley parser that
is strong-competence, frequency-sensitive, and eager (Principles 1 to 3). The parser computes
every parse, so the theory is one of total parallelism (section 3): garden-pathing needs no
reanalysis and happens exactly at words where the disconfirmed analyses comprise most of the
probability mass, `log_le_surprisal`, which is how the paper reads the spike at *fell* in *the
horse raced past the barn fell*, where grammar (1) puts the prefix probability before the word
at more than ten times the one after it (section 6.1), and the subject and object relative
asymmetry of grammar (3) (section 6.3). The ratio form of surprisal is the negative log
conditional probability of the word, `surprisal_eq_neg_log_nextProb`, the form [levy-2008]
later grounds in relative entropy; and the two levels of the linking hypothesis agree, since
prefix-level load only grows along a sentence, `disconfirmed_mono`, and word-level surprisals
telescope to the negative log of the sentence's prefix mass, `totalSurprisal_nil_eq`.

## Implementation notes

The demonstrations' numerics, grammars (1) to (3) and the reading-time figures, require
Stolcke's Earley chart over recursive probabilistic context-free grammars and await an Earley
substrate; the theorems here are the grammar-independent content of the linking hypothesis,
stated for any generative process with string yields.

## References

* [hale-2001]
* [stolcke-1995]
* [levy-2008]
-/

namespace Hale2001

open Processing.Expectation
open scoped ENNReal

variable {T W : Type*} (P : PMF T) (str : T → List W) (ws : List W) (w : W)

/-- Word-level cognitive load (section 4): the log of the ratio of the prefix probability
before the word to the prefix probability after it. -/
noncomputable def surprisal : ℝ :=
  Real.log ((prefixMass P str ws).toReal / (prefixMass P str (ws ++ [w])).toReal)

/-- Prefix-level cognitive load (section 4): the total probability of the analyses the prefix
has disconfirmed. -/
noncomputable def disconfirmed : ℝ≥0∞ :=
  1 - prefixMass P str ws

/-- No analysis has been disconfirmed before any input is seen. -/
@[simp] theorem disconfirmed_nil : disconfirmed P str [] = 0 := by
  rw [disconfirmed, prefixMass_nil, tsub_self]

/-- Disconfirmed mass grows along a sentence: an extension has disconfirmed at least what its
prefix has, so prefix-level load never decreases. -/
theorem disconfirmed_mono {ws ws' : List W} (h : ws <+: ws') :
    disconfirmed P str ws ≤ disconfirmed P str ws' :=
  tsub_le_tsub_left (prefixMass_anti P str h) 1

/-- The surprisals of the words of `rest`, read one by one after the prefix `acc`. -/
noncomputable def totalSurprisal : List W → List W → ℝ
  | _, [] => 0
  | acc, w :: rest => surprisal P str acc w + totalSurprisal (acc ++ [w]) rest

/-- A prefix of a prefix with positive mass has positive mass. -/
private theorem prefixMass_pos_of_prefix {ws ws' : List W} (h : ws <+: ws')
    (hpos : 0 < (prefixMass P str ws').toReal) : 0 < (prefixMass P str ws).toReal :=
  lt_of_lt_of_le hpos <| ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top
      (prefixMass_nil P str ▸ prefixMass_anti P str (List.nil_prefix)))
    (prefixMass_anti P str h)

/-- Word surprisals telescope: reading `rest` after `acc` costs the log of the ratio of the
masses before and after, whenever the whole string has positive mass. -/
theorem totalSurprisal_eq {acc rest : List W}
    (hpos : 0 < (prefixMass P str (acc ++ rest)).toReal) :
    totalSurprisal P str acc rest =
      Real.log (prefixMass P str acc).toReal
        - Real.log (prefixMass P str (acc ++ rest)).toReal := by
  induction rest generalizing acc with
  | nil => simp [totalSurprisal]
  | cons w rest ih =>
    rw [totalSurprisal]
    have hpos' : 0 < (prefixMass P str (acc ++ [w] ++ rest)).toReal := by
      rwa [List.append_assoc, List.singleton_append]
    have h₁ : 0 < (prefixMass P str (acc ++ [w])).toReal :=
      prefixMass_pos_of_prefix P str (List.prefix_append _ rest) hpos'
    have h₀ : 0 < (prefixMass P str acc).toReal :=
      prefixMass_pos_of_prefix P str (List.prefix_append acc [w]) h₁
    rw [ih hpos', List.append_assoc, List.singleton_append, surprisal,
      Real.log_div h₀.ne' h₁.ne']
    ring

/-- The linking hypothesis at the sentence level (section 4): the total surprisal of a sentence
is the negative log of its prefix mass, the whole disconfirmed mass paid out word by word. -/
theorem totalSurprisal_nil_eq {ws : List W} (hpos : 0 < (prefixMass P str ws).toReal) :
    totalSurprisal P str [] ws = -Real.log (prefixMass P str ws).toReal := by
  rw [totalSurprisal_eq P str (by simpa using hpos), prefixMass_nil]
  simp

/-- The paper's ratio form of surprisal is the negative log conditional probability of the
word, the form [levy-2008] derives as the relative entropy of the belief update. -/
theorem surprisal_eq_neg_log_nextProb :
    surprisal P str ws w = -Real.log (nextProb P str ws w).toReal := by
  rw [surprisal, nextProb, ENNReal.toReal_div, ← Real.log_inv, inv_div]

/-- Surprisal in disconfirmation form: the log of one plus the ratio of the mass disconfirmed
at the word to the mass surviving it. -/
theorem surprisal_eq_log_one_add
    (ha : 0 < (prefixMass P str (ws ++ [w])).toReal) :
    surprisal P str ws w =
      Real.log (1 + ((prefixMass P str ws).toReal
        - (prefixMass P str (ws ++ [w])).toReal)
          / (prefixMass P str (ws ++ [w])).toReal) := by
  rw [surprisal]
  congr 1
  field_simp
  ring

/-- Garden-pathing (section 6.1): if the mass disconfirmed at a word is at least `k` times
the surviving mass, the word's surprisal is at least `log (1 + k)`; difficulty spikes exactly
where the disconfirmable analyses comprise a great amount of probability. -/
theorem log_le_surprisal {k : ℝ} (hk : 0 ≤ k)
    (ha : 0 < (prefixMass P str (ws ++ [w])).toReal)
    (hdis : k * (prefixMass P str (ws ++ [w])).toReal ≤
      (prefixMass P str ws).toReal - (prefixMass P str (ws ++ [w])).toReal) :
    Real.log (1 + k) ≤ surprisal P str ws w := by
  rw [surprisal_eq_log_one_add P str ws w ha]
  refine Real.log_le_log (by linarith) ?_
  have hdiv : k ≤ ((prefixMass P str ws).toReal
      - (prefixMass P str (ws ++ [w])).toReal)
        / (prefixMass P str (ws ++ [w])).toReal :=
    (le_div_iff₀ ha).mpr hdis
  linarith

end Hale2001
