/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Processing.Expectation.PrefixProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Hale (2001): a probabilistic Earley parser as a psycholinguistic model

[hale-2001] (NAACL 2001) proposes that cognitive load is the total probability
of the structural analyses disconfirmed by the input so far (§4): for a
consistent grammar, the effort for a prefix is one minus its prefix
probability, and word-by-word reading time is proportional to
`log (αₙ₋₁ / αₙ)` — the word's surprisal — where `α` is [stolcke-1995]'s
prefix probability, computed by a probabilistic Earley parser that is
strong-competence, frequency-sensitive, and eager (Principles 1–3). The
parser is a *total-parallelism* theory (§3): garden-pathing needs no
reanalysis — it happens exactly at words where the disconfirmed analyses
comprise most of the probability mass (§6.1: at "fell" in *the horse raced
past the barn fell*, grammar (1) puts the pre-word prefix probability more
than ten times the post-word one), and the subject/object relative asymmetry
falls out the same way (§7).

## Main definitions

* `surprisal` — the word-level linking hypothesis, in the paper's
  log-of-ratio form.
* `disconfirmed` — the prefix-level load: total mass of disconfirmed analyses.

## Main results

* `surprisal_eq_neg_log_nextProb` — the ratio form is the conditional-word-
  probability form (the identity [levy-2008] later grounds in relative
  entropy).
* `surprisal_eq_log_one_add`, `log_le_surprisal` — surprisal grows with the
  ratio of disconfirmed to surviving mass: the paper's account of
  garden-pathing, stated for any generative process.

## Implementation notes

The demonstrations' numerics (grammars (1)–(3), Figs. 3–8) require Stolcke's
Earley chart over recursive PCFGs; they are cited in prose above and their
formalization awaits an Earley substrate. The theorems here are the
grammar-independent content of the linking hypothesis.
-/

namespace Hale2001

open Processing.Expectation
open scoped ENNReal

variable {T W : Type*} (P : PMF T) (str : T → List W) (ws : List W) (w : W)

/-- Word-level cognitive load (§4): the log of the ratio of the prefix
    probability before the word to the prefix probability after it. -/
noncomputable def surprisal : ℝ :=
  Real.log ((prefixMass P str ws).toReal / (prefixMass P str (ws ++ [w])).toReal)

/-- Prefix-level cognitive load (§4): the total probability of the analyses
    the prefix has disconfirmed. -/
noncomputable def disconfirmed : ℝ≥0∞ :=
  1 - prefixMass P str ws

/-- No analysis has been disconfirmed before any input is seen. -/
@[simp] theorem disconfirmed_nil : disconfirmed P str [] = 0 := by
  rw [disconfirmed, prefixMass_nil, tsub_self]

/-- The paper's ratio form of surprisal is the negative log conditional
    probability of the word — the form [levy-2008] derives as the relative
    entropy of the belief update. -/
theorem surprisal_eq_neg_log_nextProb :
    surprisal P str ws w = -Real.log (nextProb P str ws w).toReal := by
  rw [surprisal, nextProb, ENNReal.toReal_div, ← Real.log_inv, inv_div]

/-- Surprisal in disconfirmation form: the log of one plus the ratio of the
    mass disconfirmed at the word to the mass surviving it. -/
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

/-- **Garden-pathing** (§6.1): if the mass disconfirmed at a word is at least
    `k` times the surviving mass, the word's surprisal is at least
    `log (1 + k)` — difficulty spikes exactly where the disconfirmable
    analyses comprise a great amount of probability. -/
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
