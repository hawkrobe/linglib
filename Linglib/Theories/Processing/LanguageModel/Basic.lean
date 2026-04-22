import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Language Model as a Markov Kernel

An autoregressive language model over a vocabulary `Voc` is a Markov
kernel `List Voc → PMF (Option Voc)` from contexts to next-symbol
distributions, with `none` denoting end-of-string.

This is the smallest cross-cutting primitive shared by everything in
`Theories/Processing/`: surprisal-based theories, the IAS family
(@cite{giulianelli-etal-2026}), and any downstream measure that wants
a unified notion of "the LM's predictive distribution at a context".

`PMF` is mathlib's probability monad over a (countable) type
(`PMF α := { f : α → ℝ≥0∞ // HasSum f 1 }`); using it here gives the
language-model layer the canonical Markov-kernel typing and removes
the `[Fintype Voc]` constraint that the old `FinitePMF`-based version
inherited (vocabularies like `String` or token streams need not be
finite).

## Main definitions

- `LangModel Voc`: kernel `List Voc → PMF (Option Voc)`
- `LangModel.nextProb`: conditional probability of a single symbol
- `LangModel.surprisal`: −log p(w | c), in nats (@cite{levy-2008})
-/

set_option autoImplicit false

namespace Theories.Processing.LanguageModel

open Real
open scoped ENNReal

/-- An autoregressive language model over a vocabulary `Voc`,
expressed as a Markov kernel from contexts to next-symbol distributions.
A draw of `none` denotes end-of-string. -/
structure LangModel (Voc : Type*) where
  /-- Conditional distribution over `Option Voc` given a context. -/
  next : List Voc → PMF (Option Voc)

namespace LangModel

variable {Voc : Type*} (lm : LangModel Voc)

/-- Conditional probability of the next symbol `w` given context `c`. -/
def nextProb (c : List Voc) (w : Voc) : ℝ≥0∞ := lm.next c (some w)

/-- Surprisal of the next symbol `w` given context `c` (in nats).
This is the classical Shannon information content @cite{levy-2008}. -/
noncomputable def surprisal (c : List Voc) (w : Voc) : ℝ :=
  -Real.log (lm.nextProb c w).toReal

end LangModel

end Theories.Processing.LanguageModel
