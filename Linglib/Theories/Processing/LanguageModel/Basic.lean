import Linglib.Core.FinitePMF
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Language Model as a Markov Kernel

An autoregressive language model over a finite vocabulary `Voc` is
a Markov kernel `List Voc → FinitePMF (Option Voc)` from contexts to
next-symbol distributions, with `none` denoting end-of-string.

This is the smallest cross-cutting primitive shared by everything in
`Theories/Processing/`: surprisal-based theories, the IAS family
(@cite{giulianelli-etal-2026}), and any downstream measure that wants
a unified notion of "the LM's predictive distribution at a context".

## Main definitions

- `LangModel Voc`: kernel `List Voc → FinitePMF (Option Voc)`
- `LangModel.nextProb`: conditional probability of a single symbol
- `LangModel.surprisal`: −log p(w | c), in nats (@cite{levy-2008})
-/

set_option autoImplicit false

namespace Theories.Processing.LanguageModel

open Core Real

/-- An autoregressive language model over a finite vocabulary `Voc`,
expressed as a Markov kernel from contexts to next-symbol distributions.
A draw of `none` denotes end-of-string. -/
structure LangModel (Voc : Type*) [Fintype Voc] where
  /-- Conditional distribution over `Option Voc` given a context. -/
  next : List Voc → FinitePMF (Option Voc)

namespace LangModel

variable {Voc : Type*} [Fintype Voc] (lm : LangModel Voc)

/-- Conditional probability of the next symbol `w` given context `c`. -/
def nextProb (c : List Voc) (w : Voc) : ℚ := (lm.next c).mass (some w)

/-- Surprisal of the next symbol `w` given context `c` (in nats).
This is the classical Shannon information content @cite{levy-2008}. -/
noncomputable def surprisal (c : List Voc) (w : Voc) : ℝ :=
  -Real.log ((lm.nextProb c w : ℝ))

end LangModel

end Theories.Processing.LanguageModel
