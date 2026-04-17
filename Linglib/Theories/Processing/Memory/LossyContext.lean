import Linglib.Theories.Processing.Memory.Basic

/-!
# Lossy-Context Surprisal: Bridge to Classical Surprisal
@cite{futrell-gibson-levy-2020}

`MemoryProcess` (in `Basic.lean`) is the abstract type underlying the
lossy-context surprisal model of @cite{futrell-gibson-levy-2020}
("Lossy-Context Surprisal: An Information-Theoretic Model of Memory
Effects in Sentence Processing", Cog Sci 44, e12814).

This file proves the paper's §3.5.1 reduction: when the memory encoder
loses *no* information (a Dirac at some history-summarising function
`f`), expected surprisal collapses to classical surprisal under the
language model induced by `predict ∘ f`.

This is the load-bearing identity that demotes classical surprisal from
a primitive to a special case — the same architectural move that lets
mathlib derive `Module` from `AddCommGroup + DistribMulAction` rather
than treating it as primitive.

## Main definitions

- `MemoryProcess.IsLosslessFor` — the process exactly realises an LM
- `LangModel.virtualLM` — the LM induced by composing `predict` with a
  history-summarising function

## Main theorem

- `expectedSurprisal_eq_surprisal_of_lossless` — lossless `mp` of `lm`
  yields `mp.expectedSurprisal = lm.surprisal`
-/

set_option autoImplicit false

namespace Theories.Processing

open Core Real
open Theories.Processing.LanguageModel (LangModel)

namespace MemoryProcess

variable {Voc Mem : Type*} [Fintype Voc] [Fintype Mem]

/-- A memory process is *lossless for* a language model `lm` if some
deterministic history-summary `f` makes the encoder a Dirac at `f c`
and the predictor's distribution at `f c` equal to `lm.next c`.

(@cite{futrell-gibson-levy-2020} §3.5.1: this is the "perfect memory"
regime in which lossy-context surprisal collapses to classical
surprisal.) -/
def IsLosslessFor [DecidableEq Mem]
    (mp : MemoryProcess Voc Mem) (lm : LangModel Voc) : Prop :=
  ∃ f : List Voc → Mem,
    mp.IsDirac f ∧ ∀ c, mp.predict (f c) = lm.next c

/-- **Lossless reduction (§3.5.1).** A memory process that is lossless
for `lm` produces exactly the classical surprisal of `lm`. Lossy-context
surprisal *generalises* surprisal — it does not replace it.

Reading: when no information is lost in encoding, the integral over
memory states in `expectedSurprisal` (Eq. 3) degenerates to a single
deterministic prediction, recovering Shannon's `-log p(w | c)`. -/
theorem expectedSurprisal_eq_surprisal_of_lossless [DecidableEq Mem]
    {mp : MemoryProcess Voc Mem} {lm : LangModel Voc}
    (h : mp.IsLosslessFor lm) (c : List Voc) (w : Voc) :
    mp.expectedSurprisal c w = lm.surprisal c w := by
  obtain ⟨f, hdir, hpred⟩ := h
  rw [expectedSurprisal_of_dirac hdir]
  unfold perStateSurprisal LangModel.surprisal LangModel.nextProb
  rw [hpred c]

/-- The "virtual" language model induced by a deterministic
history-summary `f` and a memory predictor `predict`. -/
def virtualLM (mp : MemoryProcess Voc Mem)
    (f : List Voc → Mem) : LangModel Voc where
  next := fun c => mp.predict (f c)

/-- A memory process is lossless for its own virtual LM whenever the
encoder is a Dirac at `f`. This is the "construction-side" complement
of `expectedSurprisal_eq_surprisal_of_lossless`: any Dirac encoder
*does* realise some LM, namely `virtualLM`. -/
theorem isLosslessFor_virtualLM [DecidableEq Mem]
    (mp : MemoryProcess Voc Mem) {f : List Voc → Mem}
    (h : mp.IsDirac f) :
    mp.IsLosslessFor (mp.virtualLM f) :=
  ⟨f, h, fun _ => rfl⟩

/-- **Lossless ⇒ classical surprisal of the virtual LM.** Any Dirac
memory process realises classical surprisal under its induced
language model. This is the reduction in its purely structural form,
without an external `lm` parameter. -/
theorem expectedSurprisal_eq_virtualLM_surprisal [DecidableEq Mem]
    {mp : MemoryProcess Voc Mem} {f : List Voc → Mem}
    (h : mp.IsDirac f) (c : List Voc) (w : Voc) :
    mp.expectedSurprisal c w = (mp.virtualLM f).surprisal c w :=
  expectedSurprisal_eq_surprisal_of_lossless
    (mp.isLosslessFor_virtualLM h) c w

end MemoryProcess

end Theories.Processing
