import Linglib.Core.FinitePMF
import Linglib.Theories.Processing.LanguageModel.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Memory Processes
@cite{futrell-gibson-levy-2020}

A `MemoryProcess` is the abstract substrate of @cite{futrell-gibson-levy-2020}'s
lossy-context surprisal: a processor that compresses its observed history
into a (possibly noisy) memory state, then predicts the next symbol from
that memory state alone.

Following the paper's claims (their §3.1):

1. **Incrementality of memory** — the encoder `encode : List Voc → FinitePMF Mem`
   maps each observed history to a distribution over memory states.
2. **Linguistic knowledge** — the predictor `predict : Mem → FinitePMF (Option Voc)`
   maps each memory state to a next-symbol distribution (with `none` = end-of-string).
3. **Inaccessibility of context** — the predictor sees *only* the memory state,
   never the underlying history. This is what makes the model *lossy*.
4. **Linking hypothesis** — processing difficulty for the next symbol is
   `expectedSurprisal`, the expectation of `-log P(w | m)` over `m ~ encode(c)`
   (Eq. 3 of the paper).

This file provides the abstract type and the master cost function.
Specialisations (lossless = classical surprisal, n-gram, erasure noise,
cue-based retrieval) live in sibling files.

## Main definitions

- `MemoryProcess Voc Mem` — pair of `(encode, predict)` kernels
- `MemoryProcess.perStateSurprisal` — Eq. 2: `-log P(w | m)`
- `MemoryProcess.expectedSurprisal` — Eq. 3: `E_{m ~ encode(c)}[-log P(w | m)]`
- `MemoryProcess.marginalProb` — Eq. 9: `Σ_m encode(c)(m) · predict(m)(w)`
- `MemoryProcess.IsDirac` — encoder is a point mass at `f c` (lossless)

## Main theorem

- `expectedSurprisal_of_dirac` — when the encoder is a Dirac at `f c`, expected
  surprisal collapses to per-state surprisal at `f c`. This is the structural
  identity that turns the lossless case into classical surprisal in
  `LossyContext.lean`.
-/

set_option autoImplicit false

namespace Theories.Processing

open Core Real
open Theories.Processing.LanguageModel (LangModel)

/-- A processing architecture with a memory bottleneck.

`encode` lossily compresses the observed history into a distribution over
memory states; `predict` gives the next-symbol distribution from a memory
state alone. The memory state mediates *all* information flow from the
past to the prediction (the inaccessibility-of-context claim of
@cite{futrell-gibson-levy-2020} §3.1.3). -/
structure MemoryProcess (Voc Mem : Type*) [Fintype Voc] [Fintype Mem] where
  /-- Lossy encoder: history → distribution over memory states. -/
  encode : List Voc → FinitePMF Mem
  /-- Predictor: memory state → next-symbol distribution. -/
  predict : Mem → FinitePMF (Option Voc)

namespace MemoryProcess

variable {Voc Mem : Type*} [Fintype Voc] [Fintype Mem]

/-- Per-state surprisal: `D_lc(w | m) = -log P(w | m)`.
(@cite{futrell-gibson-levy-2020} Eq. 2.) -/
noncomputable def perStateSurprisal (mp : MemoryProcess Voc Mem)
    (m : Mem) (w : Voc) : ℝ :=
  -Real.log (((mp.predict m).mass (some w)) : ℝ)

/-- Expected surprisal under the lossy memory process:
`D_lc(w | c) = E_{m ~ encode(c)}[-log P(w | m)]`.
(@cite{futrell-gibson-levy-2020} Eq. 3.)

This is the master cost function from which classical surprisal,
n-gram surprisal, and the cue-based retrieval cost all derive as
instantiations of `(encode, predict)`. -/
noncomputable def expectedSurprisal (mp : MemoryProcess Voc Mem)
    (c : List Voc) (w : Voc) : ℝ :=
  ∑ m : Mem, ((mp.encode c).mass m : ℝ) * mp.perStateSurprisal m w

/-- Marginal next-symbol probability under the memory process:
`P(w | c) = Σ_m P(m | c) · P(w | m)`.
(@cite{futrell-gibson-levy-2020} Eq. 9.)

Note: `-log marginalProb` (the surprisal of the *marginal*) is not in
general equal to `expectedSurprisal` (the *expected* surprisal). The two
agree iff the encoder is a Dirac (no information loss); otherwise Jensen
gives `expectedSurprisal ≥ -log marginalProb`. -/
def marginalProb (mp : MemoryProcess Voc Mem)
    (c : List Voc) (w : Voc) : ℚ :=
  ∑ m : Mem, (mp.encode c).mass m * (mp.predict m).mass (some w)

/-- The memory process is *Dirac at* `f` if the encoder concentrates
all mass on `f c` for every history `c`. This is the lossless
("perfect memory") regime: the memory state is a deterministic
function of the history.

(@cite{futrell-gibson-levy-2020} §3.5.1: classical surprisal arises
exactly in this case.) -/
def IsDirac [DecidableEq Mem] (mp : MemoryProcess Voc Mem)
    (f : List Voc → Mem) : Prop :=
  ∀ c, mp.encode c = FinitePMF.pure (f c)

/-- **Dirac collapse.** When the encoder is a Dirac at `f c`, expected
surprisal reduces to per-state surprisal evaluated at `f c`. The
expectation has no spread to average over.

This is the structural identity that lets us recover classical
surprisal as the special case of `expectedSurprisal` with lossless
memory (see `LossyContext.lean`'s
`expectedSurprisal_eq_surprisal_of_lossless`). -/
theorem expectedSurprisal_of_dirac [DecidableEq Mem]
    {mp : MemoryProcess Voc Mem} {f : List Voc → Mem}
    (h : mp.IsDirac f) (c : List Voc) (w : Voc) :
    mp.expectedSurprisal c w = mp.perStateSurprisal (f c) w := by
  unfold expectedSurprisal
  rw [h c]
  show ∑ m : Mem, ((FinitePMF.pure (f c)).mass m : ℝ) *
        mp.perStateSurprisal m w = mp.perStateSurprisal (f c) w
  have hpoint : ∀ m : Mem,
      ((FinitePMF.pure (f c)).mass m : ℝ) * mp.perStateSurprisal m w =
        if m = f c then mp.perStateSurprisal m w else 0 := by
    intro m
    unfold FinitePMF.pure
    show ((if m = f c then (1 : ℚ) else 0 : ℚ) : ℝ) *
        mp.perStateSurprisal m w = _
    split_ifs with h
    · simp
    · simp
  simp_rw [hpoint, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end MemoryProcess

end Theories.Processing
