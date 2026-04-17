import Linglib.Core.FinitePMF
import Linglib.Core.GeneralisedSurprisal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Generalised Surprisal: Real-Valued Foundation
@cite{giulianelli-etal-2026} @cite{giulianelli-opedal-cotterell-2024}

The probabilistic backbone underneath `Core.GeneralisedSurprisal`'s
enum-level configuration. A `LangModel` is a Markov kernel from contexts
to next-symbol distributions (with `none` representing end-of-string).
Standard surprisal and the `genSurprisal` family of @cite{giulianelli-etal-2026}'s
Eq. 3 are real-valued functions of an LM, context, and target — and
classical surprisal is recovered as the special case
(warp = −log, score = indicator).

This file is what makes `Core.GeneralisedSurprisal`'s enum tags
(`WarpingFn`, `ScoringFn`) denote actual mathematical objects rather than
just labels: `WarpingFn.denote` ports each tag to its real function, and
`standardSurprisal_denotes_surprisal` is the (non-trivial) reduction
theorem that the enum config "standard surprisal" really computes the
classical −log p(w | c).

## Main definitions

- `LangModel Voc`: an autoregressive LM over vocabulary `Voc`, as a Markov
  kernel `List Voc → FinitePMF (Option Voc)` (none = EOS)
- `LangModel.surprisal`: −log p(w | c), in nats
- `genSurprisal`: γ(w; c) = warp( E_{a ~ p(·|c)} [score(a, w, c)] )
- `indicatorScore`: g(a, w, c) = 𝟙[a = some w]
- `WarpingFn.denote`: the bridge from enum tags to real functions

## Main theorem

- `standardSurprisal_denotes_surprisal`: when the (warp, score)
  arguments are the denotations of `Core.GeneralisedSurprisal.standardSurprisal`'s
  warping and scoring tags, `genSurprisal` collapses to `LangModel.surprisal`.
  This is the formal content of the surprisal-as-prefix-expectation
  identity (Eqs. 2a–2d of @cite{giulianelli-etal-2026}).
-/

set_option autoImplicit false

namespace Theories.Processing.PredictiveUncertainty

open Finset BigOperators Real Core

-- ============================================================================
-- §1: Language Model as Markov Kernel
-- ============================================================================

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

-- ============================================================================
-- §2: Generalised Surprisal (Eq. 3)
-- ============================================================================

/-- Generalised surprisal (@cite{giulianelli-etal-2026} Eq. 3):

  γ(w; c) = warp( E_{a ~ p(·|c)} [score(a, w, c)] )

`warp` is the f, `score` is the g, and the sampler is the LM's own
next-symbol distribution. Specialising (warp, score) recovers existing
processing measures. -/
noncomputable def genSurprisal {Voc : Type*} [Fintype Voc]
    (lm : LangModel Voc)
    (warp : ℝ → ℝ)
    (score : Option Voc → Voc → List Voc → ℝ)
    (c : List Voc) (w : Voc) : ℝ :=
  warp (∑ o : Option Voc, ((lm.next c).mass o : ℝ) * score o w c)

/-- The indicator scoring function: 1 iff the alternative matches the target. -/
noncomputable def indicatorScore {Voc : Type*} [DecidableEq Voc]
    (o : Option Voc) (w : Voc) (_ : List Voc) : ℝ :=
  if o = some w then 1 else 0

-- ============================================================================
-- §3: Bridge from Enum Tags to Real Functions
-- ============================================================================

/-- Denotation of a `WarpingFn` enum tag as a real function `ℝ → ℝ`.
This is the bridge that turns the symbolic enum in
`Core.GeneralisedSurprisal` into actual mathematical content. -/
noncomputable def _root_.Core.GeneralisedSurprisal.WarpingFn.denote :
    Core.GeneralisedSurprisal.WarpingFn → (ℝ → ℝ)
  | .negLog   => fun x => -Real.log x
  | .identity => id

-- ============================================================================
-- §4: Standard Surprisal as Special Case
-- ============================================================================

/-- **Standard surprisal is the special case** of `genSurprisal` with
`warp = −log` and `score = indicator`. Choosing these (warp, score)
collapses Eq. 3 to γ(w; c) = −log p(w | c) — i.e., classical surprisal
@cite{levy-2008}.

This is the non-trivial reduction theorem: it shows that the enum-level
claim `standardSurprisal = (negLog, indicator, 1, predictive)` in
`Core.GeneralisedSurprisal` actually denotes the classical surprisal
function on language models, rather than being a definitional rfl. -/
theorem standardSurprisal_denotes_surprisal
    {Voc : Type*} [Fintype Voc] [DecidableEq Voc]
    (lm : LangModel Voc) (c : List Voc) (w : Voc) :
    genSurprisal lm
        (Core.GeneralisedSurprisal.standardSurprisal.warp.denote)
        indicatorScore c w =
      lm.surprisal c w := by
  unfold genSurprisal LangModel.surprisal LangModel.nextProb
  show Core.GeneralisedSurprisal.WarpingFn.denote
        Core.GeneralisedSurprisal.standardSurprisal.warp _ = _
  unfold Core.GeneralisedSurprisal.standardSurprisal
        Core.GeneralisedSurprisal.WarpingFn.denote
  have key : ∀ o : Option Voc,
      ((lm.next c).mass o : ℝ) * indicatorScore o w c =
        if o = some w then ((lm.next c).mass (some w) : ℝ) else 0 := by
    intro o
    unfold indicatorScore
    split_ifs with h
    · rw [h]; ring
    · ring
  simp_rw [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

-- ============================================================================
-- §5: Information Value at Horizon 1
-- ============================================================================

/-- **Incremental information value at horizon 1**: the expected distance
between sampled next-symbols and the actual outcome.

This is the single-step specialisation of the IAS measure
(@cite{giulianelli-etal-2026}'s V_{r,d,1}, Eq. 6). The full IAS
generalises to horizon h ≥ 1 by sampling h-grams; we keep the h = 1
case here as the load-bearing definition (it is what is needed to
recover surprisal as a special instance via choice of distance d).

The relationship to `genSurprisal` is purely structural: information
value is `genSurprisal` with `warp = id` and `score` = a distance. -/
noncomputable def informationValue1
    {Voc : Type*} [Fintype Voc]
    (lm : LangModel Voc) (d : Option Voc → Voc → ℝ)
    (c : List Voc) (w : Voc) : ℝ :=
  ∑ o : Option Voc, ((lm.next c).mass o : ℝ) * d o w

/-- Information value at horizon 1 is `genSurprisal` with the identity
warping. The sampler is the LM, the scoring function is the distance,
and there is no warping — exactly the (identity, distance, 1, l)
instantiation of @cite{giulianelli-etal-2026}'s family. -/
theorem informationValue1_eq_genSurprisal
    {Voc : Type*} [Fintype Voc]
    (lm : LangModel Voc) (d : Option Voc → Voc → ℝ)
    (c : List Voc) (w : Voc) :
    informationValue1 lm d c w =
      genSurprisal lm id (fun o w' _ => d o w') c w := rfl

end Theories.Processing.PredictiveUncertainty
