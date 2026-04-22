import Linglib.Theories.Processing.LanguageModel.Basic
import Linglib.Theories.Processing.PredictiveUncertainty.Config
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Incremental Alternative Sampling: Real-Valued Foundation
@cite{giulianelli-etal-2026} @cite{giulianelli-opedal-cotterell-2024}

The probabilistic backbone underneath `Config.lean`'s enum-level
configuration. The `LangModel` primitive lives in
`Theories/Processing/LanguageModel/Basic.lean`; this file builds on it
to define the `genSurprisal` family of @cite{giulianelli-etal-2026}'s
Eq. 3 — real-valued functions of an LM, context, and target — and shows
that classical surprisal is recovered as the special case
(warp = −log, score = indicator).

This file is what makes `Config.lean`'s enum tags (`WarpingFn`,
`ScoringFn`) denote actual mathematical objects rather than just labels:
`WarpingFn.denote` ports each tag to its real function, and
`standardSurprisal_denotes_surprisal` is the (non-trivial) reduction
theorem that the enum config "standard surprisal" really computes the
classical −log p(w | c).

## Main definitions

- `genSurprisal`: γ(w; c) = warp( E_{a ~ p(·|c)} [score(a, w, c)] )
- `indicatorScore`: g(a, w, c) = 𝟙[a = some w]
- `WarpingFn.denote`: the bridge from enum tags to real functions
- `informationValue1`: horizon-1 IAS, expected distance to target

## Main theorem

- `standardSurprisal_denotes_surprisal`: when the (warp, score)
  arguments are the denotations of `standardSurprisal`'s warping and
  scoring tags, `genSurprisal` collapses to `LangModel.surprisal`. This
  is the formal content of the surprisal-as-prefix-expectation identity
  (Eqs. 2a–2d of @cite{giulianelli-etal-2026}).
-/

set_option autoImplicit false

namespace Theories.Processing.PredictiveUncertainty

open Finset BigOperators Real
open Theories.Processing.LanguageModel (LangModel)

-- ============================================================================
-- §1: Generalised Surprisal (Eq. 3)
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
  warp (∑ o : Option Voc, ((lm.next c) o).toReal * score o w c)

/-- The indicator scoring function: 1 iff the alternative matches the target. -/
noncomputable def indicatorScore {Voc : Type*} [DecidableEq Voc]
    (o : Option Voc) (w : Voc) (_ : List Voc) : ℝ :=
  if o = some w then 1 else 0

-- ============================================================================
-- §2: Bridge from Enum Tags to Real Functions
-- ============================================================================

/-- Denotation of a `WarpingFn` enum tag as a real function `ℝ → ℝ`.
This is the bridge that turns the symbolic enum in `Config.lean` into
actual mathematical content. -/
noncomputable def WarpingFn.denote : WarpingFn → (ℝ → ℝ)
  | .negLog   => fun x => -Real.log x
  | .identity => id

/-- Denotation of a `ScoringFn` enum tag as a scoring function. The
`.indicator` case is fully concrete (= `indicatorScore`); the `.distance`
and `.similarity` cases are parametric in the user-supplied distance and
similarity functions, since the paper's framework abstracts over these. -/
noncomputable def ScoringFn.denote
    {Voc : Type*} [DecidableEq Voc]
    (dist sim : Option Voc → Voc → List Voc → ℝ) :
    ScoringFn → (Option Voc → Voc → List Voc → ℝ)
  | .indicator  => indicatorScore
  | .distance   => dist
  | .similarity => sim

/-- Denotation of a complete `SurprisalConfig` against a language model:
applies `cfg.warp.denote` and `cfg.scoring.denote` through `genSurprisal`.
The `horizon` and `level` fields are recorded labels and currently
ignored at the denotation layer (the `informationValue1` reduction below
is the only horizon-aware case formalised so far). -/
noncomputable def SurprisalConfig.applyTo
    {Voc : Type*} [Fintype Voc] [DecidableEq Voc]
    (cfg : SurprisalConfig)
    (lm : LangModel Voc)
    (dist sim : Option Voc → Voc → List Voc → ℝ)
    (c : List Voc) (w : Voc) : ℝ :=
  genSurprisal lm cfg.warp.denote (cfg.scoring.denote dist sim) c w

-- ============================================================================
-- §3: Standard Surprisal as Special Case
-- ============================================================================

/-- **Standard surprisal is the special case** of `genSurprisal` with
`warp = −log` and `score = indicator`. Choosing these (warp, score)
collapses Eq. 3 to γ(w; c) = −log p(w | c) — i.e., classical surprisal
@cite{levy-2008}.

This is the non-trivial reduction theorem: it shows that the enum-level
claim `standardSurprisal = (negLog, indicator, 1, predictive)` in
`Config.lean` actually denotes the classical surprisal function on
language models, rather than being a definitional rfl. -/
theorem standardSurprisal_denotes_surprisal
    {Voc : Type*} [Fintype Voc] [DecidableEq Voc]
    (lm : LangModel Voc) (c : List Voc) (w : Voc) :
    genSurprisal lm
        standardSurprisal.warp.denote
        indicatorScore c w =
      lm.surprisal c w := by
  unfold genSurprisal LangModel.surprisal LangModel.nextProb
  show standardSurprisal.warp.denote _ = _
  unfold standardSurprisal WarpingFn.denote
  have key : ∀ o : Option Voc,
      ((lm.next c) o).toReal * indicatorScore o w c =
        if o = some w then ((lm.next c) (some w)).toReal else 0 := by
    intro o
    unfold indicatorScore
    split_ifs with h
    · rw [h]; ring
    · ring
  simp_rw [key, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Full enum-config reduction**: applying the entire `standardSurprisal`
configuration (not just its warping field) to any LM yields classical
surprisal, regardless of which `dist` and `sim` parameters one chooses.
This is the symmetric counterpart to `standardSurprisal_denotes_surprisal`
— it shows that the *whole* enum tag tuple in `Config.lean` denotes
correctly, since `.indicator` ignores its `dist`/`sim` arguments. -/
theorem standardSurprisal_applyTo_eq_surprisal
    {Voc : Type*} [Fintype Voc] [DecidableEq Voc]
    (lm : LangModel Voc)
    (dist sim : Option Voc → Voc → List Voc → ℝ)
    (c : List Voc) (w : Voc) :
    standardSurprisal.applyTo lm dist sim c w = lm.surprisal c w := by
  unfold SurprisalConfig.applyTo standardSurprisal ScoringFn.denote
  exact standardSurprisal_denotes_surprisal lm c w

-- ============================================================================
-- §4: Information Value at Horizon 1
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
  ∑ o : Option Voc, ((lm.next c) o).toReal * d o w

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

/-- **Full enum-config reduction for IAS** (horizon-agnostic): the entire
`informationValue h l` configuration, applied to `(lm, dist, sim)`, equals
`informationValue1 lm dist'` where `dist' o w := dist o w c`. The horizon
`h` and level `l` are recorded labels at this denotation layer; horizon
sensitivity enters only when one moves from `informationValue1` to a
horizon-h sum over h-grams. -/
theorem informationValue_applyTo_eq_informationValue1
    {Voc : Type*} [Fintype Voc] [DecidableEq Voc]
    (lm : LangModel Voc)
    (dist sim : Option Voc → Voc → List Voc → ℝ)
    (h : Nat) (l : RepLevel)
    (c : List Voc) (w : Voc) :
    (informationValue h l).applyTo lm dist sim c w =
      informationValue1 lm (fun o w' => dist o w' c) c w := by
  unfold SurprisalConfig.applyTo informationValue
        WarpingFn.denote ScoringFn.denote genSurprisal informationValue1
  rfl

end Theories.Processing.PredictiveUncertainty
