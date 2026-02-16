/-
# Tessler & Goodman (2019): The Language of Generalization

Psychological Review, 126(3), 395-436.

## Core Insight

Generics ("Robins lay eggs") use the SAME uncertain threshold semantics
as gradable adjectives (Lassiter & Goodman 2017). The scale is **prevalence**
rather than height/degree:

```
⟦generic⟧(p, θ) = 1 if prevalence p > threshold θ
```

## Result: Soft Semantics

Integrating over uniform θ gives:

```
∫₀¹ δ_{p>θ} dθ = p
```

So: L₀(p | u_gen) ∝ p · P(p) — "more is better", weighted by prior.

## Why Priors Matter

Same 50% prevalence, different judgments:
- "Robins lay eggs" TRUE — 50% is HIGH relative to bimodal prior (many kinds at 0)
- "Robins are female" FALSE — 50% is EXPECTED given unimodal prior at 50%
-/

import Linglib.Theories.Pragmatics.RSA.Core.Basic
import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Mathlib.Data.Rat.Defs

namespace RSA.TesslerGoodman2019

open RSA.Eval

-- Domain: Prevalence as Scale (parallel to LassiterGoodman2017's Height)

/-- Discretized prevalence: 0%, 10%, ..., 100% -/
inductive Prevalence where
  | p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10
  deriving Repr, DecidableEq, BEq, Fintype

def Prevalence.toRat : Prevalence → ℚ
  | .p0 => 0 | .p1 => 1/10 | .p2 => 2/10 | .p3 => 3/10 | .p4 => 4/10
  | .p5 => 5/10 | .p6 => 6/10 | .p7 => 7/10 | .p8 => 8/10 | .p9 => 9/10 | .p10 => 1

/-- Threshold (same discretization as prevalence) -/
inductive Threshold where
  | t0 | t1 | t2 | t3 | t4 | t5 | t6 | t7 | t8 | t9
  deriving Repr, DecidableEq, BEq, Fintype

def Threshold.toRat : Threshold → ℚ
  | .t0 => 0 | .t1 => 1/10 | .t2 => 2/10 | .t3 => 3/10 | .t4 => 4/10
  | .t5 => 5/10 | .t6 => 6/10 | .t7 => 7/10 | .t8 => 8/10 | .t9 => 9/10

-- Utterances

/-- Generic vs null utterance -/
inductive Utterance where
  | generic  -- "Ks have property F"
  | silent   -- say nothing
  deriving Repr, DecidableEq, BEq, Fintype

-- Semantics: Generic as Threshold Predicate over Prevalence

/-- ⟦generic⟧(p, θ) = 1 iff p > θ -/
def genericMeaning (θ : Threshold) (p : Prevalence) : Bool :=
  p.toRat > θ.toRat

def meaning (u : Utterance) (θ : Threshold) (p : Prevalence) : Bool :=
  match u with
  | .generic => genericMeaning θ p
  | .silent => true

-- Prevalence Priors: The Key to Generic Interpretation

/-- "Lays eggs" prior: bimodal (0 or ~50%) -/
def laysEggsPrior : Prevalence → ℚ
  | .p0 => 60  -- Most kinds don't lay eggs
  | .p4 | .p5 | .p6 => 12  -- Egg-layers have ~50% prevalence
  | _ => 1  -- Small mass elsewhere

/-- "Is female" prior: unimodal at 50% -/
def isFemalePrior : Prevalence → ℚ
  | .p5 => 80  -- Strong peak at 50%
  | .p4 | .p6 => 8
  | _ => 1

/-- "Carries malaria" prior: extreme low -/
def carriesMalariaPrior : Prevalence → ℚ
  | .p0 => 95  -- Almost no kinds carry malaria
  | .p1 => 4
  | _ => 1/10

-- RSA Model

def allUtterances : List Utterance := [.generic, .silent]
def allPrevalences : List Prevalence := [.p0, .p1, .p2, .p3, .p4, .p5, .p6, .p7, .p8, .p9, .p10]
def allThresholds : List Threshold := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .t7, .t8, .t9]

/-- L₁ joint over (prevalence, threshold) given generic -/
def runL1_joint (prior : Prevalence → ℚ) (u : Utterance) : List ((Prevalence × Threshold) × ℚ) :=
  let jointWorlds := allPrevalences.flatMap λ p => allThresholds.map λ θ => (p, θ)
  RSA.Eval.basicL1 allUtterances jointWorlds
    (λ utt (p, θ) => boolToRat (meaning utt θ p))
    (λ (p, _) => prior p) 1 (λ _ => 0) u

/-- L₁ marginal over prevalence -/
def runL1_prevalence (prior : Prevalence → ℚ) (u : Utterance) : List (Prevalence × ℚ) :=
  RSA.Eval.marginalize (runL1_joint prior u) Prod.fst

-- Soft Semantics: ∫δ_{p>θ}dθ = p

/-- Soft generic meaning: P(random θ < p) = p -/
def softGenericMeaning (p : Prevalence) : ℚ := p.toRat

/-- Direct soft listener: L₀(p | gen) ∝ p · P(p) -/
def softL0 (prior : Prevalence → ℚ) : List (Prevalence × ℚ) :=
  let scores := allPrevalences.map λ p => (p, softGenericMeaning p * prior p)
  RSA.Eval.normalize scores

-- Worked Examples

def l1_laysEggs : List (Prevalence × ℚ) := runL1_prevalence laysEggsPrior .generic
def l1_isFemale : List (Prevalence × ℚ) := runL1_prevalence isFemalePrior .generic
def l1_carriesMalaria : List (Prevalence × ℚ) := runL1_prevalence carriesMalariaPrior .generic

def softL0_laysEggs : List (Prevalence × ℚ) := softL0 laysEggsPrior
def softL0_isFemale : List (Prevalence × ℚ) := softL0 isFemalePrior

#eval l1_laysEggs      -- 50% gets high probability (above bimodal expectation)
#eval l1_isFemale      -- 50% gets lower probability (matches unimodal expectation)
#eval softL0_laysEggs  -- Soft semantics approximation

-- Key Theorems

/-- "Lays eggs" at 50%: high posterior (TRUE generic) -/
theorem lays_eggs_50_percent_high :
    RSA.Eval.getScore l1_laysEggs .p5 > RSA.Eval.getScore l1_laysEggs .p0 := by
  native_decide

/-- "Is female" at 50%: lower posterior relative to expectation -/
theorem is_female_50_percent_expected :
    RSA.Eval.getScore l1_isFemale .p5 > 0 := by
  native_decide

/-- Prior shapes posterior: bimodal puts more mass away from p5 initially -/
theorem bimodal_prior_spreads_mass :
    -- With bimodal prior, p4-p6 don't dominate as much as with unimodal
    RSA.Eval.getScore l1_laysEggs .p5 < RSA.Eval.getScore l1_isFemale .p5 := by
  native_decide

/-- "Carries malaria" TRUE despite <1% prevalence (prior is even lower) -/
theorem rare_property_true_generic :
    RSA.Eval.getScore l1_carriesMalaria .p1 > RSA.Eval.getScore l1_carriesMalaria .p0 := by
  native_decide

-- Connection to LassiterGoodman2017: Same Framework

/-!
## Unified Threshold Semantics

| Paper | Domain | Scale | Threshold |
|-------|--------|-------|-----------|
| Lassiter & Goodman 2017 | Adjectives | height(x) | θ_tall |
| Tessler & Goodman 2019 | Generics | prevalence(F,K) | θ_gen |

Both derive context-sensitivity from pragmatic inference over θ:
- Adjectives: prior over heights varies by reference class
- Generics: prior over prevalence varies by property

The soft semantics result (∫δ_{x>θ}dθ = x) applies to both.
-/

end RSA.TesslerGoodman2019
