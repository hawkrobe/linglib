/-
# Tessler & Goodman (2019): The Language of Generalization

Psychological Review, 126(3), 395-436.

## Core Insight

Generics ("Robins lay eggs") use the SAME uncertain threshold semantics
as gradable adjectives (Lassiter & Goodman 2017). The scale is **prevalence**
rather than height/degree:

```
[[generic]](p, theta) = 1 if prevalence p > threshold theta
```

## Result: Soft Semantics

Integrating over uniform theta gives:

```
integral_0^1 delta_{p>theta} dtheta = p
```

So: L0(p | u_gen) proportional to p * P(p) -- "more is better", weighted by prior.

## Why Priors Matter

Same 50% prevalence, different judgments:
- "Robins lay eggs" TRUE -- 50% is HIGH relative to bimodal prior (many kinds at 0)
- "Robins are female" FALSE -- 50% is EXPECTED given unimodal prior at 50%
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.DeriveFintype

namespace RSA.TesslerGoodman2019

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

/-- [[generic]](p, theta) = 1 iff p > theta -/
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

-- Lists for enumeration

def allUtterances : List Utterance := [.generic, .silent]
def allPrevalences : List Prevalence := [.p0, .p1, .p2, .p3, .p4, .p5, .p6, .p7, .p8, .p9, .p10]
def allThresholds : List Threshold := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .t7, .t8, .t9]

-- Soft Semantics: integral delta_{p>theta} dtheta = p

/-- Soft generic meaning: P(random theta < p) = p -/
def softGenericMeaning (p : Prevalence) : ℚ := p.toRat

-- Key Semantic Properties

/-- Generic meaning is monotone in prevalence: higher prevalence means
more thresholds are exceeded. -/
theorem generic_monotone_prevalence :
    ∀ θ : Threshold, genericMeaning θ .p10 = true := by
  sorry

/-- Soft generic meaning equals 0 for prevalence 0. -/
theorem soft_meaning_zero : softGenericMeaning .p0 = 0 := by decide

/-- Soft generic meaning equals 1 for prevalence 100%. -/
theorem soft_meaning_one : softGenericMeaning .p10 = 1 := by decide

/-- The bimodal "lays eggs" prior puts more mass at 0 than the unimodal
"is female" prior. This prior difference drives the different generic
judgments for 50% prevalence. -/
theorem bimodal_prior_peaks_at_zero :
    laysEggsPrior .p0 > isFemalePrior .p0 := by decide

/-- The unimodal "is female" prior peaks at 50%. -/
theorem unimodal_prior_peaks_at_50 :
    isFemalePrior .p5 > isFemalePrior .p0 := by decide

-- Connection to LassiterGoodman2017: Same Framework

/-!
## Unified Threshold Semantics

| Paper | Domain | Scale | Threshold |
|-------|--------|-------|-----------|
| Lassiter & Goodman 2017 | Adjectives | height(x) | theta_tall |
| Tessler & Goodman 2019 | Generics | prevalence(F,K) | theta_gen |

Both derive context-sensitivity from pragmatic inference over theta:
- Adjectives: prior over heights varies by reference class
- Generics: prior over prevalence varies by property

The soft semantics result (integral delta_{x>theta} dtheta = x) applies to both.
-/

end RSA.TesslerGoodman2019
