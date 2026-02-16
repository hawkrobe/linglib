/-
# RSA Model for Scope Freezing

RSA model showing that "frozen" scope readings can be rescued by world priors.

## Architecture

1. **Phenomena/ScopeFreezing**: Provides examples with observed availability
2. **Grammar** (Minimalism/CCG): Both predict freezing for possessor, double-object, etc.
3. **RSA**: Takes grammar's parse, shows world priors can rescue frozen readings

## The Key Claim

Grammar theories say: frozen = grammatically impossible (categorical)
RSA says: frozen = strongly dispreferred (gradient, rescuable by context)

This module takes the grammar-derived interpretation prior and shows
that strong world priors can override it.
-/

import Linglib.Theories.Pragmatics.RSA.Core.Eval
import Linglib.Theories.Semantics.Scope
import Mathlib.Data.Rat.Defs

namespace RSA.ScopeFreezing

open Semantics.Scope (ScopeConfig)

-- World Model

/-- World state for two-quantifier sentences.
    w0: neither scope true, w1: inverse-only true, w2: both true -/
inductive World where
  | w0 | w1 | w2
  deriving DecidableEq, BEq, Repr, Inhabited

def allWorlds : List World := [.w0, .w1, .w2]

/-- Surface (∃>∀) truth conditions -/
def surfaceTrue : World → Bool
  | .w2 => true | _ => false

/-- Inverse (∀>∃) truth conditions -/
def inverseTrue : World → Bool
  | .w1 | .w2 => true | _ => false

def meaning (s : ScopeConfig) (w : World) : Bool :=
  match s with
  | .surface => surfaceTrue w
  | .inverse => inverseTrue w

-- RSA

inductive Utterance where | target | null
  deriving DecidableEq, BEq, Repr, Inhabited

def allUtterances : List Utterance := [.target, .null]
def allScopes : List ScopeConfig := [.surface, .inverse]

def uttMeaning (s : ScopeConfig) (u : Utterance) (w : World) : Bool :=
  match u with | .null => true | .target => meaning s w

def l1Interp (worldPrior : World → ℚ) (interpPrior : ScopeConfig → ℚ) : List (ScopeConfig × ℚ) :=
  let tuples := allWorlds.flatMap λ w => allScopes.map λ s => (w, s)
  let scores := tuples.map λ (w, s) =>
    let s1 := RSA.Eval.S1 allUtterances allWorlds
      (λ s' _ u' w' => boolToRat (uttMeaning s' u' w'))
      worldPrior (λ _ _ => 1) (λ _ w1 w2 => w1 == w2) (λ _ => 0) 1 w s () () ()
    ((w, s), worldPrior w * interpPrior s * RSA.Eval.getScore s1 .target)
  let normalized := RSA.Eval.normalize scores
  allScopes.map λ s =>
    (s, normalized.filter (λ ((_, s'), _) => s' == s) |>.map (·.2) |> RSA.Eval.sumScores)

def getInverseProb (worldPrior : World → ℚ) (interpPrior : ScopeConfig → ℚ) : ℚ :=
  RSA.Eval.getScore (l1Interp worldPrior interpPrior) .inverse

-- Priors

def uniformWorldPrior : World → ℚ := λ _ => 1

/-- Rescue prior: strongly favor inverse-only world -/
def rescueWorldPrior : World → ℚ
  | .w1 => 99/100 | _ => 1/200

/-!
## Phenomena-Dependent Content

Definitions and theorems that depend on Phenomena types (Availability, Example,
possessor_baseline, possessor_frozen, etc.) have been moved to
`Linglib.Phenomena.Quantification.Bridge_RSA_ScopeFreezing`.

This includes: `interpPriorFromAvailability`, `interpPriorFromExample`,
`baseline`, `frozen`, `grammarInterpPrior`, and all associated theorems.
-/

end RSA.ScopeFreezing
