import Linglib.Theories.Semantics.Montague.Scope
import Mathlib.Data.Rat.Defs

/-!
# RSA Model for Scope Freezing

RSA model showing that "frozen" scope readings can be rescued by world priors.

## Architecture

1. **Phenomena/ScopeFreezing**: Provides examples with observed availability
2. **Grammar** (Minimalism/CCG): Both predict freezing for possessor, double-object, etc.
3. **RSA**: Takes grammar's parse, shows world priors can rescue frozen readings

## The Key Claim

Grammar theories say: frozen = grammatically impossible (categorical)
RSA says: frozen = strongly dispreferred (gradient, rescuable by context)

This module provides the domain types and meaning functions for the
scope freezing RSA model.
-/

namespace RSA.ScopeFreezing

open Semantics.Scope (ScopeConfig)

-- World Model

/-- World state for two-quantifier sentences.
    w0: neither scope true, w1: inverse-only true, w2: both true -/
inductive World where
  | w0 | w1 | w2
  deriving DecidableEq, BEq, Repr, Inhabited

def allWorlds : List World := [.w0, .w1, .w2]

/-- Surface (exists>forall) truth conditions -/
def surfaceTrue : World → Bool
  | .w2 => true | _ => false

/-- Inverse (forall>exists) truth conditions -/
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

-- Priors

def uniformWorldPrior : World → ℚ := λ _ => 1

/-- Rescue prior: strongly favor inverse-only world -/
def rescueWorldPrior : World → ℚ
  | .w1 => 99/100 | _ => 1/200

/-!
## Phenomena-Dependent Content

Definitions and theorems that depend on Phenomena types (Availability, Example,
possessor_baseline, possessor_frozen, etc.) have been moved to
`Linglib.Phenomena.Quantification.RSA_ScopeFreezingBridge`.

This includes: `interpPriorFromAvailability`, `interpPriorFromExample`,
`baseline`, `frozen`, `grammarInterpPrior`, and all associated theorems.
-/

end RSA.ScopeFreezing
