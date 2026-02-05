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

import Linglib.Theories.RSA.Core.Eval
import Linglib.Theories.TruthConditional.Derivation.Scope
import Linglib.Phenomena.Quantification.ScopeFreezing
import Mathlib.Data.Rat.Defs

namespace RSA.ScopeFreezing

open TruthConditional.Derivation.Scope (ScopeConfig)
open Phenomena.Quantification.ScopeFreezing

-- Interpretation Prior from Grammar Parse

/--
Convert grammatical availability to interpretation prior.

**Key assumption**: Frozen readings get prior ε > 0, not 0.

This encodes the RSA view that "grammatically unavailable" ≠ "impossible",
just "strongly dispreferred." Grammar theories would set ε = 0; RSA sets ε > 0.

This is the core disagreement:
- Grammar: P(frozen reading) = 0 (categorical)
- RSA: P(frozen reading) = ε > 0 (gradient, rescuable)

The rescue theorem below only goes through because ε > 0.
-/
def interpPriorFromAvailability (avail : Availability) (ε : ℚ := 1/100) : ScopeConfig → ℚ
  | .surface => match avail with
      | .ambiguous => 1
      | .surfaceOnly => 1
      | .inverseOnly => ε
  | .inverse => match avail with
      | .ambiguous => 1
      | .surfaceOnly => ε  -- frozen
      | .inverseOnly => 1

/-- Interpretation prior from a freezing example (uses grammar's prediction) -/
def interpPriorFromExample (ex : Example) : ScopeConfig → ℚ :=
  interpPriorFromAvailability ex.observed

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

-- Results with Canonical Examples

/-- Baseline example from phenomena data -/
def baseline := possessor_baseline

/-- Frozen example from phenomena data -/
def frozen := possessor_frozen

#eval baseline.observed  -- ambiguous
#eval frozen.observed    -- surfaceOnly

#eval getInverseProb uniformWorldPrior (interpPriorFromExample baseline)
#eval getInverseProb uniformWorldPrior (interpPriorFromExample frozen)
#eval getInverseProb rescueWorldPrior (interpPriorFromExample frozen)

/-- Baseline: inverse available -/
theorem baseline_inverse_available :
    getInverseProb uniformWorldPrior (interpPriorFromExample baseline) > 1/2 := by
  native_decide

/-- Frozen: grammar suppresses inverse -/
theorem frozen_suppresses_inverse :
    getInverseProb uniformWorldPrior (interpPriorFromExample frozen) < 1/10 := by
  native_decide

/-- Rescue: world prior overrides grammar (requires ε > 0 assumption) -/
theorem rsa_can_rescue_frozen :
    getInverseProb rescueWorldPrior (interpPriorFromExample frozen) > 1/2 := by
  native_decide

/-- With ε = 0 (grammar's view), rescue is impossible -/
def grammarInterpPrior : ScopeConfig → ℚ := interpPriorFromAvailability .surfaceOnly 0

theorem grammar_view_no_rescue :
    getInverseProb rescueWorldPrior grammarInterpPrior = 0 := by
  native_decide

/-! ## Connection to Grammar Theories

Both Minimalism and CCG predict `possessor_frozen.observed = .surfaceOnly`:
- **Minimalism**: DP phase blocks QR (see `Minimalism.Phenomena.Scope.predictsFreezing`)
- **CCG**: Single derivation for possessor DP (see `CCG.Scope.ccgPredictsFreezing`)

RSA takes this grammatical prediction as input (via `interpPriorFromExample`)
and shows that strong world priors can still rescue the frozen reading.

This distinguishes RSA from categorical grammar accounts:
- Grammar: P(inverse | frozen) = 0 (impossible)
- RSA: P(inverse | frozen, strong context) > 0.5 (rescuable)
-/

end RSA.ScopeFreezing
