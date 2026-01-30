/-
# Scope Ambiguity Fragments

Building blocks for RSA scope ambiguity scenarios.

## Components

- `Outcome n`: World with n entities satisfying the predicate
- `ScopeReading`: Surface vs inverse scope interpretations
- `ScopeScenario`: Builder for ambiguous scope RSA scenarios

## The Pattern

Scope ambiguity involves:
1. **Worlds**: How many entities satisfy the predicate (0..n)
2. **Interpretations**: Which scope reading (surface vs inverse)
3. **Meaning**: Truth conditions vary by interpretation

Example: "Every horse didn't jump"
- Surface (∀>¬): "No horse jumped" - true only at w0
- Inverse (¬>∀): "Not every horse jumped" - true at w0, w1, ..., w(n-1)

## Usage

```lean
import Linglib.Fragments.Scope

-- "Every X didn't VP" with 3 entities
def scenario := Scope.everyNotScenario 3

#eval RSAL.L1_world scenario .everyNot
-- Infers both world and interpretation
```

## References

- Scontras, G. & Pearl, L. (2021). When pragmatics matters more for
  truth-value judgments.
- May, R. (1985). Logical Form: Its Structure and Derivation.
-/

import Linglib.Theories.RSA.Core.Eval
import Linglib.Theories.Montague.Derivation.Scope
import Mathlib.Data.Rat.Defs

namespace Scope

open Montague.Derivation.Scope (ScopeConfig)

-- ============================================================================
-- Outcome Worlds
-- ============================================================================

/--
Outcome world: n out of total entities satisfy the predicate.

For "Every horse didn't jump" with 3 horses:
- w0: 0 horses jumped
- w1: 1 horse jumped
- w2: 2 horses jumped
- w3: all 3 horses jumped
-/
structure Outcome (total : Nat) where
  count : Fin (total + 1)
  deriving Repr, DecidableEq, BEq

instance {n : Nat} : Inhabited (Outcome n) := ⟨⟨0, Nat.zero_lt_succ n⟩⟩

/-- All outcome worlds -/
def allOutcomes (n : Nat) : List (Outcome n) :=
  List.finRange (n + 1) |>.map (⟨·⟩)

/-- Named constructors for common cases -/
def Outcome.none (n : Nat) : Outcome n := ⟨0, Nat.zero_lt_succ n⟩
def Outcome.all (n : Nat) : Outcome n := ⟨n, Nat.lt_succ_self n⟩
def Outcome.some (n : Nat) (k : Nat) (h : k < n + 1 := by omega) : Outcome n := ⟨⟨k, h⟩⟩

-- ============================================================================
-- Scope Readings (re-export from Montague)
-- ============================================================================

/-- Scope reading: surface or inverse -/
abbrev Reading := ScopeConfig

def surface : Reading := .surface
def inverse : Reading := .inverse

def allReadings : List Reading := [.surface, .inverse]

-- ============================================================================
-- Quantifier-Negation Scope Semantics
-- ============================================================================

/--
Truth conditions for "Every X didn't VP" under different scope readings.

- Surface (∀>¬): "For every X, X didn't VP" = none VP'd
- Inverse (¬>∀): "Not every X VP'd" = at least one didn't VP
-/
def everyNotMeaning (n : Nat) (reading : Reading) (w : Outcome n) : Bool :=
  match reading with
  | .surface => w.count.val == 0        -- ∀>¬: none VP'd
  | .inverse => w.count.val < n         -- ¬>∀: not all VP'd

/--
Truth conditions for "Some X didn't VP" under different scope readings.

- Surface (∃>¬): "Some X didn't VP" = at least one didn't
- Inverse (¬>∃): "It's not the case that some X VP'd" = none VP'd
-/
def someNotMeaning (n : Nat) (reading : Reading) (w : Outcome n) : Bool :=
  match reading with
  | .surface => w.count.val < n         -- ∃>¬: some didn't
  | .inverse => w.count.val == 0        -- ¬>∃: none VP'd

-- ============================================================================
-- Utterances
-- ============================================================================

/-- Standard scope-ambiguous utterances -/
inductive ScopeUtt where
  | everyNot   -- "Every X didn't VP"
  | someNot    -- "Some X didn't VP"
  | null       -- Silence (always true baseline)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Combined meaning for scope utterances -/
def scopeMeaning (n : Nat) (reading : Reading) (w : Outcome n) : ScopeUtt → Bool
  | .everyNot => everyNotMeaning n reading w
  | .someNot => someNotMeaning n reading w
  | .null => true

-- ============================================================================
-- Scenario Builders
-- ============================================================================

/--
Run L1 inference for "Every X didn't VP" with n entities.

Returns joint distribution over (Outcome, Reading) pairs.
-/
def everyNotL1 (n : Nat) (u : ScopeUtt) : List ((Outcome n × Reading) × ℚ) :=
  let jointWorlds := (allOutcomes n).flatMap fun w => allReadings.map fun r => (w, r)
  RSA.Eval.basicL1
    [ScopeUtt.everyNot, .null]
    jointWorlds
    (fun utt (w, reading) => boolToRat (scopeMeaning n reading w utt))
    (fun _ => 1) 1 (fun _ => 0) u

/--
Run L1 inference for full scope scenario with both "every...not" and "some...not".
-/
def fullL1 (n : Nat) (u : ScopeUtt) : List ((Outcome n × Reading) × ℚ) :=
  let jointWorlds := (allOutcomes n).flatMap fun w => allReadings.map fun r => (w, r)
  RSA.Eval.basicL1
    [ScopeUtt.everyNot, .someNot, .null]
    jointWorlds
    (fun utt (w, reading) => boolToRat (scopeMeaning n reading w utt))
    (fun _ => 1) 1 (fun _ => 0) u

/--
Generic scope scenario runner.

Takes a custom meaning function for flexibility.
-/
def runL1 {U : Type} [BEq U] [DecidableEq U]
    (utterances : List U)
    (n : Nat)
    (meaning : Reading → Outcome n → U → Bool)
    (worldPrior : Outcome n → ℚ := fun _ => 1)
    (readingPrior : Reading → ℚ := fun _ => 1)
    (u : U)
    : List ((Outcome n × Reading) × ℚ) :=
  let jointWorlds := (allOutcomes n).flatMap fun w => allReadings.map fun r => (w, r)
  RSA.Eval.basicL1 utterances jointWorlds
    (fun utt (w, reading) => boolToRat (meaning reading w utt))
    (fun (w, r) => worldPrior w * readingPrior r) 1 (fun _ => 0) u

-- ============================================================================
-- Convenience: RSA Computations
-- ============================================================================

/-- L1 marginal over worlds -/
def l1_world (n : Nat) (u : ScopeUtt) : List (Outcome n × ℚ) :=
  let joint := everyNotL1 n u
  RSA.Eval.marginalize joint Prod.fst

/-- L1 marginal over interpretations -/
def l1_interp (n : Nat) (u : ScopeUtt) : List (Reading × ℚ) :=
  let joint := everyNotL1 n u
  RSA.Eval.marginalize joint Prod.snd

-- ============================================================================
-- Examples
-- ============================================================================

-- "Every horse didn't jump" with 3 horses
#eval l1_world 3 .everyNot
-- Expect: w0 highest (only surface-true world)

#eval l1_interp 3 .everyNot
-- Expect: inverse has some probability (partial worlds possible)

-- Truth conditions check
#eval everyNotMeaning 3 .surface (Outcome.none 3)  -- true
#eval everyNotMeaning 3 .surface (Outcome.some 3 1)  -- false
#eval everyNotMeaning 3 .inverse (Outcome.some 3 1)  -- true

end Scope
