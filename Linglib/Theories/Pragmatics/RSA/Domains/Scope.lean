/-
# Scope Ambiguity Fragments

Building blocks for RSA scope ambiguity scenarios.

## Components

- `Outcome n`: World with n entities satisfying the predicate
- `ScopeReading`: Surface vs inverse scope interpretations
- `scopeMeaning`: Truth conditions under different readings

## The Pattern

Scope ambiguity involves:
1. **Worlds**: How many entities satisfy the predicate (0..n)
2. **Interpretations**: Which scope reading (surface vs inverse)
3. **Meaning**: Truth conditions vary by interpretation

Example: "Every horse didn't jump"
- Surface (forall > not): "No horse jumped" - true only at w0
- Inverse (not > forall): "Not every horse jumped" - true at w0, w1, ..., w(n-1)

## References

- Scontras, G. & Pearl, L. (2021). When pragmatics matters more for
  truth-value judgments.
- May, R. (1985). Logical Form: Its Structure and Derivation.
-/

import Linglib.Theories.Semantics.Montague.Scope

namespace RSA.Domains.Scope

open Semantics.Scope (ScopeConfig)

-- Outcome Worlds

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

-- Scope Readings (re-export from Montague)

/-- Scope reading: surface or inverse -/
abbrev Reading := ScopeConfig

def surface : Reading := .surface
def inverse : Reading := .inverse

def allReadings : List Reading := [.surface, .inverse]

-- Quantifier-Negation Scope Semantics

/--
Truth conditions for "Every X didn't VP" under different scope readings.

- Surface (forall > not): "For every X, X didn't VP" = none VP'd
- Inverse (not > forall): "Not every X VP'd" = at least one didn't VP
-/
def everyNotMeaning (n : Nat) (reading : Reading) (w : Outcome n) : Bool :=
  match reading with
  | .surface => w.count.val == 0        -- forall > not: none VP'd
  | .inverse => w.count.val < n         -- not > forall: not all VP'd

/--
Truth conditions for "Some X didn't VP" under different scope readings.

- Surface (exists > not): "Some X didn't VP" = at least one didn't
- Inverse (not > exists): "It's not the case that some X VP'd" = none VP'd
-/
def someNotMeaning (n : Nat) (reading : Reading) (w : Outcome n) : Bool :=
  match reading with
  | .surface => w.count.val < n         -- exists > not: some didn't
  | .inverse => w.count.val == 0        -- not > exists: none VP'd

-- Utterances

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

end RSA.Domains.Scope
