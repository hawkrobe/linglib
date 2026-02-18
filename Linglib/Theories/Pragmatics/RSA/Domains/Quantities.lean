/-
# RSA Quantity Domains

Building blocks for RSA quantity/scalar domains.

## Components

- `Utterance`: Scalar utterances (none, some, all)
- `ExtUtterance`: Extended with "most"
- `meaning`: Literal semantics for scalar utterances
- `extMeaning`: Extended semantics with "most"

## References

- Goodman, N. D. & Stuhlmüller, A. (2013). Knowledge and implicature.
  Topics in Cognitive Science 5(1): 173-184.
-/

import Linglib.Fragments.English.Determiners

namespace RSA.Domains.Quantity

-- Generic Quantity Domain (Parameterized by size)

/-- Scalar utterances for quantity domains -/
inductive Utterance where
  | none_  -- "none of them"
  | some_  -- "some of them" (weak: ≥1)
  | all    -- "all of them"
  deriving Repr, DecidableEq, BEq, Inhabited

instance : Fintype Utterance where
  elems := {.none_, .some_, .all}
  complete := λ x => by cases x <;> simp

/-- Literal semantics (weak "some") -/
def meaning (n : Nat) : Utterance → Fin (n + 1) → Bool
  | .none_, w => w.val == 0
  | .some_, w => w.val ≥ 1          -- includes all!
  | .all,   w => w.val == n

/-- All utterances -/
def allUtterances : List Utterance := [.none_, .some_, .all]

/-- All worlds for a domain of size n -/
def allWorlds (n : Nat) : List (Fin (n + 1)) :=
  List.finRange (n + 1)

-- Named World Accessors (for readability)

/-- World where 0 have the property -/
def w0 {n : Nat} : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩

/-- World where 1 has the property -/
def w1 {n : Nat} (h : 1 < n + 1 := by omega) : Fin (n + 1) := ⟨1, h⟩

/-- World where 2 have the property -/
def w2 {n : Nat} (h : 2 < n + 1 := by omega) : Fin (n + 1) := ⟨2, h⟩

/-- World where all n have the property -/
def wAll {n : Nat} : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩

-- Extended Scalar Utterances (with "most")

/-- Extended scalar utterances including "most" -/
inductive ExtUtterance where
  | none_  -- "none of them"
  | some_  -- "some of them"
  | most   -- "most of them" (> half)
  | all    -- "all of them"
  deriving Repr, DecidableEq, BEq, Inhabited

instance : Fintype ExtUtterance where
  elems := {.none_, .some_, .most, .all}
  complete := λ x => by cases x <;> simp

/-- Extended semantics with "most" -/
def extMeaning (n : Nat) : ExtUtterance → Fin (n + 1) → Bool
  | .none_, w => w.val == 0
  | .some_, w => w.val ≥ 1
  | .most,  w => w.val * 2 > n     -- more than half
  | .all,   w => w.val == n

/-- All extended utterances -/
def allExtUtterances : List ExtUtterance := [.none_, .some_, .most, .all]

end RSA.Domains.Quantity

-- VanTiel Quantity Domain (6-word scale)

-- Uses unified QuantityWord from Fragments.English.Determiners

namespace VanTielQuantity

-- Re-export QuantityWord as Utterance for backwards compatibility
open Fragments.English.Determiners in
abbrev Utterance := QuantityWord

-- Re-export Monotonicity
open Fragments.English.Determiners in
abbrev Monotonicity := Fragments.English.Determiners.Monotonicity

def allUtterances : List Utterance := Fragments.English.Determiners.QuantityWord.toList

/-- Get monotonicity from unified entry -/
def monotonicity (u : Utterance) : Monotonicity :=
  Fragments.English.Determiners.QuantityWord.monotonicity u

-- GQT Semantics (from Determiners)

/-- GQT meaning from unified entry -/
def gqtMeaning (n : Nat) (m : Utterance) (t : Fin (n + 1)) : Bool :=
  Fragments.English.Determiners.QuantityWord.gqtMeaning n m t

-- All worlds for a domain of size n
def allWorlds (n : Nat) : List (Fin (n + 1)) :=
  List.finRange (n + 1)

end VanTielQuantity
