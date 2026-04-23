import Mathlib.Data.Fintype.Basic

/-!
# Quantity Domains for Scalar Implicatures

Building blocks for tutorial-style scalar quantity domains used in
scalar-implicature studies (RSA models, EXH models, neo-Gricean
derivations). The canonical 6-element ⟨none, few, some, half, most, all⟩
paradigm now lives in `Phenomena.Quantification.Inventory`; this file
covers the smaller 3- and 4-element domains used as toy tutorial scales.

## Components

- `Utterance`: 3-element scalar utterances (none, some, all)
- `ExtUtterance`: 4-element extension with "most"
- `meaning`: Literal semantics for scalar utterances
- `extMeaning`: Extended semantics with "most"
-/

namespace Phenomena.ScalarImplicatures.QuantityDomain

-- Generic Quantity Domain (Parameterized by size)

/-- Scalar utterances for quantity domains -/
inductive Utterance where
  | none_  -- "none of them"
  | some_  -- "some of them" (weak: ≥1)
  | all    -- "all of them"
  deriving Repr, DecidableEq, Inhabited

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
  deriving Repr, DecidableEq, Inhabited

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

end Phenomena.ScalarImplicatures.QuantityDomain
