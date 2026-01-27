/-
# Quantity Domain Fragments

Building blocks for RSA quantity/scalar domains.

## Components

- `Domain n`: A quantity domain with n+1 worlds (0 through n)
- `Utterance`: Scalar utterances (none, some, all)
- `ExtUtterance`: Extended with "most"
- `standard n`: Uniform-prior domain of size n
- `withPrior n p`: Domain with custom prior

## Usage

```lean
-- In your paper replication file:
import Linglib.Fragments.Quantities

def myDomain := Quantity.standard 3

#eval Quantity.l1 myDomain .some_
-- w1, w2 > w3 (scalar implicature)
```

## References

- Goodman, N. D. & Stuhlmüller, A. (2013). Knowledge and implicature.
  Topics in Cognitive Science 5(1): 173-184.
-/

import Linglib.Theories.RSA.Core
import Mathlib.Data.Rat.Defs

namespace Quantity

-- ============================================================================
-- Generic Quantity Domain (Parameterized by size)
-- ============================================================================

/--
A quantity domain with n+1 worlds (0 through n).

Standard scalar semantics:
- "none" true iff count = 0
- "some" true iff count ≥ 1 (weak, includes all)
- "all" true iff count = n
-/
structure Domain (n : Nat) where
  /-- Prior over worlds (defaults to uniform) -/
  prior : Fin (n + 1) → ℚ := fun _ => 1

/-- Scalar utterances for quantity domains -/
inductive Utterance where
  | none_  -- "none of them"
  | some_  -- "some of them" (weak: ≥1)
  | all    -- "all of them"
  deriving Repr, DecidableEq, BEq, Inhabited

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

/-- Build RSA scenario from domain -/
def Domain.toScenario {n : Nat} (d : Domain n) : RSAScenario :=
  RSAScenario.basicBool allUtterances (allWorlds n) (fun w u => meaning n u w) d.prior

-- ============================================================================
-- Convenience Constructors
-- ============================================================================

/-- Standard uniform-prior domain -/
def standard (n : Nat) : Domain n := {}

/-- Domain with custom prior -/
def withPrior (n : Nat) (p : Fin (n + 1) → ℚ) : Domain n := { prior := p }

-- ============================================================================
-- RSA Computations
-- ============================================================================

/-- L0 distribution -/
def l0 {n : Nat} (d : Domain n) (u : Utterance) : List (Fin (n + 1) × ℚ) :=
  RSA.L0 d.toScenario u ()

/-- S1 distribution -/
def s1 {n : Nat} (d : Domain n) (w : Fin (n + 1)) : List (Utterance × ℚ) :=
  RSA.S1 d.toScenario w () ()

/-- L1 distribution -/
def l1 {n : Nat} (d : Domain n) (u : Utterance) : List (Fin (n + 1) × ℚ) :=
  RSA.L1_world d.toScenario u

-- ============================================================================
-- Named World Accessors (for readability)
-- ============================================================================

/-- World where 0 have the property -/
def w0 {n : Nat} : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩

/-- World where 1 has the property -/
def w1 {n : Nat} (h : 1 < n + 1 := by omega) : Fin (n + 1) := ⟨1, h⟩

/-- World where 2 have the property -/
def w2 {n : Nat} (h : 2 < n + 1 := by omega) : Fin (n + 1) := ⟨2, h⟩

/-- World where all n have the property -/
def wAll {n : Nat} : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩

-- ============================================================================
-- Extended Scalar Utterances (with "most")
-- ============================================================================

/-- Extended scalar utterances including "most" -/
inductive ExtUtterance where
  | none_  -- "none of them"
  | some_  -- "some of them"
  | most   -- "most of them" (> half)
  | all    -- "all of them"
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Extended semantics with "most" -/
def extMeaning (n : Nat) : ExtUtterance → Fin (n + 1) → Bool
  | .none_, w => w.val == 0
  | .some_, w => w.val ≥ 1
  | .most,  w => w.val * 2 > n     -- more than half
  | .all,   w => w.val == n

/-- All extended utterances -/
def allExtUtterances : List ExtUtterance := [.none_, .some_, .most, .all]

/-- Extended domain with "most" -/
structure ExtDomain (n : Nat) where
  prior : Fin (n + 1) → ℚ := fun _ => 1

/-- Build RSA scenario from extended domain -/
def ExtDomain.toScenario {n : Nat} (d : ExtDomain n) : RSAScenario :=
  RSAScenario.basicBool allExtUtterances (allWorlds n) (fun w u => extMeaning n u w) d.prior

/-- Standard extended domain -/
def extStandard (n : Nat) : ExtDomain n := {}

-- ============================================================================
-- Examples
-- ============================================================================

-- Build a 3-person domain (like the cookie scenario)
private def threePerson : Domain 3 := standard 3

-- Classic scalar implicature
#eval l1 threePerson .some_
-- w1, w2 have higher prob than w3

#eval s1 threePerson wAll
-- "all" preferred over "some"

-- Larger domain
#eval l1 (standard 5) .some_

-- Extended with "most"
#eval RSA.L1_world (extStandard 5).toScenario ExtUtterance.most

end Quantity
