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

import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval
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
  /-- Prior is non-negative -/
  prior_nonneg : ∀ w, 0 ≤ prior w := by intros; decide

/-- Scalar utterances for quantity domains -/
inductive Utterance where
  | none_  -- "none of them"
  | some_  -- "some of them" (weak: ≥1)
  | all    -- "all of them"
  deriving Repr, DecidableEq, BEq, Inhabited

instance : Fintype Utterance where
  elems := {.none_, .some_, .all}
  complete := fun x => by cases x <;> simp

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

/-- Run L0 for domain using RSA.Eval -/
def Domain.runL0 {n : Nat} (d : Domain n) (u : Utterance) : List (Fin (n + 1) × ℚ) :=
  RSA.Eval.basicL0 allUtterances (allWorlds n)
    (fun u w => boolToRat (meaning n u w)) d.prior u

/-- Run S1 for domain using RSA.Eval -/
def Domain.runS1 {n : Nat} (d : Domain n) (w : Fin (n + 1)) : List (Utterance × ℚ) :=
  RSA.Eval.basicS1 allUtterances (allWorlds n)
    (fun u w => boolToRat (meaning n u w)) d.prior 1 (fun _ => 0) w

/-- Run L1 for domain using RSA.Eval -/
def Domain.runL1 {n : Nat} (d : Domain n) (u : Utterance) : List (Fin (n + 1) × ℚ) :=
  RSA.Eval.basicL1 allUtterances (allWorlds n)
    (fun u w => boolToRat (meaning n u w)) d.prior 1 (fun _ => 0) u

-- ============================================================================
-- Convenience Constructors
-- ============================================================================

/-- Standard uniform-prior domain -/
def standard (n : Nat) : Domain n := {}

/-- Domain with custom prior -/
def withPrior (n : Nat) (p : Fin (n + 1) → ℚ) (hp : ∀ w, 0 ≤ p w := by intros; decide) : Domain n :=
  { prior := p, prior_nonneg := hp }

-- ============================================================================
-- RSA Computations
-- ============================================================================

/-- L0 distribution -/
def l0 {n : Nat} (d : Domain n) (u : Utterance) : List (Fin (n + 1) × ℚ) :=
  d.runL0 u

/-- S1 distribution -/
def s1 {n : Nat} (d : Domain n) (w : Fin (n + 1)) : List (Utterance × ℚ) :=
  d.runS1 w

/-- L1 distribution -/
def l1 {n : Nat} (d : Domain n) (u : Utterance) : List (Fin (n + 1) × ℚ) :=
  d.runL1 u

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

instance : Fintype ExtUtterance where
  elems := {.none_, .some_, .most, .all}
  complete := fun x => by cases x <;> simp

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
  prior_nonneg : ∀ w, 0 ≤ prior w := by intros; decide

/-- Run L1 for extended domain using RSA.Eval -/
def ExtDomain.runL1 {n : Nat} (d : ExtDomain n) (u : ExtUtterance) : List (Fin (n + 1) × ℚ) :=
  RSA.Eval.basicL1 allExtUtterances (allWorlds n)
    (fun u w => boolToRat (extMeaning n u w)) d.prior 1 (fun _ => 0) u

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
#eval (extStandard 5).runL1 ExtUtterance.most

-- ============================================================================
-- Fintype-Based API (RSAScenario / RSA)
-- ============================================================================

/-- Build Fintype-based RSA scenario from domain -/
def Domain.toScenarioF {n : Nat} (d : Domain n) : RSAScenario :=
  RSAScenario.basicBool
    (U := Utterance)
    (W := Fin (n + 1))
    (satisfies := fun w u => meaning n u w)
    (prior := d.prior)
    (prior_nonneg := d.prior_nonneg)
    (cost := fun _ => 0)
    (cost_nonneg := fun _ => le_refl 0)

/-- Build Fintype-based RSA scenario from extended domain -/
def ExtDomain.toScenarioF {n : Nat} (d : ExtDomain n) : RSAScenario :=
  RSAScenario.basicBool
    (U := ExtUtterance)
    (W := Fin (n + 1))
    (satisfies := fun w u => extMeaning n u w)
    (prior := d.prior)
    (prior_nonneg := d.prior_nonneg)
    (cost := fun _ => 0)
    (cost_nonneg := fun _ => le_refl 0)

/-- L0 distribution (Fintype) -/
def l0F {n : Nat} (d : Domain n) (u : Utterance) : Option (ExactDist (Fin (n + 1))) :=
  RSA.L0 d.toScenarioF u () () () ()

/-- S1 distribution (Fintype) -/
def s1F {n : Nat} (d : Domain n) (w : Fin (n + 1)) : Option (ExactDist Utterance) :=
  RSA.S1 d.toScenarioF w () () () ()

/-- L1 distribution (Fintype) -/
def l1F {n : Nat} (d : Domain n) (u : Utterance) : Option (ExactDist (Fin (n + 1))) :=
  RSA.L1_world d.toScenarioF u

end Quantity
