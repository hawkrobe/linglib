/-
# RSA Quantity Domains

Building blocks for RSA quantity/scalar domains.

## Components

- `Domain n`: A quantity domain with n+1 worlds (0 through n)
- `Utterance`: Scalar utterances (none, some, all)
- `ExtUtterance`: Extended with "most"
- `standard n`: Uniform-prior domain of size n
- `withPrior n p`: Domain with custom prior

## Usage

```lean
import Linglib.Theories.RSA.Domains.Quantities

def myDomain := RSA.Domains.Quantity.standard 3

#eval RSA.Domains.Quantity.l1 myDomain .some_
```

## References

- Goodman, N. D. & Stuhlmüller, A. (2013). Knowledge and implicature.
  Topics in Cognitive Science 5(1): 173-184.
-/

import Linglib.Theories.RSA.Core.Basic
import Linglib.Theories.RSA.Core.Eval
import Linglib.Theories.RSA.Core.ChainComparison
import Linglib.Fragments.English.Determiners
import Mathlib.Data.Rat.Defs

namespace RSA.Domains.Quantity

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

/-- Helper for uniform prior non-negativity -/
private theorem one_nonneg : (0 : ℚ) ≤ 1 := by decide

/-- Build Fintype-based RSA scenario from domain -/
def Domain.toScenarioF {n : Nat} (d : Domain n) : RSAScenario Utterance (Fin (n + 1)) :=
  RSAScenario.basicBool
    (satisfies := fun w u => meaning n u w)
    (prior := d.prior)
    (prior_nonneg := d.prior_nonneg)
    (cost := fun _ => 0)
    (cost_nonneg := fun _ => le_refl 0)
    (utterancePrior := fun _ => 1)
    (utterancePrior_nonneg := fun _ => one_nonneg)

/-- Build Fintype-based RSA scenario from extended domain -/
def ExtDomain.toScenarioF {n : Nat} (d : ExtDomain n) : RSAScenario ExtUtterance (Fin (n + 1)) :=
  RSAScenario.basicBool
    (satisfies := fun w u => extMeaning n u w)
    (prior := d.prior)
    (prior_nonneg := d.prior_nonneg)
    (cost := fun _ => 0)
    (cost_nonneg := fun _ => le_refl 0)
    (utterancePrior := fun _ => 1)
    (utterancePrior_nonneg := fun _ => one_nonneg)

/-- L0 distribution (Fintype) -/
def l0F {n : Nat} (d : Domain n) (u : Utterance) : Option (ExactDist (Fin (n + 1))) :=
  RSA.L0 d.toScenarioF u () () () ()

/-- S1 distribution (Fintype) -/
def s1F {n : Nat} (d : Domain n) (w : Fin (n + 1)) : Option (ExactDist Utterance) :=
  RSA.S1 d.toScenarioF w () () () ()

/-- L1 distribution (Fintype) -/
def l1F {n : Nat} (d : Domain n) (u : Utterance) : Option (ExactDist (Fin (n + 1))) :=
  RSA.L1_world d.toScenarioF u

end RSA.Domains.Quantity

-- ============================================================================
-- VanTiel Quantity Domain (6-word scale)
-- ============================================================================

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

-- ============================================================================
-- GQT Semantics (from Determiners)
-- ============================================================================

/-- GQT meaning from unified entry -/
def gqtMeaning (n : Nat) (m : Utterance) (t : Fin (n + 1)) : Bool :=
  Fragments.English.Determiners.QuantityWord.gqtMeaning n m t

/-- GQT meaning as rational (for RSA) -/
def gqtMeaningRat (n : Nat) (m : Utterance) (t : Fin (n + 1)) : ℚ :=
  Fragments.English.Determiners.QuantityWord.gqtMeaningRat n m t

-- ============================================================================
-- PT Semantics (from Determiners)
-- ============================================================================

/-- PT meaning from unified entry -/
def ptMeaning (n : Nat) (m : Utterance) (t : Fin (n + 1)) : ℚ :=
  Fragments.English.Determiners.QuantityWord.ptMeaning n m t

-- ============================================================================
-- Quantity Domain Structure
-- ============================================================================

/--
A unified quantity domain for VanTiel-style analysis.

This structure bundles:
- A meaning function (GQT or PT style)
- Salience weights for each utterance
- Prior over world states

The domain size n gives worlds 0, 1, ..., n.
-/
structure Domain (n : Nat) where
  /-- Meaning function: truth/compatibility of utterance at world -/
  meaning : Utterance → Fin (n + 1) → ℚ
  /-- Salience/accessibility prior over utterances -/
  salience : Utterance → ℚ := fun _ => 1
  /-- Prior over world states -/
  worldPrior : Fin (n + 1) → ℚ := fun _ => 1
  /-- Non-negativity proofs -/
  meaning_nonneg : ∀ u w, 0 ≤ meaning u w := by intros; decide
  salience_nonneg : ∀ u, 0 ≤ salience u := by intros; decide
  worldPrior_nonneg : ∀ w, 0 ≤ worldPrior w := by intros; decide

/-- All worlds for a domain of size n -/
def allWorlds (n : Nat) : List (Fin (n + 1)) :=
  List.finRange (n + 1)

/-- GQT domain with uniform priors -/
def gqtDomain (n : Nat) : Domain n where
  meaning := gqtMeaningRat n
  meaning_nonneg := fun u w => Fragments.English.Determiners.QuantityWord.gqtMeaningRat_nonneg n u w

/-- PT domain with uniform priors -/
def ptDomain (n : Nat) : Domain n where
  meaning := ptMeaning n
  meaning_nonneg := fun u _ => Fragments.English.Determiners.QuantityWord.ptMeaning_nonneg n u _

/-- GQT domain with custom salience -/
def gqtDomainWithSalience (n : Nat) (salience : Utterance → ℚ)
    (h : ∀ u, 0 ≤ salience u := by intros; decide) : Domain n where
  meaning := gqtMeaningRat n
  salience := salience
  meaning_nonneg := fun u w => Fragments.English.Determiners.QuantityWord.gqtMeaningRat_nonneg n u w
  salience_nonneg := h

/-- PT domain with custom salience -/
def ptDomainWithSalience (n : Nat) (salience : Utterance → ℚ)
    (h : ∀ u, 0 ≤ salience u := by intros; decide) : Domain n where
  meaning := ptMeaning n
  salience := salience
  meaning_nonneg := fun u _ => Fragments.English.Determiners.QuantityWord.ptMeaning_nonneg n u _
  salience_nonneg := h

-- ============================================================================
-- RSA Computations using Domain
-- ============================================================================

-- ============================================================================
-- Base Agents (Level 0)
-- ============================================================================

/-- S0: Literal speaker. P(m | w) ∝ salience(m) · φ(m, w) -/
def Domain.runS0 {n : Nat} (d : Domain n) (w : Fin (n + 1)) : List (Utterance × ℚ) :=
  RSA.Eval.basicS0 allUtterances (allWorlds n) d.meaning d.salience w

/-- L0: Literal listener. P(w | m) ∝ prior(w) · φ(m, w) -/
def Domain.runL0 {n : Nat} (d : Domain n) (u : Utterance) : List (Fin (n + 1) × ℚ) :=
  RSA.Eval.basicL0 allUtterances (allWorlds n) d.meaning d.worldPrior u

-- ============================================================================
-- ChainVariant-Parameterized Methods (Primary API)
-- ============================================================================

/--
Run S1 (pragmatic speaker) using the specified chain variant.

- `.L0Based` (default): L0 → **S1** (speaker reasons about literal listener)
- `.S0Based`: S0 → L1 → **S1** (speaker reasons about pragmatic listener)
-/
def Domain.runS1 {n : Nat} (d : Domain n)
    (chain : RSA.ChainVariant := .L0Based)
    (w : Fin (n + 1)) (α : ℕ := 1) : List (Utterance × ℚ) :=
  RSA.Eval.runS1 allUtterances (allWorlds n) d.meaning d.worldPrior d.salience α (fun _ => 0) chain w

/--
Run L1 (pragmatic listener) using the specified chain variant.

- `.L0Based` (default): L0 → S1 → **L1** (listener reasons about pragmatic speaker)
- `.S0Based`: S0 → **L1** (listener reasons about literal speaker)
-/
def Domain.runL1 {n : Nat} (d : Domain n)
    (chain : RSA.ChainVariant := .L0Based)
    (u : Utterance) (α : ℕ := 1) : List (Fin (n + 1) × ℚ) :=
  RSA.Eval.runL1 allUtterances (allWorlds n) d.meaning d.worldPrior d.salience α (fun _ => 0) chain u

-- ============================================================================
-- Chain Comparison Methods
-- ============================================================================

/--
Compare S1 outputs from S0-based vs L0-based chains.

Returns both distributions and divergence metrics.
-/
def Domain.compareS1 {n : Nat} (d : Domain n) (w : Fin (n + 1))
    (α : ℕ := 1) : RSA.ChainComparison Utterance :=
  { S0Based := d.runS1 .S0Based w α
    L0Based := d.runS1 .L0Based w α }

/--
Compare L1 outputs from S0-based vs L0-based chains.
-/
def Domain.compareL1 {n : Nat} (d : Domain n) (u : Utterance)
    (α : ℕ := 1) : RSA.ChainComparison (Fin (n + 1)) :=
  { S0Based := d.runL1 .S0Based u α
    L0Based := d.runL1 .L0Based u α }

-- ============================================================================
-- Backwards Compatibility Aliases
-- ============================================================================

/-- Run L1 from S0 (S0-based chain). Alias for `runL1 .S0Based`. -/
def Domain.runL1_fromS0 {n : Nat} (d : Domain n) (u : Utterance) : List (Fin (n + 1) × ℚ) :=
  d.runL1 .S0Based u

/-- Run S1 via S0-based chain. Alias for `runS1 .S0Based`. -/
def Domain.runS1_fromL1S0 {n : Nat} (d : Domain n) (w : Fin (n + 1))
    (α : ℕ := 1) : List (Utterance × ℚ) :=
  d.runS1 .S0Based w α

-- ============================================================================
-- RSAScenario Construction
-- ============================================================================

/-- Build RSAScenario from Domain (includes salience as utterancePrior) -/
def Domain.toScenario {n : Nat} (d : Domain n) (α : ℕ := 1) : RSAScenario Utterance (Fin (n + 1)) :=
  RSAScenario.basic
    (φ := d.meaning)
    (φ_nonneg := d.meaning_nonneg)
    (prior := d.worldPrior)
    (prior_nonneg := d.worldPrior_nonneg)
    (α := α)
    (cost := fun _ => 0)
    (cost_nonneg := fun _ => le_refl 0)
    (utterancePrior := d.salience)
    (utterancePrior_nonneg := d.salience_nonneg)

-- ============================================================================
-- Examples
-- ============================================================================

-- GQT domain of size 10
#eval (gqtDomain 10).runS0 ⟨5, by omega⟩
-- Literal speaker at t=5: "some" and "half" should be true

#eval (gqtDomain 10).runS1 (w := ⟨5, by omega⟩)
-- Pragmatic speaker (default: L0-based chain)

#eval (gqtDomain 10).runS1 .S0Based ⟨5, by omega⟩
-- Pragmatic speaker via S0-based chain

#eval (ptDomain 10).runS0 ⟨5, by omega⟩
-- PT literal speaker: graded truth values

-- Compare S0-based vs L0-based chains
#eval (gqtDomain 10).runS1 (w := ⟨5, by omega⟩)        -- default: L0-based
#eval (gqtDomain 10).runS1 .S0Based ⟨5, by omega⟩     -- explicit: S0-based

-- Use comparison helper
#eval (gqtDomain 10).compareS1 ⟨5, by omega⟩
-- Returns both distributions for easy comparison

-- Check divergence
#eval RSA.totalVariation ((gqtDomain 10).compareS1 ⟨5, by omega⟩)
-- Total variation distance between the two chains

end VanTielQuantity
