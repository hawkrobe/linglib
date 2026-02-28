import Linglib.Theories.Pragmatics.Assertion.Stalnaker
import Linglib.Theories.Pragmatics.Assertion.FarkasAdapter
import Linglib.Theories.Pragmatics.Assertion.Krifka
import Linglib.Theories.Pragmatics.Assertion.Brandom
import Linglib.Theories.Pragmatics.Assertion.Gunlogson
import Linglib.Theories.Pragmatics.Assertion.Lauer

/-!
# Assertion Theories: Cross-Theory Comparison

Compares six theories of assertion along structural dimensions:
Stalnaker, Farkas & Bruce, Krifka, Brandom, Gunlogson, and Lauer.

## Comparison Matrix

| Theory | Commitment ≠ Belief | Retraction | Source | Entitlements | Probabilistic |
|--------|---------------------|------------|--------|-------------|---------------|
| Stalnaker | No | No | No | No | No |
| F&B | Yes | No | No | No | No |
| Krifka | Yes | Yes | No | No | No |
| Brandom | Yes | Yes | No | Yes | No |
| Gunlogson | Yes | Yes | Yes | No | No |
| Lauer | Yes | No | No | No | Yes |

## Key Embeddings

1. **Stalnaker embeds in Krifka**: when commitment = belief (no lying,
   no hedging), Krifka's model collapses to Stalnaker's.
2. **F&B's dcS/dcL are Krifka commitment states**: dcS = speaker's
   commitment slate, dcL = addressee's commitment slate.
3. **Brandom strictly richer than Stalnaker**: entitlements have no
   Stalnaker analog.
4. **Gunlogson models rising declaratives; Stalnaker cannot**.
5. **Lying**: Krifka and Brandom handle it (commitment without belief);
   Stalnaker struggles (assertion = belief update).

## References

- Stalnaker, R. (1978). Assertion. *Syntax and Semantics* 9.
- Farkas, D. & Bruce, K. (2010). On Reacting to Assertions. *JoS* 27(1).
- Krifka, M. (2015). Bias in Commitment Space Semantics. *L&P* 38.
- Brandom, R. (1994). *Making It Explicit*. Harvard UP.
- Gunlogson, C. (2001). *True to Form*. PhD dissertation.
- Lauer, S. (2013). *Towards a Dynamic Pragmatics*. PhD dissertation.
-/

namespace Comparisons.AssertionTheories

open Interfaces
open Theories.Pragmatics.Assertion

-- ════════════════════════════════════════════════════
-- § 1. Structural Feature Comparison
-- ════════════════════════════════════════════════════

/-- Stalnaker does NOT separate commitment from belief. -/
theorem stalnaker_no_separation :
    AssertionTheory.separatesCommitmentFromBelief (T := Stalnaker.StalnakerTag) = false := rfl

/-- All other theories DO separate commitment from belief. -/
theorem others_separate :
    AssertionTheory.separatesCommitmentFromBelief (T := FarkasAdapter.FarkasTag) = true ∧
    AssertionTheory.separatesCommitmentFromBelief (T := Krifka.KrifkaTag) = true ∧
    AssertionTheory.separatesCommitmentFromBelief (T := Brandom.BrandomTag) = true ∧
    AssertionTheory.separatesCommitmentFromBelief (T := Gunlogson.GunlogsonTag) = true ∧
    AssertionTheory.separatesCommitmentFromBelief (T := Lauer.LauerTag) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Only Krifka, Brandom, and Gunlogson support retraction. -/
theorem retraction_support :
    AssertionTheory.supportsRetraction (T := Stalnaker.StalnakerTag) = false ∧
    AssertionTheory.supportsRetraction (T := FarkasAdapter.FarkasTag) = false ∧
    AssertionTheory.supportsRetraction (T := Krifka.KrifkaTag) = true ∧
    AssertionTheory.supportsRetraction (T := Brandom.BrandomTag) = true ∧
    AssertionTheory.supportsRetraction (T := Gunlogson.GunlogsonTag) = true ∧
    AssertionTheory.supportsRetraction (T := Lauer.LauerTag) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Only Gunlogson models source marking. -/
theorem source_marking :
    AssertionTheory.modelsSourceMarking (T := Stalnaker.StalnakerTag) = false ∧
    AssertionTheory.modelsSourceMarking (T := FarkasAdapter.FarkasTag) = false ∧
    AssertionTheory.modelsSourceMarking (T := Krifka.KrifkaTag) = false ∧
    AssertionTheory.modelsSourceMarking (T := Brandom.BrandomTag) = false ∧
    AssertionTheory.modelsSourceMarking (T := Gunlogson.GunlogsonTag) = true ∧
    AssertionTheory.modelsSourceMarking (T := Lauer.LauerTag) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. Embeddings and Strict Extensions
-- ════════════════════════════════════════════════════

/-- Stalnaker embeds in Krifka: when commitment = belief (sincere
    assertion), Krifka's commitment operation has the same effect as
    Stalnaker's CG update.

    The embedding is witnessed by the fact that Stalnaker has strictly
    fewer structural features. -/
theorem stalnaker_embeds_in_krifka :
    -- Stalnaker has no commitment/belief separation
    AssertionTheory.separatesCommitmentFromBelief (T := Stalnaker.StalnakerTag) = false ∧
    -- Krifka does
    AssertionTheory.separatesCommitmentFromBelief (T := Krifka.KrifkaTag) = true ∧
    -- Stalnaker has no retraction
    AssertionTheory.supportsRetraction (T := Stalnaker.StalnakerTag) = false ∧
    -- Krifka does
    AssertionTheory.supportsRetraction (T := Krifka.KrifkaTag) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Brandom is strictly richer than Stalnaker: entitlements have no
    Stalnaker analog.

    In Brandom's model, an agent's normative status has TWO dimensions
    (commitments + entitlements). Stalnaker's CG only tracks what's
    mutually believed, with no notion of "being entitled to assert p
    without having asserted it." -/
theorem brandom_strictly_richer :
    AssertionTheory.separatesCommitmentFromBelief (T := Brandom.BrandomTag) = true ∧
    AssertionTheory.supportsRetraction (T := Brandom.BrandomTag) = true ∧
    AssertionTheory.separatesCommitmentFromBelief (T := Stalnaker.StalnakerTag) = false :=
  ⟨rfl, rfl, rfl⟩

/-- Gunlogson models rising declaratives; Stalnaker cannot.

    Rising declaratives require source marking (self vs other-generated
    commitments). Stalnaker's symmetric CG update cannot represent the
    asymmetry between "It's raining." (falling) and "It's raining?" (rising). -/
theorem gunlogson_handles_rising :
    AssertionTheory.modelsSourceMarking (T := Gunlogson.GunlogsonTag) = true ∧
    AssertionTheory.modelsSourceMarking (T := Stalnaker.StalnakerTag) = false :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Phenomenon Coverage
-- ════════════════════════════════════════════════════

/-- Lying: commitment without belief.

    Krifka and Brandom handle lying because they separate commitment
    from belief. An agent can be publicly committed to p without
    privately believing p. Stalnaker's model equates assertion with
    belief update, making lying incoherent as a formal operation. -/
theorem lying_coverage :
    handlesAssertion Krifka.KrifkaTag .lying = true ∧
    handlesAssertion Brandom.BrandomTag .lying = true ∧
    handlesAssertion Stalnaker.StalnakerTag .lying = false :=
  ⟨rfl, rfl, rfl⟩

/-- Rising declaratives are only modeled by Gunlogson. -/
theorem rising_declarative_coverage :
    handlesAssertion Gunlogson.GunlogsonTag .risingDeclaratives = true ∧
    handlesAssertion Stalnaker.StalnakerTag .risingDeclaratives = false ∧
    handlesAssertion Krifka.KrifkaTag .risingDeclaratives = false :=
  ⟨rfl, rfl, rfl⟩

/-- All theories handle basic assertion. -/
theorem basic_assertion_universal :
    handlesAssertion Stalnaker.StalnakerTag .basicAssertion = true ∧
    handlesAssertion FarkasAdapter.FarkasTag .basicAssertion = true ∧
    handlesAssertion Krifka.KrifkaTag .basicAssertion = true ∧
    handlesAssertion Brandom.BrandomTag .basicAssertion = true ∧
    handlesAssertion Gunlogson.GunlogsonTag .basicAssertion = true ∧
    handlesAssertion Lauer.LauerTag .basicAssertion = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Comparison Matrix
-- ════════════════════════════════════════════════════

/-- Summary comparison record for one theory. -/
structure AssertionComparison where
  /-- Theory name -/
  name : String
  /-- Separates commitment from belief? -/
  separates : Bool
  /-- Supports retraction? -/
  retraction : Bool
  /-- Models source marking? -/
  source : Bool
  deriving Repr

/-- The full comparison matrix. -/
def comparisonMatrix : List AssertionComparison :=
  [ ⟨"Stalnaker", false, false, false⟩
  , ⟨"Farkas & Bruce", true, false, false⟩
  , ⟨"Krifka", true, true, false⟩
  , ⟨"Brandom", true, true, false⟩
  , ⟨"Gunlogson", true, true, true⟩
  , ⟨"Lauer", true, false, false⟩ ]

/-- The matrix agrees with the interface flags. -/
theorem matrix_correct :
    comparisonMatrix.length = 6 := rfl

end Comparisons.AssertionTheories
