import Linglib.Phenomena.Assertion.Basic
import Linglib.Theories.Pragmatics.Assertion.Krifka

/-!
# Krifka Bridge: Layered Clause Structure

Connects Krifka's clause-layer analysis to the theory-neutral assertion data.

## Key Predictions

1. **Hedges are JP modifiers**: "I think p" modifies the epistemic status
   (JP layer), reducing it to `weak`.
2. **Oaths are ComP modifiers**: "I swear p" modifies the commitment
   strength (ComP layer), increasing it to `strong`.
3. **JP and ComP are independent**: hedges and oaths can co-occur
   ("I think I swear p" vs "I swear I think p").

## References

- Krifka, M. (2015). Bias in Commitment Space Semantics. *L&P* 38.
-/

namespace Phenomena.Assertion.Bridge.KrifkaLayers

open Theories.Pragmatics.Assertion.Krifka
open Phenomena.Assertion

-- ════════════════════════════════════════════════════
-- § 1. Hedges as JP Modifiers
-- ════════════════════════════════════════════════════

/-- A hedge modifies the JP layer (epistemic status) to `weak`.

    "I think p" = assertion with `epistemicStatus := .weak`.
    The TP content (p) is unchanged; only the JP layer is modified. -/
def hedgeAsJP {W : Type*} (la : LayeredAssertion W) : LayeredAssertion W :=
  { la with epistemicStatus := .weak }

/-- Hedging preserves content (TP is untouched by JP modification). -/
theorem hedge_preserves_content {W : Type*} (la : LayeredAssertion W) :
    (hedgeAsJP la).content = la.content := rfl

/-- Hedging reduces epistemic status to weak. -/
theorem hedge_weakens {W : Type*} (la : LayeredAssertion W) :
    (hedgeAsJP la).epistemicStatus = .weak := rfl

/-- Hedging does not affect commitment strength. -/
theorem hedge_preserves_commitment {W : Type*} (la : LayeredAssertion W) :
    (hedgeAsJP la).commitmentStrength = la.commitmentStrength := rfl

-- ════════════════════════════════════════════════════
-- § 2. Oaths as ComP Modifiers
-- ════════════════════════════════════════════════════

/-- An oath modifies the ComP layer (commitment strength) to `strong`.

    "I swear p" = assertion with `commitmentStrength := .strong`.
    The TP content (p) is unchanged; only the ComP layer is modified. -/
def oathAsComP {W : Type*} (la : LayeredAssertion W) : LayeredAssertion W :=
  { la with commitmentStrength := .strong }

/-- Oaths preserve content (TP is untouched by ComP modification). -/
theorem oath_preserves_content {W : Type*} (la : LayeredAssertion W) :
    (oathAsComP la).content = la.content := rfl

/-- Oaths increase commitment strength to strong. -/
theorem oath_strengthens {W : Type*} (la : LayeredAssertion W) :
    (oathAsComP la).commitmentStrength = .strong := rfl

/-- Oaths do not affect epistemic status. -/
theorem oath_preserves_epistemic {W : Type*} (la : LayeredAssertion W) :
    (oathAsComP la).epistemicStatus = la.epistemicStatus := rfl

-- ════════════════════════════════════════════════════
-- § 3. JP/ComP Independence
-- ════════════════════════════════════════════════════

/-- JP and ComP can co-occur: hedging + oath on the same assertion.

    "I think I swear p": epistemicStatus = weak, commitmentStrength = strong.
    "I swear I think p": same result (layers are independent). -/
def hedgedOath {W : Type*} (la : LayeredAssertion W) : LayeredAssertion W :=
  { la with epistemicStatus := .weak, commitmentStrength := .strong }

/-- Order doesn't matter: hedge(oath(la)) = oath(hedge(la)). -/
theorem jp_comp_commute {W : Type*} (la : LayeredAssertion W) :
    hedgeAsJP (oathAsComP la) = oathAsComP (hedgeAsJP la) := rfl

/-- Hedged oath is weak epistemic + strong commitment. -/
theorem hedged_oath_profile {W : Type*} (la : LayeredAssertion W) :
    (hedgedOath la).epistemicStatus = .weak ∧
    (hedgedOath la).commitmentStrength = .strong :=
  ⟨rfl, rfl⟩

/-- Both modifications preserve TP content. -/
theorem both_preserve_content {W : Type*} (la : LayeredAssertion W) :
    (hedgedOath la).content = la.content := rfl

-- ════════════════════════════════════════════════════
-- § 4. Bridge to Data
-- ════════════════════════════════════════════════════

/-- Hedge data matches JP modification:
    All canonical hedges reduce commitment, and JP → weak is the mechanism. -/
theorem hedge_data_bridge :
    hedgeExamples.all (·.reducesCommitment) = true ∧
    CommitmentStrength.weak.rank < CommitmentStrength.standard.rank :=
  ⟨rfl, by decide⟩

/-- Oath data matches ComP modification:
    All canonical oaths increase commitment, and ComP → strong is the mechanism. -/
theorem oath_data_bridge :
    oathExamples.all (·.increasesCommitment) = true ∧
    CommitmentStrength.strong.rank > CommitmentStrength.standard.rank :=
  ⟨rfl, by decide⟩

end Phenomena.Assertion.Bridge.KrifkaLayers
