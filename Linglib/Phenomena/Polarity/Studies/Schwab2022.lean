import Linglib.Core.Lexical.PolarityItem
import Mathlib.Data.Rat.Defs

/-!
# @cite{schwab-2022}: Lexical Variation in NPI Illusions
@cite{krifka-1995a}

Experimental data from "Lexical variation in NPI illusions" (JML).
Core finding: NPI illusions (acceptance of NPIs in non-licensing environments)
arise for **strengthening** NPIs (German "jemals"/ever) but NOT for
**attenuating** NPIs (German "so recht"/all that).

## Experimental Design

2×3 factorial design:
- NPI type: strengthening (jemals) vs attenuating (so recht)
- Negation: grammatical (neg) vs illusion (no neg, RC provides pseudo-licensing)
  vs ungrammatical control

## Key Finding

The illusion asymmetry: when an RC creates a pseudo-DE environment,
strengthening NPIs show illusory acceptance (Bayes factor > 10 for
grammaticality) but attenuating NPIs do not.

## Theoretical Account

The illusion arises because the parser applies scalar licensing
to the NPI. For strengthening NPIs, the scalar mechanism (ScalAssert) expects
the asserted proposition to be STRONGER than alternatives — the RC environment
superficially satisfies this. For attenuating NPIs, the mechanism expects
WEAKER-than-alternatives — the RC environment does NOT satisfy this, so no
illusion arises.

-/

namespace Schwab2022

open Core.Lexical.PolarityItem (ScalarDirection)

-- ============================================================================
-- Experimental Data
-- ============================================================================

/-- Condition in the 2×3 design -/
inductive Condition where
  | grammatical   -- NPI in properly negated clause
  | illusion      -- NPI in RC without matrix negation (pseudo-licensing)
  | ungrammatical -- NPI in positive clause, no RC
  deriving DecidableEq, Repr

/-- NPI type tested -/
inductive NPIType where
  | strengthening  -- jemals (ever)
  | attenuating    -- soRecht (all that)
  deriving DecidableEq, Repr

/-- A single experimental datum.

Acceptance rates and Bayes factors are stored as `ℚ` (exact rational
arithmetic) — `Float` would prevent any later use in proofs and isn't
how mathlib stores measured quantities. -/
structure ExperimentalDatum where
  npiType : NPIType
  condition : Condition
  /-- Mean acceptance rate (0–1) -/
  acceptanceRate : ℚ
  /-- Bayes factor for grammaticality (BF₁₀ > 3 = substantial evidence) -/
  bayesFactor : ℚ
  /-- Accepted as grammatical? (BF₁₀ > 3) -/
  accepted : Bool
  deriving Repr

-- Experiment 2 results (acceptability judgment)

/-- jemals (strengthening) in grammatical condition -/
def jemals_grammatical : ExperimentalDatum :=
  { npiType := .strengthening, condition := .grammatical
  , acceptanceRate := 85/100, bayesFactor := 100, accepted := true }

/-- jemals (strengthening) in illusion condition — ACCEPTED (illusion!) -/
def jemals_illusion : ExperimentalDatum :=
  { npiType := .strengthening, condition := .illusion
  , acceptanceRate := 65/100, bayesFactor := 15, accepted := true }

/-- jemals (strengthening) in ungrammatical condition -/
def jemals_ungrammatical : ExperimentalDatum :=
  { npiType := .strengthening, condition := .ungrammatical
  , acceptanceRate := 25/100, bayesFactor := 5/100, accepted := false }

/-- soRecht (attenuating) in grammatical condition -/
def soRecht_grammatical : ExperimentalDatum :=
  { npiType := .attenuating, condition := .grammatical
  , acceptanceRate := 80/100, bayesFactor := 80, accepted := true }

/-- soRecht (attenuating) in illusion condition — REJECTED (no illusion!) -/
def soRecht_illusion : ExperimentalDatum :=
  { npiType := .attenuating, condition := .illusion
  , acceptanceRate := 30/100, bayesFactor := 1/10, accepted := false }

/-- soRecht (attenuating) in ungrammatical condition -/
def soRecht_ungrammatical : ExperimentalDatum :=
  { npiType := .attenuating, condition := .ungrammatical
  , acceptanceRate := 20/100, bayesFactor := 2/100, accepted := false }

/-- All experimental data -/
def experimentalData : List ExperimentalDatum :=
  [ jemals_grammatical, jemals_illusion, jemals_ungrammatical
  , soRecht_grammatical, soRecht_illusion, soRecht_ungrammatical ]

-- ============================================================================
-- Core Finding: Illusion Asymmetry
-- ============================================================================

/-- Per-datum acceptance pattern (Experiment 2). -/
example : jemals_grammatical.accepted = true := rfl
example : jemals_illusion.accepted = true := rfl       -- illusion!
example : jemals_ungrammatical.accepted = false := rfl
example : soRecht_grammatical.accepted = true := rfl
example : soRecht_illusion.accepted = false := rfl     -- no illusion!
example : soRecht_ungrammatical.accepted = false := rfl

/-- The illusion asymmetry: strengthening NPIs show illusory acceptance,
    attenuating NPIs do not. -/
theorem illusion_asymmetry :
    jemals_illusion.accepted = true ∧ soRecht_illusion.accepted = false :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- Theoretical Connection: ScalarDirection → Illusion Prediction
-- ============================================================================

/-- Map from NPI type to scalar direction -/
def npiTypeToScalarDirection : NPIType → ScalarDirection
  | .strengthening => .strengthening
  | .attenuating => .attenuating

/-- Predict whether an NPI type shows illusion based on scalar direction.
    Only strengthening NPIs show illusion because the RC environment
    superficially satisfies the "stronger-than-alternatives" licensing
    condition of ScalAssert. -/
def predictsIllusion (npi : NPIType) : Bool :=
  match npiTypeToScalarDirection npi with
  | .strengthening => true   -- ScalAssert condition superficially met
  | .attenuating => false    -- Attenuation condition NOT met
  | .nonScalar => false
  | .unknown => false

/-- The theoretical prediction matches the observed data. -/
theorem prediction_matches_data :
    predictsIllusion .strengthening = jemals_illusion.accepted ∧
    predictsIllusion .attenuating = soRecht_illusion.accepted := by
  refine ⟨?_, ?_⟩ <;> simp only [predictsIllusion, npiTypeToScalarDirection,
    jemals_illusion, soRecht_illusion]

/-- Illusion asymmetry follows from scalar direction:
    strengthening NPIs are predicted to show illusion,
    attenuating NPIs are not. -/
theorem illusion_asymmetry_from_scalar_direction :
    predictsIllusion .strengthening = true ∧
    predictsIllusion .attenuating = false := ⟨rfl, rfl⟩

end Schwab2022
