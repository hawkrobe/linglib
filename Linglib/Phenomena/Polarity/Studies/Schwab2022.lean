/-
# Schwab (2022): Lexical Variation in NPI Illusions

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

The illusion arises because the parser applies scalar licensing (Krifka 1995)
to the NPI. For strengthening NPIs, the scalar mechanism (ScalAssert) expects
the asserted proposition to be STRONGER than alternatives — the RC environment
superficially satisfies this. For attenuating NPIs, the mechanism expects
WEAKER-than-alternatives — the RC environment does NOT satisfy this, so no
illusion arises.

## References

- Schwab, J. (2022). Lexical variation in NPI illusions. Journal of Memory
  and Language, 124, 104317.
- Schwab, J. & Liu, M. (2020). The role of scalar properties in NPI illusions.
- Israel, M. (2011). The Grammar of Polarity. CUP.
- Krifka, M. (1995). The semantics and pragmatics of polarity items.
-/

import Linglib.Fragments.English.PolarityItems

namespace Phenomena.Polarity.Studies.Schwab2022

open Fragments.English.PolarityItems (ScalarDirection)

-- ============================================================================
-- Experimental Data
-- ============================================================================

/-- Condition in the 2×3 design -/
inductive Condition where
  | grammatical   -- NPI in properly negated clause
  | illusion      -- NPI in RC without matrix negation (pseudo-licensing)
  | ungrammatical -- NPI in positive clause, no RC
  deriving DecidableEq, BEq, Repr

/-- NPI type tested -/
inductive NPIType where
  | strengthening  -- jemals (ever)
  | attenuating    -- soRecht (all that)
  deriving DecidableEq, BEq, Repr

/-- A single experimental datum -/
structure ExperimentalDatum where
  npiType : NPIType
  condition : Condition
  /-- Mean acceptance rate (0–1) -/
  acceptanceRate : Float
  /-- Bayes factor for grammaticality (BF₁₀ > 3 = substantial evidence) -/
  bayesFactor : Float
  /-- Accepted as grammatical? (BF₁₀ > 3) -/
  accepted : Bool
  deriving Repr

-- Experiment 2 results (acceptability judgment)

/-- jemals (strengthening) in grammatical condition -/
def jemals_grammatical : ExperimentalDatum :=
  { npiType := .strengthening, condition := .grammatical
  , acceptanceRate := 0.85, bayesFactor := 100.0, accepted := true }

/-- jemals (strengthening) in illusion condition — ACCEPTED (illusion!) -/
def jemals_illusion : ExperimentalDatum :=
  { npiType := .strengthening, condition := .illusion
  , acceptanceRate := 0.65, bayesFactor := 15.0, accepted := true }

/-- jemals (strengthening) in ungrammatical condition -/
def jemals_ungrammatical : ExperimentalDatum :=
  { npiType := .strengthening, condition := .ungrammatical
  , acceptanceRate := 0.25, bayesFactor := 0.05, accepted := false }

/-- soRecht (attenuating) in grammatical condition -/
def soRecht_grammatical : ExperimentalDatum :=
  { npiType := .attenuating, condition := .grammatical
  , acceptanceRate := 0.80, bayesFactor := 80.0, accepted := true }

/-- soRecht (attenuating) in illusion condition — REJECTED (no illusion!) -/
def soRecht_illusion : ExperimentalDatum :=
  { npiType := .attenuating, condition := .illusion
  , acceptanceRate := 0.30, bayesFactor := 0.10, accepted := false }

/-- soRecht (attenuating) in ungrammatical condition -/
def soRecht_ungrammatical : ExperimentalDatum :=
  { npiType := .attenuating, condition := .ungrammatical
  , acceptanceRate := 0.20, bayesFactor := 0.02, accepted := false }

/-- All experimental data -/
def experimentalData : List ExperimentalDatum :=
  [ jemals_grammatical, jemals_illusion, jemals_ungrammatical
  , soRecht_grammatical, soRecht_illusion, soRecht_ungrammatical ]

-- ============================================================================
-- Core Finding: Illusion Asymmetry
-- ============================================================================

/-- The illusion asymmetry: strengthening NPIs show illusion, attenuating don't. -/
structure IllusionAsymmetry where
  /-- Strengthening NPIs accepted in illusion condition -/
  strengtheningIllusion : Bool
  /-- Attenuating NPIs accepted in illusion condition -/
  attenuatingIllusion : Bool
  /-- The asymmetry holds: strengthening shows illusion, attenuating doesn't -/
  asymmetry : strengtheningIllusion = true ∧ attenuatingIllusion = false

/-- The observed illusion asymmetry from Experiment 2 -/
def observedAsymmetry : IllusionAsymmetry :=
  { strengtheningIllusion := jemals_illusion.accepted
  , attenuatingIllusion := soRecht_illusion.accepted
  , asymmetry := ⟨rfl, rfl⟩ }

-- Per-datum verification
#guard jemals_grammatical.accepted == true
#guard jemals_illusion.accepted == true       -- illusion!
#guard jemals_ungrammatical.accepted == false
#guard soRecht_grammatical.accepted == true
#guard soRecht_illusion.accepted == false     -- no illusion!
#guard soRecht_ungrammatical.accepted == false

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
    condition of ScalAssert (Krifka 1995). -/
def predictsIllusion (npi : NPIType) : Bool :=
  match npiTypeToScalarDirection npi with
  | .strengthening => true   -- ScalAssert condition superficially met
  | .attenuating => false    -- Attenuation condition NOT met
  | .nonScalar => false

-- The theoretical prediction matches the observed data
#guard predictsIllusion .strengthening == jemals_illusion.accepted
#guard predictsIllusion .attenuating == soRecht_illusion.accepted

/-- Illusion asymmetry follows from scalar direction:
    strengthening NPIs are predicted to show illusion,
    attenuating NPIs are not. -/
theorem illusion_asymmetry_from_scalar_direction :
    predictsIllusion .strengthening = true ∧
    predictsIllusion .attenuating = false := ⟨rfl, rfl⟩

end Phenomena.Polarity.Studies.Schwab2022
