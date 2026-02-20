/-
# Égré et al. (2023) — Empirical Data

Theory-neutral empirical observations from "On the optimality of vagueness."

## Phenomena

1. "Around n" produces triangular (tent-shaped) interpretation distributions
2. "Around n" conveys more shape information than "between a and b"
3. Speakers prefer "around n" for peaked private distributions
4. The round/non-round asymmetry affects "around" acceptability
5. Sorites-like tolerance chains for "around"

## References

- Égré, P., Spector, B., Mortier, A., & Verheyen, S. (2023). On the optimality
  of vagueness. Linguistics and Philosophy, 46, 1101–1130.
-/

import Linglib.Phenomena.Gradability.Imprecision.Numerals
import Mathlib.Data.Rat.Defs

namespace Phenomena.Gradability.Imprecision.Studies.EgreEtAl2023

open Phenomena.Gradability.Imprecision.Numerals

/--
Shape inference datum: "around n" vs "between a b" interpretation shape.

The key empirical claim: hearing "around n" leads to a peaked (triangular)
interpretation centered on n, while "between a b" leads to a flat
(uniform) interpretation over [a,b].
-/
structure ShapeInferenceDatum where
  /-- The vague expression -/
  vagueExpression : String
  /-- The precise alternative -/
  preciseAlternative : String
  /-- Center value n -/
  center : Nat
  /-- Does the vague expression produce peaked interpretation? -/
  vagueIsPeaked : Bool
  /-- Does the precise alternative produce peaked interpretation? -/
  preciseIsPeaked : Bool
  /-- Notes -/
  notes : String
  deriving Repr

/--
"Around 20" produces peaked interpretation; "between 10 and 30" does not.

Source: Égré et al. 2023, Sections 5-6, Figure 2 vs Figure 5
-/
def aroundVsBetween : ShapeInferenceDatum :=
  { vagueExpression := "around 20"
  , preciseAlternative := "between 10 and 30"
  , center := 20
  , vagueIsPeaked := true
  , preciseIsPeaked := false
  , notes := "Both cover similar ranges but 'around' conveys triangular shape"
  }

/--
Speaker preference datum: when does a speaker choose "around n"
over "between a b"?
-/
structure SpeakerPreferenceDatum where
  /-- Speaker's private distribution shape -/
  privateDistShape : String
  /-- Preferred message -/
  preferredMessage : String
  /-- Alternative message -/
  alternativeMessage : String
  /-- Why preferred? -/
  reason : String
  deriving Repr

/--
Speakers with peaked beliefs prefer "around n".

Source: Égré et al. 2023, Section 6
-/
def peakedSpeakerPreference : SpeakerPreferenceDatum :=
  { privateDistShape := "Peaked at 20 (e.g., observed 20 ± 2)"
  , preferredMessage := "around 20"
  , alternativeMessage := "between 10 and 30"
  , reason := "KL divergence: 'around 20' posterior is closer to peaked belief than flat 'between' posterior"
  }

/--
Speakers with flat beliefs prefer "between a b".

Source: Égré et al. 2023, Section 6
-/
def flatSpeakerPreference : SpeakerPreferenceDatum :=
  { privateDistShape := "Flat over [10, 30] (equal probability for all values)"
  , preferredMessage := "between 10 and 30"
  , alternativeMessage := "around 20"
  , reason := "'Between' posterior matches flat belief; 'around' posterior is too peaked"
  }

/--
Sorites chain datum for "around".

The sorites for "around n":
  If k is around n, and k' is close to k, then k' is around n.
  Applied repeatedly, this would make 0 "around 100".
-/
structure SoritesAroundDatum where
  /-- Center value -/
  center : Nat
  /-- Step size in chain -/
  stepSize : Nat
  /-- Starting value (clearly "around n") -/
  startValue : Nat
  /-- Ending value (clearly not "around n") -/
  endValue : Nat
  /-- Is each individual step compelling? -/
  individualStepsCompelling : Bool
  /-- Is the conclusion acceptable? -/
  conclusionAcceptable : Bool
  deriving Repr

def soritesAround20 : SoritesAroundDatum :=
  { center := 20
  , stepSize := 1
  , startValue := 20
  , endValue := 0
  , individualStepsCompelling := true
  , conclusionAcceptable := false
  }

/--
LU limitation datum: observations that LU cannot distinguish.

The LU model assigns the same speaker probabilities to observations
with the same support, even when their shapes differ dramatically.
-/
structure LULimitationDatum where
  /-- First observation -/
  observation1 : String
  /-- First observation shape -/
  shape1 : String
  /-- Second observation -/
  observation2 : String
  /-- Second observation shape -/
  shape2 : String
  /-- Same support? -/
  sameSupport : Bool
  /-- LU distinguishes them? -/
  luDistinguishes : Bool
  /-- BIR model distinguishes them? -/
  birDistinguishes : Bool
  deriving Repr

/--
Peaked vs flat distributions with same support: LU fails, BIR succeeds.

Source: Égré et al. 2023, Section 7, Appendix A
-/
def luFailsOnShape : LULimitationDatum :=
  { observation1 := "Peaked at 20 (values 10-30 possible, most near 20)"
  , shape1 := "triangular"
  , observation2 := "Flat over 10-30 (all equally likely)"
  , shape2 := "uniform"
  , sameSupport := true    -- Both have support {10,...,30}
  , luDistinguishes := false  -- LU gives same Sⁿ for both
  , birDistinguishes := true  -- BIR gives different posteriors
  }

/--
Closed-form prediction datum: the triangular posterior formula.

Under uniform priors on x ∈ {0,...,N} and y ∈ {0,...,N}:
  P(x=k | around n) = (n - |n-k| + 1) / (n+1)²
-/
structure ClosedFormDatum where
  /-- Domain maximum N -/
  domainMax : Nat
  /-- Center n -/
  center : Nat
  /-- Value k -/
  value : Nat
  /-- Expected probability (rational) -/
  expectedProb : ℚ
  /-- Notes -/
  notes : String
  deriving Repr

/-- P(x=20 | around 20) under uniform prior on {0,...,40} -/
def closedForm_center : ClosedFormDatum :=
  { domainMax := 40
  , center := 20
  , value := 20
  , expectedProb := 21 / 441  -- (20 - 0 + 1) / (20+1)²
  , notes := "Peak of triangular distribution"
  }

/-- P(x=15 | around 20) under uniform prior on {0,...,40} -/
def closedForm_offset5 : ClosedFormDatum :=
  { domainMax := 40
  , center := 20
  , value := 15
  , expectedProb := 16 / 441  -- (20 - 5 + 1) / (20+1)²
  , notes := "5 units from center, probability drops linearly"
  }

-- Collections

def shapeInferenceData : List ShapeInferenceDatum :=
  [aroundVsBetween]

def speakerPreferenceData : List SpeakerPreferenceDatum :=
  [peakedSpeakerPreference, flatSpeakerPreference]

def soritesData : List SoritesAroundDatum :=
  [soritesAround20]

def luLimitationData : List LULimitationDatum :=
  [luFailsOnShape]

def closedFormData : List ClosedFormDatum :=
  [closedForm_center, closedForm_offset5]

end Phenomena.Gradability.Imprecision.Studies.EgreEtAl2023
