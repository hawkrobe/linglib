/-
# Generics and Habituals: Empirical Patterns

Theory-neutral data about generic and habitual sentences.

## Key Phenomena

1. **Prevalence asymmetries**: Same prevalence, different truth judgments
2. **Rare property generics**: True generics with <1% prevalence
3. **Striking property effect**: Dangerous properties need less prevalence
4. **Habituals**: Individual-level frequency generalizations
5. **Causal generics**: "Smoking causes cancer"

## References

- Carlson, G.N. (1977). Reference to Kinds in English. PhD dissertation.
- Leslie, S.J. (2008). Generics: Cognition and Acquisition. Philosophical Review.
- Prasada, S. & Dillingham, E. (2006). Principled and statistical connections.
- Cimpian, A., Brandone, A., & Gelman, S. (2010). Generic statements require
  little evidence for acceptance but have powerful implications.
- Tessler, M.H. & Goodman, N.D. (2019). The Language of Generalization.
-/

import Mathlib.Data.Rat.Defs

namespace Phenomena.Generics

-- ============================================================================
-- Prevalence Asymmetry Data
-- ============================================================================

/-- A prevalence asymmetry datum: same prevalence, different judgments -/
structure PrevalenceAsymmetry where
  /-- First sentence -/
  sentence1 : String
  /-- Second sentence -/
  sentence2 : String
  /-- Shared prevalence (approximate) -/
  prevalence : ℚ
  /-- Judgment for sentence1 (1 = clearly true, 0 = clearly false) -/
  judgment1 : ℚ
  /-- Judgment for sentence2 -/
  judgment2 : ℚ
  /-- Source -/
  source : String

/-- Classic asymmetry: "lays eggs" vs "is female" (Leslie 2008) -/
def laysEggsVsIsFemale : PrevalenceAsymmetry :=
  { sentence1 := "Robins lay eggs"
  , sentence2 := "Robins are female"
  , prevalence := 1/2  -- Both ~50%
  , judgment1 := 9/10  -- Clearly true
  , judgment2 := 2/10  -- Odd/false
  , source := "Leslie 2008"
  }

/-- "Has a liver" vs "has brown eyes" -/
def hasLiverVsHasBrownEyes : PrevalenceAsymmetry :=
  { sentence1 := "People have a liver"
  , sentence2 := "People have brown eyes"
  , prevalence := 1  -- ~100% vs ~80%
  , judgment1 := 95/100
  , judgment2 := 3/10  -- Odd despite high prevalence
  , source := "Prasada & Dillingham 2006"
  }

-- ============================================================================
-- Rare Property Generics
-- ============================================================================

/-- A rare property generic: true despite very low prevalence -/
structure RarePropertyGeneric where
  sentence : String
  /-- Actual prevalence (very low) -/
  prevalence : ℚ
  /-- Truth judgment (typically high despite low prevalence) -/
  judgment : ℚ
  /-- Why it's accepted (striking, dangerous, etc.) -/
  explanation : String
  source : String

/-- "Mosquitos carry malaria" - classic rare property generic -/
def mosquitosMalaria : RarePropertyGeneric :=
  { sentence := "Mosquitos carry malaria"
  , prevalence := 1/100  -- <1% of mosquitos
  , judgment := 85/100   -- Clearly true
  , explanation := "Dangerous/striking property"
  , source := "Leslie 2008"
  }

/-- "Sharks attack swimmers" -/
def sharksAttack : RarePropertyGeneric :=
  { sentence := "Sharks attack swimmers"
  , prevalence := 1/1000  -- Extremely rare
  , judgment := 8/10
  , explanation := "Dangerous property"
  , source := "Leslie 2008"
  }

/-- "Ticks carry Lyme disease" -/
def ticksLyme : RarePropertyGeneric :=
  { sentence := "Ticks carry Lyme disease"
  , prevalence := 1/50  -- ~2% in endemic areas
  , judgment := 85/100
  , explanation := "Dangerous property"
  , source := "Tessler & Goodman 2019"
  }

/-- "Peacocks have colorful tails" - only males -/
def peacocksTails : RarePropertyGeneric :=
  { sentence := "Peacocks have colorful tails"
  , prevalence := 1/2  -- Only males
  , judgment := 9/10
  , explanation := "Characteristic/striking feature"
  , source := "Leslie 2008"
  }

-- ============================================================================
-- Striking Property Effect
-- ============================================================================

/-- The striking property effect: dangerous/distinctive properties
    require less prevalence for generic acceptance -/
structure StrikingPropertyEffect where
  /-- Neutral property sentence -/
  neutralSentence : String
  neutralPrevalenceNeeded : ℚ
  /-- Striking property sentence -/
  strikingSentence : String
  strikingPrevalenceNeeded : ℚ
  source : String

/-- Comparison: "carry malaria" needs less prevalence than "have wings" -/
def malariaVsWings : StrikingPropertyEffect :=
  { neutralSentence := "Mosquitos have wings"
  , neutralPrevalenceNeeded := 9/10  -- Needs high prevalence
  , strikingSentence := "Mosquitos carry malaria"
  , strikingPrevalenceNeeded := 1/100  -- Accepted at very low prevalence
  , source := "Cimpian et al. 2010"
  }

-- ============================================================================
-- Principled vs Statistical Connections
-- ============================================================================

/-- Prasada & Dillingham's distinction between connection types -/
inductive ConnectionType where
  | principled  -- Part of what it IS to be a K (e.g., having a heart)
  | statistical -- Merely correlated (e.g., having brown eyes)
  deriving Repr, DecidableEq, BEq

/-- A connection type datum -/
structure ConnectionDatum where
  sentence : String
  connectionType : ConnectionType
  /-- Principled connections accepted at lower prevalence -/
  acceptanceThreshold : ℚ
  source : String

def hasHeart : ConnectionDatum :=
  { sentence := "Dogs have a heart"
  , connectionType := .principled
  , acceptanceThreshold := 5/10  -- Accepted even if some lack it
  , source := "Prasada & Dillingham 2006"
  }

def hasBrownFur : ConnectionDatum :=
  { sentence := "Dogs have brown fur"
  , connectionType := .statistical
  , acceptanceThreshold := 8/10  -- Needs higher prevalence
  , source := "Prasada & Dillingham 2006"
  }

-- ============================================================================
-- Habitual Data
-- ============================================================================

/-- A habitual sentence datum -/
structure HabitualDatum where
  sentence : String
  /-- Frequency description -/
  frequency : String
  /-- Acceptance rate -/
  judgment : ℚ
  source : String

/-- "John smokes" requires regular behavior -/
def johnSmokes : HabitualDatum :=
  { sentence := "John smokes"
  , frequency := "regularly (e.g., daily)"
  , judgment := 9/10
  , source := "Carlson 1977"
  }

/-- "John smokes" false for one-time event -/
def johnSmokedOnce : HabitualDatum :=
  { sentence := "John smokes"
  , frequency := "once at a party"
  , judgment := 1/10
  , source := "Carlson 1977"
  }

/-- "John drinks" (alcohol) vs "John drinks" (any liquid) -/
def johnDrinksAmbiguity : HabitualDatum :=
  { sentence := "John drinks"
  , frequency := "habitual alcohol consumption"
  , judgment := 85/100  -- On alcohol reading
  , source := "Carlson 1977"
  }

-- ============================================================================
-- Causal Generics
-- ============================================================================

/-- A causal generic datum -/
structure CausalGenericDatum where
  sentence : String
  /-- Estimated causal power (Cheng 1997) -/
  causalPower : ℚ
  judgment : ℚ
  source : String

/-- "Smoking causes cancer" -/
def smokingCancer : CausalGenericDatum :=
  { sentence := "Smoking causes cancer"
  , causalPower := 15/100  -- ~15% increase in risk
  , judgment := 9/10
  , source := "Tessler & Goodman 2019"
  }

/-- "Birth control pills cause blood clots" -/
def pillsClots : CausalGenericDatum :=
  { sentence := "Birth control pills cause blood clots"
  , causalPower := 1/1000  -- Very rare
  , judgment := 6/10  -- Mixed judgments
  , source := "Tessler & Goodman 2019"
  }

-- ============================================================================
-- Quantifier Contrast Data
-- ============================================================================

/-- Generics vs explicit quantifiers -/
structure QuantifierContrast where
  generic : String
  quantified : String
  /-- Generic judgment -/
  genericJudgment : ℚ
  /-- Quantified judgment -/
  quantifiedJudgment : ℚ
  source : String

/-- "Tigers are striped" vs "All tigers are striped" -/
def tigersStriped : QuantifierContrast :=
  { generic := "Tigers are striped"
  , quantified := "All tigers are striped"
  , genericJudgment := 95/100  -- True
  , quantifiedJudgment := 7/10  -- Slightly lower (albino tigers?)
  , source := "Leslie 2008"
  }

/-- "Ducks lay eggs" vs "All ducks lay eggs" -/
def ducksLay : QuantifierContrast :=
  { generic := "Ducks lay eggs"
  , quantified := "All ducks lay eggs"
  , genericJudgment := 9/10   -- True
  , quantifiedJudgment := 3/10  -- False (males don't)
  , source := "Leslie 2008"
  }

-- ============================================================================
-- Acquisition Data (Cimpian et al. 2010)
-- ============================================================================

/-- Children accept generics with minimal evidence -/
structure AcquisitionDatum where
  /-- The generic tested -/
  sentence : String
  /-- Evidence provided (e.g., "2 out of 4 lorps have purple feathers") -/
  evidence : String
  /-- Child acceptance rate -/
  childAcceptance : ℚ
  /-- Adult acceptance rate -/
  adultAcceptance : ℚ
  source : String

def lorpsPurple : AcquisitionDatum :=
  { sentence := "Lorps have purple feathers"
  , evidence := "2 out of 4 lorps shown have purple feathers"
  , childAcceptance := 7/10  -- Children readily accept
  , adultAcceptance := 5/10  -- Adults more hesitant
  , source := "Cimpian et al. 2010"
  }

-- ============================================================================
-- Theory Desiderata
-- ============================================================================

/-!
## What a Theory of Generics Must Explain

1. **Prevalence asymmetries**: Same % prevalence, different judgments
   - "Robins lay eggs" (TRUE) vs "Robins are female" (FALSE)

2. **Rare property generics**: Acceptance at very low prevalence
   - "Mosquitos carry malaria" (~1%)
   - "Sharks attack swimmers" (~0.1%)

3. **Striking property effect**: Dangerous/distinctive properties
   need less prevalence

4. **Principled vs statistical**: "Has a heart" vs "has brown eyes"

5. **Quantifier contrast**: Generics ≠ universal quantification
   - "Ducks lay eggs" (TRUE) but "All ducks lay eggs" (FALSE)

6. **Habituals**: Individual-level generalizations with frequency sensitivity

7. **Acquisition**: Children accept generics with minimal evidence

## Theoretical Approaches

| Approach | Key Mechanism |
|----------|---------------|
| Tessler & Goodman 2019 | Uncertain threshold + prevalence priors |
| Leslie 2008 | Cognitive default + striking properties |
| Prasada & Dillingham 2006 | Principled vs statistical connections |
| Cohen 1999 | Homogeneity presupposition |
| Nickel 2016 | Normality-based semantics |
-/

end Phenomena.Generics
