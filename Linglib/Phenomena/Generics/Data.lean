/-
# Generics and Habituals: Empirical Patterns

Theory-neutral data about generic and habitual sentences, including prevalence asymmetries, rare property generics, striking property effects, habituals, and causal generics.

## Main definitions

`PrevalenceAsymmetry`, `RarePropertyGeneric`, `StrikingPropertyEffect`, `PrincipledSubtype`, `ConnectionType`, `ConnectionDatum`, `HabitualDatum`, `CausalGenericDatum`, `QuantifierContrast`, `AcquisitionDatum`

-/

import Mathlib.Data.Rat.Defs

namespace Phenomena.Generics

-- Prevalence Asymmetry Data

/-- Same prevalence, different truth judgments. -/
structure PrevalenceAsymmetry where
  sentence1 : String
  sentence2 : String
  prevalence : ℚ
  judgment1 : ℚ
  judgment2 : ℚ
  source : String

/-- Classic asymmetry: "lays eggs" vs "is female" -/
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

-- Rare Property Generics

/-- True generic despite very low prevalence. -/
structure RarePropertyGeneric where
  sentence : String
  prevalence : ℚ
  judgment : ℚ
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

-- Striking Property Effect

/-- Dangerous/distinctive properties require less prevalence for generic acceptance. -/
structure StrikingPropertyEffect where
  neutralSentence : String
  neutralPrevalenceNeeded : ℚ
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

-- Principled vs Statistical Connections
-- @cite{prasada-dillingham-2006} @cite{prasada-2013}

/-- Subtypes of principled connections (@cite{prasada-2013}).

    Principled connections link a kind to a property via an explanatory
    relation — one can say *why* members have the property. The three
    subtypes differ in their tolerance for exceptions:

    - **formal**: definitional/analytic ("Triangles have three sides").
      Zero exceptions tolerated.
    - **constitutive**: proper physical makeup ("Dogs have four legs").
      Few exceptions tolerated (birth defects, injury).
    - **causal**: causal mechanism ("Mosquitos carry malaria").
      Many exceptions tolerated — the mechanism exists even if
      rarely manifested. -/
inductive PrincipledSubtype where
  | formal        -- Definitional/analytic (zero exceptions)
  | constitutive  -- Proper physical makeup (few exceptions)
  | causal        -- Causal mechanism (many exceptions)
  deriving Repr, DecidableEq, BEq

/-- Kind–property connection type (@cite{prasada-dillingham-2006}, @cite{prasada-2013}).

    Principled connections support "bare" generics at any prevalence
    because the explanatory relation licenses the generalization.
    Statistical connections require high prevalence — there is no
    explanatory "why", just observed frequency. -/
inductive ConnectionType where
  | principled (sub : PrincipledSubtype)
  | statistical
  deriving Repr, DecidableEq, BEq

/-- Connection type datum. -/
structure ConnectionDatum where
  sentence : String
  connectionType : ConnectionType
  toleratesExceptions : Bool
  acceptanceThreshold : ℚ
  source : String

/-- "Triangles have three sides" — formal/definitional connection. -/
def trianglesSides : ConnectionDatum :=
  { sentence := "Triangles have three sides"
  , connectionType := .principled .formal
  , toleratesExceptions := false
  , acceptanceThreshold := 0  -- True at any prevalence (analytic)
  , source := "Prasada & Dillingham 2006"
  }

/-- "Dogs have a heart" — constitutive connection. -/
def hasHeart : ConnectionDatum :=
  { sentence := "Dogs have a heart"
  , connectionType := .principled .constitutive
  , toleratesExceptions := true
  , acceptanceThreshold := 5/10  -- Accepted even if some lack it
  , source := "Prasada & Dillingham 2006"
  }

/-- "Mosquitos carry malaria" — causal connection. -/
def mosquitosMalariaCxn : ConnectionDatum :=
  { sentence := "Mosquitos carry malaria"
  , connectionType := .principled .causal
  , toleratesExceptions := true
  , acceptanceThreshold := 1/100  -- Accepted at very low prevalence
  , source := "Prasada & Dillingham 2006"
  }

/-- "Dogs have brown fur" — statistical connection. -/
def hasBrownFur : ConnectionDatum :=
  { sentence := "Dogs have brown fur"
  , connectionType := .statistical
  , toleratesExceptions := true
  , acceptanceThreshold := 8/10  -- Needs higher prevalence
  , source := "Prasada & Dillingham 2006"
  }

/-- Principled connections have lower acceptance thresholds than statistical. -/
theorem principled_lower_threshold :
    hasHeart.acceptanceThreshold < hasBrownFur.acceptanceThreshold ∧
    mosquitosMalariaCxn.acceptanceThreshold < hasBrownFur.acceptanceThreshold ∧
    trianglesSides.acceptanceThreshold < hasHeart.acceptanceThreshold := by
  native_decide

/-- Formal connections tolerate no exceptions; others do. -/
theorem formal_no_exceptions :
    trianglesSides.toleratesExceptions = false ∧
    hasHeart.toleratesExceptions = true ∧
    mosquitosMalariaCxn.toleratesExceptions = true ∧
    hasBrownFur.toleratesExceptions = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- All connection data entries. -/
def connectionData : List ConnectionDatum :=
  [trianglesSides, hasHeart, mosquitosMalariaCxn, hasBrownFur]

/-- Acceptance thresholds decrease as connection strength increases:
    formal < constitutive < causal < statistical. -/
theorem threshold_ordering :
    trianglesSides.acceptanceThreshold <
    hasHeart.acceptanceThreshold ∧
    hasHeart.acceptanceThreshold >
    mosquitosMalariaCxn.acceptanceThreshold ∧
    mosquitosMalariaCxn.acceptanceThreshold <
    hasBrownFur.acceptanceThreshold := by
  native_decide

-- Habitual Data

/-- Habitual sentence datum. -/
structure HabitualDatum where
  sentence : String
  frequency : String
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

-- Causal Generics

/-- Causal generic datum. -/
structure CausalGenericDatum where
  sentence : String
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

-- Quantifier Contrast Data

/-- Generics vs explicit quantifiers. -/
structure QuantifierContrast where
  generic : String
  quantified : String
  genericJudgment : ℚ
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

-- Acquisition Data (@cite{cimpian-brandone-gelman-2010})

/-- Child generic acceptance with minimal evidence. -/
structure AcquisitionDatum where
  sentence : String
  evidence : String
  childAcceptance : ℚ
  adultAcceptance : ℚ
  source : String

def lorpsPurple : AcquisitionDatum :=
  { sentence := "Lorps have purple feathers"
  , evidence := "2 out of 4 lorps shown have purple feathers"
  , childAcceptance := 7/10  -- Children readily accept
  , adultAcceptance := 5/10  -- Adults more hesitant
  , source := "Cimpian et al. 2010"
  }


end Phenomena.Generics
