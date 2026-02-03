/-
# Negation Phenomena

Empirical data: semantic and pragmatic properties of sentential negation.

## Key Properties

1. **Downward Entailing (DE)**: Negation reverses entailment direction
   - "John didn't see an animal" → "John didn't see a dog" (valid)
   - dogs ⊆ animals, but under negation the inference goes from superset to subset

2. **Scalar Implicature Blocking**: DE contexts block "some → not all"
   - "John didn't eat some cookies" ≠ "John didn't eat some but not all cookies"

3. **NPI Licensing**: Negation licenses Negative Polarity Items
   - "John didn't see anyone" (valid)
   - *"John saw anyone" (invalid without negation)

## References

- Ladusaw (1980) on polarity sensitivity
- Chierchia (2004) on scalar implicatures and DE
- Horn (1989) on negation
-/

import Linglib.Phenomena.Core.EmpiricalData

namespace Phenomena.Negation

open Phenomena

-- ============================================================================
-- Negation Inference Judgments
-- ============================================================================

/--
A negation inference test case.
-/
structure NegationInference where
  /-- The premise sentence -/
  premise : String
  /-- The conclusion sentence -/
  conclusion : String
  /-- The set relation licensing the inference -/
  setRelation : String
  /-- Direction of inference (up = subset→superset, down = superset→subset) -/
  direction : String
  /-- Do speakers judge this as valid? -/
  judgedValid : Bool
  /-- Notes on the judgment -/
  notes : String := ""
  deriving Repr

-- ============================================================================
-- DE Property of Negation
-- ============================================================================

/--
Negation is DE: "didn't see animal" → "didn't see dog" (downward valid).

Given: dogs ⊆ animals
If John didn't see any animal, he didn't see any dog.
-/
def negation_de_valid : NegationInference :=
  { premise := "John didn't see an animal"
  , conclusion := "John didn't see a dog"
  , setRelation := "dogs ⊆ animals"
  , direction := "downward"
  , judgedValid := true
  , notes := "DE property: superset to subset is valid under negation"
  }

/--
Negation is NOT UE: "didn't see dog" ↛ "didn't see animal" (upward invalid).

Given: dogs ⊆ animals
John could have not seen a dog but seen a cat (which is an animal).
-/
def negation_not_ue : NegationInference :=
  { premise := "John didn't see a dog"
  , conclusion := "John didn't see an animal"
  , setRelation := "dogs ⊆ animals"
  , direction := "upward"
  , judgedValid := false
  , notes := "NOT UE: subset to superset is invalid under negation"
  }

/--
Double negation restores UE: "didn't not see dog" → "didn't not see animal".

DE ∘ DE = UE (proven in Core.Proposition and Entailment.Polarity)
-/
def double_negation_ue : NegationInference :=
  { premise := "It's not the case that John didn't see a dog"
  , conclusion := "It's not the case that John didn't see an animal"
  , setRelation := "dogs ⊆ animals"
  , direction := "upward"
  , judgedValid := true
  , notes := "DE ∘ DE = UE: double negation restores upward inference"
  }

-- ============================================================================
-- Scalar Implicature Interaction
-- ============================================================================

/--
DE blocks scalar implicature: "didn't eat some" ≠ "didn't eat some but not all".

In UE contexts: "ate some" → "ate some but not all" (SI)
In DE contexts: this implicature is blocked.
-/
structure SIBlockingDatum where
  /-- The sentence in a DE context -/
  sentence : String
  /-- Is the scalar implicature derived? -/
  siDerived : Bool
  /-- Expected meaning without SI -/
  literalMeaning : String
  /-- Expected meaning with SI (if derived) -/
  siMeaning : String
  /-- Notes -/
  notes : String := ""
  deriving Repr

def negation_blocks_si : SIBlockingDatum :=
  { sentence := "John didn't eat some of the cookies"
  , siDerived := false
  , literalMeaning := "John ate none of the cookies OR John ate all of the cookies"
  , siMeaning := "John didn't eat some-but-not-all of the cookies"
  , notes := "DE context blocks 'some → not all' implicature"
  }

def positive_derives_si : SIBlockingDatum :=
  { sentence := "John ate some of the cookies"
  , siDerived := true
  , literalMeaning := "John ate at least one cookie"
  , siMeaning := "John ate some but not all of the cookies"
  , notes := "UE context: SI is derived"
  }

-- ============================================================================
-- NPI Licensing
-- ============================================================================

/--
Negative Polarity Item licensing datum.
-/
structure NPIDatum where
  /-- The sentence with the NPI -/
  sentence : String
  /-- Is it grammatical/acceptable? -/
  acceptable : Bool
  /-- The NPI being tested -/
  npi : String
  /-- The licensing environment -/
  licensor : String
  deriving Repr

def negation_licenses_anyone : NPIDatum :=
  { sentence := "John didn't see anyone"
  , acceptable := true
  , npi := "anyone"
  , licensor := "negation (didn't)"
  }

def no_licensor_anyone : NPIDatum :=
  { sentence := "*John saw anyone"
  , acceptable := false
  , npi := "anyone"
  , licensor := "none"
  }

def negation_licenses_ever : NPIDatum :=
  { sentence := "John hasn't ever been to Paris"
  , acceptable := true
  , npi := "ever"
  , licensor := "negation (hasn't)"
  }

def no_licensor_ever : NPIDatum :=
  { sentence := "*John has ever been to Paris"
  , acceptable := false
  , npi := "ever"
  , licensor := "none"
  }

-- ============================================================================
-- All Data
-- ============================================================================

def allNegationInferences : List NegationInference :=
  [negation_de_valid, negation_not_ue, double_negation_ue]

def allSIBlockingData : List SIBlockingDatum :=
  [negation_blocks_si, positive_derives_si]

def allNPIData : List NPIDatum :=
  [negation_licenses_anyone, no_licensor_anyone,
   negation_licenses_ever, no_licensor_ever]

-- ============================================================================
-- Consistency Checks
-- ============================================================================

/-- Negation should be DE but not UE -/
theorem negation_is_de_not_ue :
    negation_de_valid.judgedValid = true ∧
    negation_not_ue.judgedValid = false := ⟨rfl, rfl⟩

/-- Double negation should restore UE -/
theorem double_negation_restores_ue :
    double_negation_ue.judgedValid = true := rfl

/-- Negation should block SI -/
theorem negation_blocks_scalar_implicature :
    negation_blocks_si.siDerived = false ∧
    positive_derives_si.siDerived = true := ⟨rfl, rfl⟩

/-- Negation should license NPIs -/
theorem negation_licenses_npis :
    negation_licenses_anyone.acceptable = true ∧
    negation_licenses_ever.acceptable = true := ⟨rfl, rfl⟩

end Phenomena.Negation
