import Linglib.Features.NounCategorization.Basic

/-!
# Western Armenian noun-categorization parameters

Western Armenian numerals combine directly with bare nouns (*yergu dəgha vaze-ts* 'two boys
ran') as well as with plural nouns, so its classifiers are non-obligatory; plural nouns are
incompatible with classifiers. The numeral-classifier type is retained so that cross-language
consumers can filter on it, although with no obligatory classifier and an empty inventory the
language arguably has no classifier system in Aikhenvald's sense.

## References

* [bale-khanjian-2014], (10) and fn. 3
* [bale-khanjian-2008]
-/

namespace Armenian

open NounCategorization

/-- Retained as a numeral-classifier type for filtering; see the module docstring. -/
def classifierType : ClassifierType := .numeralClassifier

/-- Classifiers, when present, occur in the numeral phrase. -/
def classifierScopes : List CategorizationScope := [.numeralNP]

/-- Classifier choice is semantic. -/
def classifierAssignment : AssignmentPrinciple := .semantic

/-- Free morphemes. -/
def classifierRealizations : List SurfaceRealization := [.freeForm]

def classifierAgreement : Bool := false

/-- Numerals combine with bare nouns. -/
def classifierObligatory : Bool := false

/-- Whether the inventory has a general classifier. -/
def classifierDefault : Bool := false

def classifierSemantics : List SemanticParameter := []

def obligatoryNumber : Bool := false

/-- Whether classifiers and plural marking co-occur. -/
def pluralClassifierCooccur : Bool := false

end Armenian
