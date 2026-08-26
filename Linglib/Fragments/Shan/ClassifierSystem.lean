import Linglib.Features.NounCategorization.Basic
import Linglib.Fragments.Shan.Classifiers

/-!
# Shan noun-categorization parameters

Shan classifiers are numeral classifiers: free morphemes derived from nominal elements (*tǒ*
'body'), required uniformly by numerals and extending to quantifiers, demonstratives and
relative clauses, with a generic classifier and no co-occurrence with plural marking. The
lexical inventory is `Fragments/Shan/Classifiers.lean`.

## References

* [moroney-2021]
* [little-moroney-royer-2022]
* [aikhenvald-2000]
-/

namespace Shan

open NounCategorization

/-- Classifiers are numeral classifiers. -/
def classifierType : ClassifierType := .numeralClassifier

/-- Classifiers occur with numerals, quantifiers, demonstratives and relative clauses. -/
def classifierScopes : List CategorizationScope := [.numeralNP, .attributiveNP]

/-- Classifier choice is semantic. -/
def classifierAssignment : AssignmentPrinciple := .semantic

/-- Free morphemes. -/
def classifierRealizations : List SurfaceRealization := [.freeForm]

def classifierAgreement : Bool := false

def classifierObligatory : Bool := true

/-- Whether the inventory has a general classifier. -/
def classifierDefault : Bool := Classifiers.allClassifiers.any (·.isDefault)

def classifierSemantics : List SemanticParameter := collectSemantics Classifiers.allClassifiers

def obligatoryNumber : Bool := false

/-- Whether classifiers and plural marking co-occur. -/
def pluralClassifierCooccur : Bool := false

end Shan
