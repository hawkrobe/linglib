import Linglib.Features.NounCategorization.Basic
import Linglib.Fragments.Mandarin.Classifiers

/-!
# Mandarin noun-categorization parameters

Mandarin classifiers are numeral classifiers: free morphemes obligatory with numerals and
demonstratives, chosen on semantic grounds with a lexical residue that must be memorized, with
*ge* as the general classifier that can replace the specific ones. The lexical inventory is
`Fragments/Mandarin/Classifiers.lean`; the semantic parameters and the general classifier are
read off it.

## References

* [li-thompson-1981], §4.2.1
* [aikhenvald-2000]
-/

namespace Mandarin

open NounCategorization

/-- Classifiers are numeral classifiers. -/
def classifierType : ClassifierType := .numeralClassifier

/-- Classifiers occur with numerals and with demonstratives (那本书). -/
def classifierScopes : List CategorizationScope := [.numeralNP, .attributiveNP]

/-- Classifier choice is semantic. -/
def classifierAssignment : AssignmentPrinciple := .semantic

/-- Free morphemes. -/
def classifierRealizations : List SurfaceRealization := [.freeForm]

def classifierAgreement : Bool := false

/-- Obligatory with numerals and demonstratives. -/
def classifierObligatory : Bool := true

/-- Whether the inventory has a general classifier. -/
def classifierDefault : Bool := Classifiers.allClassifiers.any (·.isDefault)

def classifierSemantics : List SemanticParameter := collectSemantics Classifiers.allClassifiers

def obligatoryNumber : Bool := false

end Mandarin
