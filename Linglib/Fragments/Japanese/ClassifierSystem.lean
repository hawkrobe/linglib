import Linglib.Features.NounCategorization.Basic
import Linglib.Fragments.Japanese.Classifier

/-!
# Japanese noun-categorization parameters

Japanese classifiers are numeral classifiers suffixed to numerals, chosen on semantic grounds,
with *tsu* as the general classifier. The lexical inventory is
`Fragments/Japanese/Classifier.lean`; the semantic parameters and the general classifier are
read off it.

## References

* [downing-1996]
* [aikhenvald-2000]
-/

namespace Japanese

open NounCategorization

/-- Classifiers are numeral classifiers. -/
def classifierType : ClassifierType := .numeralClassifier

/-- Classifiers occur in the numeral phrase. -/
def classifierScopes : List CategorizationScope := [.numeralNP]

/-- Classifier choice is semantic. -/
def classifierAssignment : AssignmentPrinciple := .semantic

/-- Suffixes on numerals. -/
def classifierRealizations : List SurfaceRealization := [.suffix]

def classifierAgreement : Bool := false

def classifierObligatory : Bool := true

/-- Whether the inventory has a general classifier. -/
def classifierDefault : Bool := Classifier.defaultClassifier?.isSome

def classifierSemantics : List SemanticParameter := Classifier.allEncodedParams

def obligatoryNumber : Bool := false

end Japanese
