import Linglib.Features.NounCategorization.Basic
import Linglib.Fragments.Mayan.Chol.Classifiers

/-!
# Ch'ol noun-categorization parameters

Ch'ol classifiers are numeral classifiers suffixed to the numeral stem, obligatory with native
numerals (Spanish loan numerals reject them), with *-p'ej* as the generic default and attested
co-occurrence with plural marking. The lexical inventory is
`Fragments/Mayan/Chol/Classifiers.lean`.

## References

* [bale-coon-2014]
* [bale-et-al-2019]
* [little-moroney-royer-2022]
* [aikhenvald-2000]
-/

namespace Chol

open NounCategorization

/-- Classifiers are numeral classifiers. -/
def classifierType : ClassifierType := .numeralClassifier

/-- Classifiers occur in the numeral phrase. -/
def classifierScopes : List CategorizationScope := [.numeralNP]

/-- Classifier choice is semantic. -/
def classifierAssignment : AssignmentPrinciple := .semantic

/-- Suffixes on the numeral stem. -/
def classifierRealizations : List SurfaceRealization := [.suffix]

def classifierAgreement : Bool := false

/-- Obligatory with native numerals. -/
def classifierObligatory : Bool := true

/-- Whether the inventory has a general classifier. -/
def classifierDefault : Bool := Classifiers.allClassifiers.any (·.isDefault)

def classifierSemantics : List SemanticParameter := collectSemantics Classifiers.allClassifiers

def obligatoryNumber : Bool := false

/-- Whether classifiers and plural marking co-occur. -/
def pluralClassifierCooccur : Bool := true

end Chol
