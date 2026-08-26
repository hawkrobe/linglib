import Linglib.Features.NounCategorization.Basic

/-!
# Xhosa noun-categorization parameters

Xhosa has a Bantu noun-class system with prefixal realization and pervasive concord inside
the noun phrase and on the verb; class 2 *ba-* and class 8 *zi-* serve as default agreement
classes, and singular/plural class pairs make number obligatory.

## References

* [carstens-2026]
* [taraldsen-et-al-2018]
-/

namespace Xhosa

open NounCategorization

/-- Gender is a noun-class system. -/
def classifierType : ClassifierType := .nounClass

/-- Agreement inside the head-modifier NP and with the predicate. -/
def classifierScopes : List CategorizationScope := [.headModifierNP, .predicateArgument]

/-- Semantic core with morphological residue. -/
def classifierAssignment : AssignmentPrinciple := .mixed

/-- Class prefixes on the noun and its agreement targets. -/
def classifierRealizations : List SurfaceRealization := [.prefix]

def classifierAgreement : Bool := true

def classifierObligatory : Bool := true

/-- A default agreement class. -/
def classifierDefault : Bool := true

def classifierSemantics : List SemanticParameter := [.humanness, .animacy]

def obligatoryNumber : Bool := true

end Xhosa
