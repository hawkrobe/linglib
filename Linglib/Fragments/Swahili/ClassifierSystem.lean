import Linglib.Features.NounCategorization.Basic

/-!
# Swahili noun-categorization parameters

Swahili has a Bantu noun-class system with prefixal realization and pervasive concord inside
the noun phrase and on the verb; singular/plural class pairs (M/Wa, Ki/Vi, …) make number
obligatory.

## References

* [aikhenvald-2000]
-/

namespace Swahili

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

end Swahili
