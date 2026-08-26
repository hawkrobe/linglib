import Linglib.Features.NounCategorization.Basic

/-!
# French noun-categorization parameters

French has a two-gender noun-class system (masculine and feminine) with obligatory agreement
inside the noun phrase and with the predicate, semantic assignment with a morphological
residue, masculine as the unmarked gender, and obligatory number.

## References

* [aikhenvald-2000], §2
-/

namespace French

open NounCategorization

/-- Gender is a noun-class system. -/
def classifierType : ClassifierType := .nounClass

/-- Agreement inside the head-modifier NP and with the predicate. -/
def classifierScopes : List CategorizationScope := [.headModifierNP, .predicateArgument]

/-- Semantic core with a morphological residue. -/
def classifierAssignment : AssignmentPrinciple := .mixed

/-- Agreement inflection on modifiers; noun classes are never free lexemes. -/
def classifierRealizations : List SurfaceRealization := [.suffix]

def classifierAgreement : Bool := true

def classifierObligatory : Bool := true

/-- Masculine is the unmarked gender. -/
def classifierDefault : Bool := true

def classifierSemantics : List SemanticParameter := [.sex, .animacy]

def obligatoryNumber : Bool := true

end French
