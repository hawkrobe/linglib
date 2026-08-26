import Linglib.Features.NounCategorization.Basic

/-!
# Italian noun-categorization parameters

Italian has a two-gender noun-class system (masculine and feminine) with obligatory agreement
inside the noun phrase and with the predicate, assignment by sex and by the *-o* / *-a* endings,
masculine as the unmarked gender, and obligatory number.

## References

* [aikhenvald-2000], §2
* [chierchia-1998]
-/

namespace Italian

open NounCategorization

/-- Gender is a noun-class system. -/
def classifierType : ClassifierType := .nounClass

/-- Agreement inside the head-modifier NP and with the predicate. -/
def classifierScopes : List CategorizationScope := [.headModifierNP, .predicateArgument]

/-- Sex plus the morphological *-o* / *-a* endings. -/
def classifierAssignment : AssignmentPrinciple := .mixed

/-- Agreement inflection on modifiers; noun classes are never free lexemes. -/
def classifierRealizations : List SurfaceRealization := [.suffix]

def classifierAgreement : Bool := true

def classifierObligatory : Bool := true

/-- Masculine is the unmarked gender. -/
def classifierDefault : Bool := true

def classifierSemantics : List SemanticParameter := [.sex, .animacy]

def obligatoryNumber : Bool := true

end Italian
