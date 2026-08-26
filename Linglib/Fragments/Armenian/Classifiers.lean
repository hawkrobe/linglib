import Linglib.Syntax.Category.Classifier.Basic

/-!
# Western Armenian classifiers

Western Armenian numerals combine directly with bare nouns (*yergu dəgha vaze-ts* 'two boys
ran') as well as with plural nouns, so its classifiers are non-obligatory and there is no
inventory to record; plural nouns are incompatible with classifiers. The numeral-classifier
locus is retained so that cross-language consumers can classify the language, although with no
obligatory classifier the language arguably has no classifier system in Aikhenvald's sense.

## References

* [bale-khanjian-2014], (10) and fn. 3
* [bale-khanjian-2008]
-/
/-! ### Typological parameters -/

namespace Armenian

/-- Classifiers, when present, occur in the numeral phrase. -/
def classifierLocus : Classifier.Scope := .numeralNP

def classifierConstituent : Classifier.Constituent := .headNoun

/-- The kind of device, read off its locus and the constituent it characterizes. -/
abbrev classifierKind : Option Classifier.Kind :=
  Classifier.kind classifierLocus classifierConstituent

/-- Every environment the device operates in. -/
def classifierScopes : List Classifier.Scope := [.numeralNP]

/-- Classifier choice is semantic. -/
def classifierAssignment : Classifier.Assignment := .semantic

/-- Free morphemes. -/
def classifierRealizations : List Classifier.Realization := [.freeForm]

def classifierAgreement : Bool := false

/-- Numerals combine with bare nouns. -/
def classifierObligatory : Bool := false

def classifierDefault : Bool := false

def classifierSemantics : List Classifier.Parameter := []

def obligatoryNumber : Bool := false

/-- Whether classifiers and plural marking co-occur. -/
def pluralClassifierCooccur : Bool := false

end Armenian
