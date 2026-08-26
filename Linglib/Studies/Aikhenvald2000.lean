import Linglib.Fragments.Romance.French.ClassifierSystem
import Linglib.Fragments.Italian.ClassifierSystem
import Linglib.Fragments.Mandarin.ClassifierSystem
import Linglib.Fragments.Japanese.ClassifierSystem
import Linglib.Fragments.Xhosa.ClassifierSystem
import Linglib.Fragments.Shona.ClassifierSystem
import Linglib.Fragments.Swahili.ClassifierSystem

/-!
# A typology of noun categorization devices

Aikhenvald's typology individuates classifier types by their morphosyntactic locus and
scope, the definitional parameters (A)–(G) of the book's first chapter, and then reads the
contingent parameters — interaction with other categories, preferred semantics, evolution,
acquisition — as correlates of the types so established. The types are focal points on a
continuum rather than discrete classes, and most generalizations are tendencies with listed
exceptions. Here the book's parameter list is the record `Parameters`, assembled from the
values seven Fragments record field by field — the French and Italian gender systems, the
Xhosa, Shona and Swahili noun-class systems, and the Mandarin and Japanese numeral-classifier
systems (`allSystems`) — and the book's summary claims are checked on that sample; none is a
universal over the record type.

Agreement by a constituent outside the noun is the definitional property of a noun class
system, a closed obligatory grammatical system (`nounClass_agreement_obligatory`), and noun
classes are never expressed by free lexemes (`nounClass_bound`), whereas free-form numeral
classifiers are non-agreeing (`free_numeralClassifier_no_agreement`). Each type's defining
scope appears among the system's scopes (`locus_mem_scopes`), and every type other than noun
class assigns classifiers on purely semantic grounds (`classifier_assignment_semantic`). Both
numeral-classifier systems in the sample have a generic classifier, Mandarin *ge* and Japanese
*tsu*, read off their inventories (`numeralClassifier_general`), and the choice of a specific
classifier is semantically motivated (`classifier_choice_semantic`). Animacy, humanness or sex
is basic to noun classes and numeral classifiers alike, shape is typical of numeral
classifiers, and colour is never a basis for categorization (`animacy_basic`,
`numeralClassifier_shape`, `colour_never`); the absence of compulsory number in
numeral-classifier languages, Greenberg's association that the book records together with
its Dravidian, Nivkh, Algonquian, Tucano, Arawak and Ejagham exceptions, holds in the sample
(`numeralClassifier_no_obligatory_number`). Western Armenian, whose numerals combine with
bare nouns, is not classified as a classifier language by the book and is left to
`BaleKhanjian2014`.

## References

* [aikhenvald-2000]
* [greenberg-1972]
* [li-thompson-1981]
* [downing-1996]
-/

namespace Aikhenvald2000

open NounCategorization

/-- The definitional parameters (A)–(G) of a noun categorization system, its preferred
semantics (I), and the language's number marking. -/
structure Parameters where
  /-- (A), (B): the device type, individuated by locus and scope. -/
  classifierType : ClassifierType
  /-- (B): the scopes the device operates in. -/
  scopes : List CategorizationScope
  /-- (C): the principle of assignment. -/
  assignment : AssignmentPrinciple
  /-- (D): surface realizations. -/
  realizations : List SurfaceRealization
  /-- (E): whether the device participates in agreement. -/
  agreement : Bool
  /-- (G): whether the device is obligatory. -/
  obligatory : Bool
  /-- (F): a functionally unmarked member, or a general classifier. -/
  unmarkedMember : Bool
  /-- (I): preferred semantic parameters. -/
  semantics : List SemanticParameter
  /-- Whether the language marks number obligatorily. -/
  obligatoryNumber : Bool
  deriving DecidableEq

def french : Parameters :=
  ⟨French.classifierType, French.classifierScopes, French.classifierAssignment,
   French.classifierRealizations, French.classifierAgreement, French.classifierObligatory,
   French.classifierDefault, French.classifierSemantics, French.obligatoryNumber⟩

def italian : Parameters :=
  ⟨Italian.classifierType, Italian.classifierScopes, Italian.classifierAssignment,
   Italian.classifierRealizations, Italian.classifierAgreement, Italian.classifierObligatory,
   Italian.classifierDefault, Italian.classifierSemantics, Italian.obligatoryNumber⟩

def mandarin : Parameters :=
  ⟨Mandarin.classifierType, Mandarin.classifierScopes, Mandarin.classifierAssignment,
   Mandarin.classifierRealizations, Mandarin.classifierAgreement, Mandarin.classifierObligatory,
   Mandarin.classifierDefault, Mandarin.classifierSemantics, Mandarin.obligatoryNumber⟩

def japanese : Parameters :=
  ⟨Japanese.classifierType, Japanese.classifierScopes, Japanese.classifierAssignment,
   Japanese.classifierRealizations, Japanese.classifierAgreement, Japanese.classifierObligatory,
   Japanese.classifierDefault, Japanese.classifierSemantics, Japanese.obligatoryNumber⟩

def xhosa : Parameters :=
  ⟨Xhosa.classifierType, Xhosa.classifierScopes, Xhosa.classifierAssignment,
   Xhosa.classifierRealizations, Xhosa.classifierAgreement, Xhosa.classifierObligatory,
   Xhosa.classifierDefault, Xhosa.classifierSemantics, Xhosa.obligatoryNumber⟩

def shona : Parameters :=
  ⟨Shona.classifierType, Shona.classifierScopes, Shona.classifierAssignment,
   Shona.classifierRealizations, Shona.classifierAgreement, Shona.classifierObligatory,
   Shona.classifierDefault, Shona.classifierSemantics, Shona.obligatoryNumber⟩

def swahili : Parameters :=
  ⟨Swahili.classifierType, Swahili.classifierScopes, Swahili.classifierAssignment,
   Swahili.classifierRealizations, Swahili.classifierAgreement, Swahili.classifierObligatory,
   Swahili.classifierDefault, Swahili.classifierSemantics, Swahili.obligatoryNumber⟩

/-- The sample: two gender systems, three Bantu noun-class systems, two numeral-classifier
systems. -/
def allSystems : List Parameters := [french, italian, mandarin, japanese, xhosa, shona, swahili]

/-! ### Definitional properties -/

/-- A noun class system is defined by agreement outside the noun and is a closed obligatory
grammatical system. -/
theorem nounClass_agreement_obligatory :
    ∀ s ∈ allSystems, s.classifierType = .nounClass → s.agreement = true ∧ s.obligatory = true := by
  decide

/-- Noun classes are realized with affixes or clitics, never with free lexemes. -/
theorem nounClass_bound :
    ∀ s ∈ allSystems, s.classifierType = .nounClass → .freeForm ∉ s.realizations := by decide

/-- Numeral classifiers expressed as free morphemes do not participate in agreement. -/
theorem free_numeralClassifier_no_agreement :
    ∀ s ∈ allSystems, s.classifierType = .numeralClassifier → .freeForm ∈ s.realizations →
      s.agreement = false := by decide

/-- Each system operates in the scope that defines its type. -/
theorem locus_mem_scopes : ∀ s ∈ allSystems, s.classifierType.locus ∈ s.scopes := by decide

/-- Every classifier type other than noun class is assigned on purely semantic grounds; noun
class assignment may be only partially semantic. -/
theorem classifier_assignment_semantic :
    ∀ s ∈ allSystems, s.classifierType ≠ .nounClass → s.assignment = .semantic := by decide

/-- Both numeral-classifier systems have a generic classifier that can replace the specific
ones, Mandarin *ge* and Japanese *tsu*, the analogue of a functionally unmarked noun class. -/
theorem numeralClassifier_general :
    ∀ s ∈ allSystems, s.classifierType = .numeralClassifier → s.unmarkedMember = true := by decide

/-- The choice of a specific numeral classifier is semantic: every non-generic sortal classifier
encodes some semantic parameter. -/
theorem classifier_choice_semantic :
    (Mandarin.Classifiers.allClassifiers.filter (!·.isDefault)).all (·.semantics ≠ []) ∧
    ∀ c : Japanese.Classifier, ¬ Japanese.Classifier.IsDefault c →
      ¬ Japanese.Classifier.IsMensural c → c.encodes ≠ [] :=
  ⟨by decide, Japanese.Classifier.specific_classifiers_have_semantics⟩

/-! ### Preferred semantics -/

/-- Animacy, humanness or sex is basic to noun classes and numeral classifiers. -/
theorem animacy_basic :
    ∀ s ∈ allSystems, s.classifierType = .nounClass ∨ s.classifierType = .numeralClassifier →
      ∃ p ∈ s.semantics, p = .animacy ∨ p = .humanness ∨ p = .sex := by decide

/-- Physical properties such as shape are typical of numeral classifiers. -/
theorem numeralClassifier_shape :
    ∀ s ∈ allSystems, s.classifierType = .numeralClassifier → .shape ∈ s.semantics := by
  decide

/-- Colour is never a basis for noun categorization. -/
theorem colour_never : ∀ s ∈ allSystems, .colour ∉ s.semantics := by decide

/-! ### Classifiers and number -/

/-- Numeral-classifier languages usually lack compulsory number marking. -/
theorem numeralClassifier_no_obligatory_number :
    ∀ s ∈ allSystems, s.classifierType = .numeralClassifier → s.obligatoryNumber = false := by
  decide

end Aikhenvald2000
