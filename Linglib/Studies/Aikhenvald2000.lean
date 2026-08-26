import Linglib.Fragments.Romance.French.Nouns
import Linglib.Fragments.Italian.NumberGender
import Linglib.Fragments.Mandarin.Classifiers
import Linglib.Fragments.Japanese.Classifiers
import Linglib.Fragments.Xhosa.Basic
import Linglib.Fragments.Shona.Basic
import Linglib.Fragments.Swahili.Basic

/-!
# A typology of noun categorization devices

Aikhenvald's typology individuates classifier types by their morphosyntactic locus and
scope, the definitional parameters (A)–(G) of the book's first chapter, and then reads the
contingent parameters — interaction with other categories, preferred semantics, evolution,
acquisition — as correlates of the types so established. The types are focal points on a
continuum rather than discrete classes, and most generalizations are tendencies with listed
exceptions. Here the book's parameter list is the record `Device`, assembled from the values
seven Fragments record field by field — the French and Italian gender systems, the Xhosa,
Shona and Swahili noun-class systems, and the Mandarin and Japanese numeral-classifier systems
(`allDevices`) — with the kind of each device derived from its locus and the constituent it
characterizes rather than stored; the book's summary claims are checked on that sample, and
none is a universal over the record type.

Agreement by a constituent outside the noun is the definitional property of a noun class
system, a closed obligatory grammatical system (`nounClass_agreement_obligatory`), and noun
classes are never expressed by free lexemes (`nounClass_bound`), whereas free-form numeral
classifiers are non-agreeing (`free_numeralClassifier_no_agreement`). Every kind other than
noun class assigns classifiers on purely semantic grounds (`classifier_assignment_semantic`). Both
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

open Classifier

/-- The definitional parameters (A)–(G) of a noun categorization device, its preferred
semantics (I), and the language's number marking. -/
structure Device where
  /-- (A): the locus of coding. -/
  locus : Scope
  /-- (B): the constituent characterized. -/
  constituent : Constituent
  /-- (B): every scope the device operates in. -/
  scopes : List Scope
  /-- (C): the principle of assignment. -/
  assignment : Assignment
  /-- (D): surface realizations. -/
  realizations : List Realization
  /-- (E): whether the device participates in agreement. -/
  agreement : Bool
  /-- (G): whether the device is obligatory. -/
  obligatory : Bool
  /-- (F): a functionally unmarked member, or a general classifier. -/
  unmarkedMember : Bool
  /-- (I): preferred semantic parameters. -/
  semantics : List Parameter
  /-- Whether the language marks number obligatorily. -/
  obligatoryNumber : Bool
  deriving DecidableEq

/-- The kind of a device, read off its locus and the constituent it characterizes. -/
abbrev Device.kind (d : Device) : Option Kind := Classifier.kind d.locus d.constituent

def french : Device :=
  ⟨French.classifierLocus, French.classifierConstituent, French.classifierScopes,
   French.classifierAssignment, French.classifierRealizations, French.classifierAgreement,
   French.classifierObligatory, French.classifierDefault, French.classifierSemantics,
   French.obligatoryNumber⟩

def italian : Device :=
  ⟨Italian.classifierLocus, Italian.classifierConstituent, Italian.classifierScopes,
   Italian.classifierAssignment, Italian.classifierRealizations, Italian.classifierAgreement,
   Italian.classifierObligatory, Italian.classifierDefault, Italian.classifierSemantics,
   Italian.obligatoryNumber⟩

def mandarin : Device :=
  ⟨Mandarin.classifierLocus, Mandarin.classifierConstituent, Mandarin.classifierScopes,
   Mandarin.classifierAssignment, Mandarin.classifierRealizations, Mandarin.classifierAgreement,
   Mandarin.classifierObligatory, Mandarin.classifierDefault, Mandarin.classifierSemantics,
   Mandarin.obligatoryNumber⟩

def japanese : Device :=
  ⟨Japanese.classifierLocus, Japanese.classifierConstituent, Japanese.classifierScopes,
   Japanese.classifierAssignment, Japanese.classifierRealizations, Japanese.classifierAgreement,
   Japanese.classifierObligatory, Japanese.classifierDefault, Japanese.classifierSemantics,
   Japanese.obligatoryNumber⟩

def xhosa : Device :=
  ⟨Xhosa.classifierLocus, Xhosa.classifierConstituent, Xhosa.classifierScopes,
   Xhosa.classifierAssignment, Xhosa.classifierRealizations, Xhosa.classifierAgreement,
   Xhosa.classifierObligatory, Xhosa.classifierDefault, Xhosa.classifierSemantics,
   Xhosa.obligatoryNumber⟩

def shona : Device :=
  ⟨Shona.classifierLocus, Shona.classifierConstituent, Shona.classifierScopes,
   Shona.classifierAssignment, Shona.classifierRealizations, Shona.classifierAgreement,
   Shona.classifierObligatory, Shona.classifierDefault, Shona.classifierSemantics,
   Shona.obligatoryNumber⟩

def swahili : Device :=
  ⟨Swahili.classifierLocus, Swahili.classifierConstituent, Swahili.classifierScopes,
   Swahili.classifierAssignment, Swahili.classifierRealizations, Swahili.classifierAgreement,
   Swahili.classifierObligatory, Swahili.classifierDefault, Swahili.classifierSemantics,
   Swahili.obligatoryNumber⟩

/-- The sample: two gender systems, three Bantu noun-class systems, two numeral-classifier
systems. -/
def allDevices : List Device := [french, italian, mandarin, japanese, xhosa, shona, swahili]

/-! ### Definitional properties -/

/-- A noun class system is defined by agreement outside the noun and is a closed obligatory
grammatical system. -/
theorem nounClass_agreement_obligatory :
    ∀ s ∈ allDevices, s.kind = some .nounClass → s.agreement = true ∧ s.obligatory = true := by
  decide

/-- Noun classes are realized with affixes or clitics, never with free lexemes. -/
theorem nounClass_bound :
    ∀ s ∈ allDevices, s.kind = some .nounClass → .freeForm ∉ s.realizations := by decide

/-- Numeral classifiers expressed as free morphemes do not participate in agreement. -/
theorem free_numeralClassifier_no_agreement :
    ∀ s ∈ allDevices, s.kind = some .numeralClassifier → .freeForm ∈ s.realizations →
      s.agreement = false := by decide

/-- Every kind of device other than noun class is assigned on purely semantic grounds; noun
class assignment may be only partially semantic. -/
theorem classifier_assignment_semantic :
    ∀ s ∈ allDevices, s.kind ≠ some .nounClass → s.assignment = .semantic := by decide

/-- Both numeral-classifier systems have a generic classifier that can replace the specific
ones, Mandarin *ge* and Japanese *tsu*, the analogue of a functionally unmarked noun class. -/
theorem numeralClassifier_general :
    ∀ s ∈ allDevices, s.kind = some .numeralClassifier → s.unmarkedMember = true := by decide

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
    ∀ s ∈ allDevices, s.kind = some .nounClass ∨ s.kind = some .numeralClassifier →
      ∃ p ∈ s.semantics, p = .animacy ∨ p = .humanness ∨ p = .sex := by decide

/-- Physical properties such as shape are typical of numeral classifiers. -/
theorem numeralClassifier_shape :
    ∀ s ∈ allDevices, s.kind = some .numeralClassifier → .shape ∈ s.semantics := by
  decide

/-- Colour is never a basis for noun categorization. -/
theorem colour_never : ∀ s ∈ allDevices, .colour ∉ s.semantics := by decide

/-! ### Classifiers and number -/

/-- Numeral-classifier languages usually lack compulsory number marking. -/
theorem numeralClassifier_no_obligatory_number :
    ∀ s ∈ allDevices, s.kind = some .numeralClassifier → s.obligatoryNumber = false := by
  decide

end Aikhenvald2000
