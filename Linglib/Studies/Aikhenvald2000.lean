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
exceptions. Here the book's summary claims are stated over the `NounCategorization.System`
records of seven Fragments — the French and Italian gender systems, the Xhosa, Shona and
Swahili noun-class systems, and the Mandarin and Japanese numeral-classifier systems
(`allSystems`) — and checked on that sample; none is a universal over the record type.

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

abbrev french := French.classifierSystem
abbrev italian := Italian.classifierSystem
abbrev mandarin := Mandarin.classifierSystem
abbrev japanese := Japanese.classifierSystem
abbrev xhosa := Xhosa.classifierSystem
abbrev shona := Shona.classifierSystem
abbrev swahili := Swahili.classifierSystem

/-- The sample: two gender systems, three Bantu noun-class systems, two numeral-classifier
systems. -/
def allSystems : List System := [french, italian, mandarin, japanese, xhosa, shona, swahili]

/-! ### Definitional properties -/

/-- A noun class system is defined by agreement outside the noun and is a closed obligatory
grammatical system. -/
theorem nounClass_agreement_obligatory :
    ∀ s ∈ allSystems, s.classifierType = .nounClass → s.HasAgreement ∧ s.IsObligatory := by
  decide

/-- Noun classes are realized with affixes or clitics, never with free lexemes. -/
theorem nounClass_bound :
    ∀ s ∈ allSystems, s.classifierType = .nounClass → .freeForm ∉ s.realizations := by decide

/-- Numeral classifiers expressed as free morphemes do not participate in agreement. -/
theorem free_numeralClassifier_no_agreement :
    ∀ s ∈ allSystems, s.classifierType = .numeralClassifier → .freeForm ∈ s.realizations →
      ¬ s.HasAgreement := by decide

/-- Each system operates in the scope that defines its type. -/
theorem locus_mem_scopes : ∀ s ∈ allSystems, s.classifierType.locus ∈ s.scopes := by decide

/-- Every classifier type other than noun class is assigned on purely semantic grounds; noun
class assignment may be only partially semantic. -/
theorem classifier_assignment_semantic :
    ∀ s ∈ allSystems, s.classifierType ≠ .nounClass → s.assignment = .semantic := by decide

/-- Both numeral-classifier systems have a generic classifier that can replace the specific
ones, Mandarin *ge* and Japanese *tsu*, the analogue of a functionally unmarked noun class. -/
theorem numeralClassifier_general :
    ∀ s ∈ allSystems, s.classifierType = .numeralClassifier → s.HasUnmarkedDefault := by decide

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
      ∃ p ∈ s.preferredSemantics, p = .animacy ∨ p = .humanness ∨ p = .sex := by decide

/-- Physical properties such as shape are typical of numeral classifiers. -/
theorem numeralClassifier_shape :
    ∀ s ∈ allSystems, s.classifierType = .numeralClassifier → .shape ∈ s.preferredSemantics := by
  decide

/-- Colour is never a basis for noun categorization. -/
theorem colour_never : ∀ s ∈ allSystems, .colour ∉ s.preferredSemantics := by decide

/-! ### Classifiers and number -/

/-- Numeral-classifier languages usually lack compulsory number marking. -/
theorem numeralClassifier_no_obligatory_number :
    ∀ s ∈ allSystems, s.classifierType = .numeralClassifier → ¬ s.HasObligatoryNumber := by
  decide

end Aikhenvald2000
