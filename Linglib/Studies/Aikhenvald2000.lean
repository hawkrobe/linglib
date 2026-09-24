module

public import Linglib.Fragments.Mandarin.Nouns
public import Linglib.Fragments.Japanese.Classifiers

/-!
# A typology of noun categorization devices

Aikhenvald's typology individuates classifier types by their morphosyntactic locus and
scope, the definitional parameters (A)–(G) of the book's first chapter, and then reads the
contingent parameters — interaction with other categories, preferred semantics, evolution,
acquisition — as correlates of the types so established. The types are focal points on a
continuum rather than discrete classes, and most generalizations are tendencies with listed
exceptions. Here the book's parameters are functions on a sample of seven languages
(`Language`), the French and Italian gender systems, the Xhosa, Shona and Swahili noun-class
systems, and the Mandarin and Japanese numeral-classifier systems, coded as the book describes
them, with the kind of each device derived from its locus and the constituent it characterizes
rather than stored; the book's summary claims are checked on that sample, and none is a
universal.

Agreement by a constituent outside the noun is the definitional property of a noun class
system, a closed obligatory grammatical system (`nounClass_agreement_obligatory`), and noun
classes are never expressed by free lexemes (`nounClass_bound`), whereas free-form numeral
classifiers are non-agreeing (`free_numeralClassifier_no_agreement`). Every kind other than
noun class assigns classifiers on purely semantic grounds (`classifier_assignment_semantic`).
Both numeral-classifier systems in the sample have a general classifier, read off the fragments
rather than coded: every Mandarin noun that takes a classifier can take *gè*, and Japanese
*-tsu* encodes no parameter (`numeralClassifier_general`). Animacy, humanness or sex is basic
to noun classes and numeral classifiers alike, shape is typical of numeral classifiers, and
colour is never a basis for categorization (`animacy_basic`, `numeralClassifier_shape`,
`colour_never`); the absence of compulsory number in numeral-classifier languages, Greenberg's
association that the book records together with its Dravidian, Nivkh, Algonquian, Tucano,
Arawak and Ejagham exceptions, holds in the sample (`numeralClassifier_no_obligatory_number`).
Western Armenian, whose numerals combine with bare nouns, is not classified as a classifier
language by the book and is left to `BaleKhanjian2014`.

## References

* [aikhenvald-2000]
* [greenberg-1972]
* [li-thompson-1981]
* [downing-1996]
-/

@[expose] public section

namespace Aikhenvald2000

open Classifier

/-- The sample: two gender systems, three Bantu noun-class systems, two numeral-classifier
systems. -/
inductive Language where
  | french | italian | xhosa | shona | swahili | mandarin | japanese
  deriving DecidableEq, Fintype

namespace Language

/-- (A): the locus of coding, the head-modifier NP for the gender and noun-class systems and the
numeral NP for the numeral classifiers. -/
def locus : Language → Scope
  | mandarin | japanese => .numeralNP
  | french | italian | xhosa | shona | swahili => .headModifierNP

/-- (B): every device of the sample characterizes the head noun. -/
def constituent (_ : Language) : Constituent := .headNoun

/-- The kind of a device, read off its locus and the constituent it characterizes. -/
def kind (l : Language) : Option Kind := Classifier.kind l.locus l.constituent

/-- (B): every scope the device operates in. Mandarin uses the same classifiers with numerals
and with demonstratives (the book's Table 9.1); agreement in gender and class reaches the
predicate. -/
def scopes : Language → Finset Scope
  | mandarin => {.numeralNP, .attributiveNP}
  | japanese => {.numeralNP}
  | french | italian | xhosa | shona | swahili => {.headModifierNP, .predicateArgument}

/-- (C): the principle of assignment, semantic for the numeral classifiers and a semantic core
with a morphological residue for gender and noun class. -/
def assignment : Language → Assignment
  | mandarin | japanese => .semantic
  | french | italian | xhosa | shona | swahili => .mixed

/-- (D): the surface realizations: Mandarin classifiers are independent forms, Japanese ones
suffixes on the numeral, gender is inflection on the agreeing words and Bantu class a prefix. -/
def realizations : Language → Finset Realization
  | mandarin => {.freeForm}
  | japanese | french | italian => {.suffix}
  | xhosa | shona | swahili => {.prefix}

/-- (E): the device participates in agreement. -/
def Agreement : Language → Prop
  | mandarin | japanese => False
  | french | italian | xhosa | shona | swahili => True

/-- (G): the device is obligatory. -/
def Obligatory (_ : Language) : Prop := True

/-- (F): the system has a functionally unmarked member or a general classifier. For the
numeral classifiers it is read off the fragments: a Mandarin classifier every counted noun can
take, and a Japanese classifier that encodes no parameter. The masculine gender and a default
class are the unmarked members of the other systems. -/
def HasUnmarkedMember : Language → Prop
  | mandarin => ∃ c ∈ Mandarin.Classifiers.classifiers,
      ∀ n ∈ Mandarin.Nouns.nouns, n.classifiers.Nonempty → n.Takes c
  | japanese => ∃ c, Japanese.Classifier.IsDefault c
  | french | italian | xhosa | shona | swahili => True

/-- (I): the preferred semantic parameters. Sex and animacy for the Romance genders, humanness
and animacy for the Bantu classes; for Mandarin, the animacy of *zhī* and the shape by which
*tiáo* extended from 'small branch' to long things in general, shape being the preferred
parameter of numeral classifiers; for Japanese, the parameters its classifiers encode. -/
def semantics : Language → Finset Parameter
  | french | italian => {.sex, .animacy}
  | xhosa | shona | swahili => {.humanness, .animacy}
  | mandarin => {.animacy, .shape}
  | japanese => Japanese.Classifier.allEncodedParams.toFinset

/-- The language marks number obligatorily. -/
def ObligatoryNumber : Language → Prop
  | mandarin | japanese => False
  | french | italian | xhosa | shona | swahili => True

instance : DecidablePred Agreement := fun l ↦ by cases l <;> unfold Agreement <;> infer_instance

instance : DecidablePred Obligatory := fun _ ↦ inferInstanceAs (Decidable True)

instance : DecidablePred ObligatoryNumber := fun l ↦ by
  cases l <;> unfold ObligatoryNumber <;> infer_instance

end Language

open Language

/-! ### Definitional properties -/

/-- A noun class system is defined by agreement outside the noun and is a closed obligatory
grammatical system. -/
theorem nounClass_agreement_obligatory :
    ∀ l : Language, l.kind = some .nounClass → l.Agreement ∧ l.Obligatory := by
  decide

/-- Noun classes are realized with affixes or clitics, never with free lexemes. -/
theorem nounClass_bound :
    ∀ l : Language, l.kind = some .nounClass → .freeForm ∉ l.realizations := by
  decide

/-- Numeral classifiers expressed as free morphemes do not participate in agreement. -/
theorem free_numeralClassifier_no_agreement :
    ∀ l : Language, l.kind = some .numeralClassifier → .freeForm ∈ l.realizations →
      ¬ l.Agreement := by
  decide

/-- Every kind of device other than noun class is assigned on purely semantic grounds; noun
class assignment may be only partially semantic. -/
theorem classifier_assignment_semantic :
    ∀ l : Language, l.kind ≠ some .nounClass → l.assignment = .semantic := by
  decide

/-- Both numeral-classifier systems have a general classifier that can replace the specific
ones, the analogue of a functionally unmarked noun class: *gè*, which every Mandarin noun that
takes a classifier can take, and Japanese *-tsu*. -/
theorem numeralClassifier_general :
    ∀ l : Language, l.kind = some .numeralClassifier → l.HasUnmarkedMember
  | .mandarin, _ =>
    ⟨Mandarin.Classifiers.ge, by simp [Mandarin.Classifiers.classifiers],
      fun _ _ h ↦ Mandarin.Nouns.Noun.takes_ge h⟩
  | .japanese, _ => ⟨.tsu, rfl⟩

/-! ### Preferred semantics -/

/-- Animacy, humanness or sex is basic to noun classes and numeral classifiers. -/
theorem animacy_basic :
    ∀ l : Language, l.kind = some .nounClass ∨ l.kind = some .numeralClassifier →
      ∃ p ∈ l.semantics, p = .animacy ∨ p = .humanness ∨ p = .sex := by
  decide

/-- Physical properties such as shape are typical of numeral classifiers. -/
theorem numeralClassifier_shape :
    ∀ l : Language, l.kind = some .numeralClassifier → .shape ∈ l.semantics := by
  decide

/-- Colour is never a basis for noun categorization. -/
theorem colour_never : ∀ l : Language, .colour ∉ l.semantics := by decide

/-! ### Classifiers and number -/

/-- Numeral-classifier languages usually lack compulsory number marking. -/
theorem numeralClassifier_no_obligatory_number :
    ∀ l : Language, l.kind = some .numeralClassifier → ¬ l.ObligatoryNumber := by
  decide

end Aikhenvald2000
