module

public import Linglib.Morphology.Paradigm.Basic
public import Linglib.Pragmatics.SocialMeaning.Register
public import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Personal pronouns

A personal pronoun is a pronoun with a register, the honorific grades it realizes, and the
referential categories it denotes. The categories are by default those its agreement person and
number realize. A polite pronoun overrides the default: Italian *Lei* and German *Sie* agree as
third person and denote the addressee, so their formal features govern agreement, clitic
allomorphy and reflexive binding while their referential categories govern the person-case
constraint and resolved agreement.

An honorific system grades forms by the deference they present toward the person they refer to
or address, and its grades are the language's own categories: German opposes familiar *du* to
polite *Sie*, Magahi grades its second person in three and Maithili in four. A fragment defines
its grades as a type `G` linearly ordered by deference from the lowest grade up, and an ungraded
language takes `Empty`. A pronoun records the set of grades it realizes, since a form may serve
several: Maithili *tõ* is both the nonhonorific and the mid-honorific second person, which only
verbal agreement tells apart. Systems are compared by their shape, the number of grades and which
of them the forms distinguish, never by identifying one language's grades with another's. The one
distinction every system draws is between the lowest grade and the rest, so a pronoun is
honorific when every grade it realizes is above another.

## Main definitions

* `PersonalPronoun` — a pronoun with its register, honorific grades and referential categories
* `PersonalPronoun.IsHonorific` — the pronoun realizes only grades above the lowest
* `PersonalPronoun.referentialPerson`, `PersonalPronoun.referentialNumber` — the person and
  number the pronoun contributes to interpretation
* `PersonalPronoun.IsOrdinary` — the pronoun denotes what its agreement features realize
* `PersonalPronoun.paradigm` — the forms an inventory offers for each referential category,
  whose kernel `Setoid.ker` is the inventory's person-number syncretism
* `PersonalPronoun.gradeParadigm` — the forms an inventory offers for a category at each
  honorific grade, whose kernel relates the grades its pronouns do not distinguish

## Main results

* `PersonalPronoun.referentialPerson_eq_person` — an ordinary pronoun's referential person is
  its agreement person
* `PersonalPronoun.bindingClassOf_toWord` — a personal pronoun is a pronominal

## References

* [L. J. Adamson and S. Zompì, *Polite Pronouns and the PCC* (2025)][adamson-zompi-2025]
* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
* [P. Kumari and P. Chandra, *Honorificity Feature as an Enabler: Bridging the Person Gap*
  (2026)][kumari-chandra-2026]
-/

@[expose] public section

/-- A personal pronoun is a `Pronoun` with its register, the honorific grades it realizes on the
scale `G` of its language, and the referential categories it denotes. -/
structure PersonalPronoun (G : Type) extends Pronoun where
  /-- The register. Japanese *boku* is an informal first person, and Korean *geu* a third person
  of written narrative. -/
  register : SocialMeaning.Register := .neutral
  /-- The honorific grades the pronoun realizes, empty for a form the language does not grade.
  Maithili *tõ* realizes the nonhonorific and the mid-honorific second person. -/
  grades : Finset G := ∅
  /-- The referential categories the pronoun can denote, by default those its agreement person
  and number realize. Italian *Lei* denotes `{addressee}` and German *Sie*
  `{addressee, addresseeOthers}` ([adamson-zompi-2025]). -/
  referential : Finset Person.Category := toPronoun.categories
  deriving DecidableEq

namespace PersonalPronoun

variable {G : Type} {p : PersonalPronoun G}

instance : HasPhi (PersonalPronoun G) := ⟨fun p ↦ p.toPronoun.phi⟩

/-- The person a pronoun contributes to interpretation: the one its referential categories
share. -/
def referentialPerson (p : PersonalPronoun G) : Option Person :=
  Person.Category.sharedPerson p.referential

/-- The number a pronoun contributes to interpretation: the one its referential categories
share, `general` for a number-neutral form such as polite *Sie*. -/
def referentialNumber (p : PersonalPronoun G) : Option Number :=
  Person.Category.sharedNumber p.referential

/-- An ordinary pronoun denotes exactly the categories its agreement features realize. -/
def IsOrdinary (p : PersonalPronoun G) : Prop := p.referential = p.categories

instance : Decidable p.IsOrdinary := inferInstanceAs (Decidable (_ = _))

/-- An ordinary pronoun's referential person is its agreement person. -/
theorem referentialPerson_eq_person (h : p.IsOrdinary) (hne : p.referential.Nonempty) :
    p.referentialPerson = p.person := by
  unfold referentialPerson
  rw [h, Pronoun.categories] at hne ⊢
  rcases hp : p.person with _ | per <;> rcases hn : p.number with _ | num <;>
    simp_all [Person.Category.sharedPerson_ofPersonNumber]

/-! ### Honorific pronouns -/

section Honorific

variable [LT G]

/-- A pronoun is honorific when it realizes some grade and every grade it realizes is above
another: Maithili *əhã* is, while *tõ* and *o*, which also serve the lowest grade, are not. -/
def IsHonorific (p : PersonalPronoun G) : Prop :=
  p.grades.Nonempty ∧ ∀ g ∈ p.grades, ∃ h, h < g

instance [Fintype G] [DecidableLT G] : Decidable p.IsHonorific :=
  inferInstanceAs (Decidable (_ ∧ _))

end Honorific

/-! ### The paradigm of an inventory -/

section Paradigm

variable {I J : Finset (PersonalPronoun G)} {c : Person.Category} {f : String}

/-- The paradigm of an inventory assigns each referential category the forms the inventory offers
for it. A category no pronoun denotes gets `∅`, and two categories receive the same forms
exactly when the inventory does not distinguish them. -/
def paradigm : Finset (PersonalPronoun G) → Person.Category → Finset String :=
  Morphology.formsAt (·.referential) (·.form)

theorem mem_paradigm : f ∈ paradigm I c ↔ ∃ p ∈ I, c ∈ p.referential ∧ p.form = f :=
  Morphology.mem_formsAt

@[gcongr]
theorem paradigm_mono (h : I ⊆ J) (c : Person.Category) : paradigm I c ⊆ paradigm J c :=
  Morphology.formsAt_mono h c

variable [DecidableEq G] {g : G}

/-- The grade paradigm of an inventory for a referential category assigns each honorific grade
the forms of the pronouns that denote the category and realize the grade. Two grades receive the
same forms exactly when the inventory does not distinguish them for that category. -/
def gradeParadigm (I : Finset (PersonalPronoun G)) (c : Person.Category) : G → Finset String :=
  Morphology.formsAt (·.grades) (·.form) (I.filter (c ∈ ·.referential))

theorem mem_gradeParadigm :
    f ∈ gradeParadigm I c g ↔ ∃ p ∈ I, c ∈ p.referential ∧ g ∈ p.grades ∧ p.form = f := by
  simp [gradeParadigm, Morphology.mem_formsAt, and_assoc]

@[gcongr]
theorem gradeParadigm_mono (h : I ⊆ J) (c : Person.Category) (g : G) :
    gradeParadigm I c g ⊆ gradeParadigm J c g :=
  Morphology.formsAt_mono (Finset.filter_subset_filter _ h) g

end Paradigm

/-! ### The pronoun as a token -/

/-- A personal pronoun's token is of UD pronoun type `Prs`. -/
def toWord (p : PersonalPronoun G) : Morphology.Word := p.toPronoun.toWord (some .Prs)

/-- A personal pronoun is a pronominal. -/
@[simp]
theorem bindingClassOf_toWord (p : PersonalPronoun G) :
    Binding.bindingClassOf p.toWord = some .pronoun :=
  p.toPronoun.bindingClassOf_toWord (by decide)

end PersonalPronoun
