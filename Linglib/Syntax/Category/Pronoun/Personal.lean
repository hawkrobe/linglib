module

public import Linglib.Morphology.Paradigm.Basic
public import Linglib.Pragmatics.SocialMeaning.Honorific
public import Linglib.Pragmatics.SocialMeaning.Register
public import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Personal pronouns

A personal pronoun is a pronoun with a register, an honorific level where the language grades its
pronouns for one, and the referential categories it denotes. The categories are by default those its
agreement person and number realize. A polite pronoun overrides the default: Italian *Lei* and
German *Sie* agree as third person and denote the addressee, so their formal features govern
agreement, clitic allomorphy and reflexive binding while their referential categories govern the
person-case constraint and resolved agreement ([adamson-zompi-2025]).

## Main definitions

* `PersonalPronoun` — a pronoun with its register, honorific level and referential categories
* `PersonalPronoun.referentialPerson`, `PersonalPronoun.referentialNumber` — the person and
  number the pronoun contributes to interpretation
* `PersonalPronoun.IsOrdinary` — the pronoun denotes what its agreement features realize
* `PersonalPronoun.paradigm` — the forms an inventory offers for each referential category,
  whose `Morphology.syncretism` is the inventory's person-number syncretism

## Main results

* `PersonalPronoun.referentialPerson_eq_person` — an ordinary pronoun's referential person is
  its agreement person
* `PersonalPronoun.bindingClassOf_toWord` — a personal pronoun is a pronominal

## References

* [L. J. Adamson and S. Zompì, *Polite Pronouns and the PCC* (2025)][adamson-zompi-2025]
* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
-/

@[expose] public section

/-- A personal pronoun is a `Pronoun` with its register, its honorific level and the referential
categories it denotes. -/
structure PersonalPronoun extends Pronoun where
  /-- The register. Japanese *boku* is an informal first person, and Korean *geu* a third person
  of written narrative. -/
  register : SocialMeaning.Register := .neutral
  /-- The honorific level the pronoun presents its referent at, `none` where the language does not
  grade the pronoun. A binary system uses `nonhonorific` and `honorific`; a ternary one, as in
  Hindi, Magahi and Maithili, all three levels. -/
  honorific : Option SocialMeaning.HonorificLevel := none
  /-- The referential categories the pronoun can denote, by default those its agreement person
  and number realize. Italian *Lei* denotes `{addressee}` and German *Sie*
  `{addressee, addresseeOthers}` ([adamson-zompi-2025]). -/
  referential : Finset Person.Category := toPronoun.categories
  deriving DecidableEq

namespace PersonalPronoun

variable {p : PersonalPronoun}

instance : HasPhi PersonalPronoun := ⟨fun p ↦ p.toPronoun.phi⟩

/-- The person a pronoun contributes to interpretation: the one its referential categories
share. -/
def referentialPerson (p : PersonalPronoun) : Option Person :=
  Person.Category.sharedPerson p.referential

/-- The number a pronoun contributes to interpretation: the one its referential categories
share, `general` for a number-neutral form such as polite *Sie*. -/
def referentialNumber (p : PersonalPronoun) : Option Number :=
  Person.Category.sharedNumber p.referential

/-- An ordinary pronoun denotes exactly the categories its agreement features realize. -/
def IsOrdinary (p : PersonalPronoun) : Prop := p.referential = p.categories

instance : Decidable p.IsOrdinary := inferInstanceAs (Decidable (_ = _))

/-- An ordinary pronoun's referential person is its agreement person. -/
theorem referentialPerson_eq_person (h : p.IsOrdinary) (hne : p.referential.Nonempty) :
    p.referentialPerson = p.person := by
  unfold referentialPerson
  rw [h, Pronoun.categories] at hne ⊢
  rcases hp : p.person with _ | per <;> rcases hn : p.number with _ | num <;>
    simp_all [Person.Category.sharedPerson_ofPersonNumber]

/-! ### The paradigm of an inventory -/

section Paradigm

variable {I J : Finset PersonalPronoun} {c : Person.Category} {f : String}

/-- The paradigm of an inventory assigns each referential category the forms the inventory offers
for it. A category no pronoun denotes gets `∅`, and two categories receive the same forms
exactly when the inventory does not distinguish them. -/
def paradigm : Finset PersonalPronoun → Person.Category → Finset String :=
  Morphology.formsAt (·.referential) (·.form)

theorem mem_paradigm : f ∈ paradigm I c ↔ ∃ p ∈ I, c ∈ p.referential ∧ p.form = f :=
  Morphology.mem_formsAt

@[gcongr]
theorem paradigm_mono (h : I ⊆ J) (c : Person.Category) : paradigm I c ⊆ paradigm J c :=
  Morphology.formsAt_mono h c

end Paradigm

/-! ### The pronoun as a token -/

/-- A personal pronoun's token is of UD pronoun type `Prs`. -/
def toWord (p : PersonalPronoun) : Morphology.Word := p.toPronoun.toWord (some .Prs)

/-- A personal pronoun is a pronominal. -/
@[simp]
theorem bindingClassOf_toWord (p : PersonalPronoun) :
    Binding.bindingClassOf p.toWord = some .pronoun :=
  p.toPronoun.bindingClassOf_toWord (by decide)

end PersonalPronoun
