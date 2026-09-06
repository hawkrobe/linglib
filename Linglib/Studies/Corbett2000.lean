import Mathlib.Data.Rat.Defs
import Mathlib.Order.UpperLower.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Linglib.Features.Number.Resolve
import Linglib.Features.Prominence
import Linglib.Fragments.Bayso.Number
import Linglib.Fragments.Teop.Nouns
import Linglib.Studies.Corbett1991
import Linglib.Studies.Corbett1998
import Linglib.Data.Examples.Corbett2000

/-!
# Corbett's typology of number

Number has more shape than the singular and plural of English. A language may express a
noun's meaning outside the number system, the general number of Bayso, with a form of its
own, or of Japanese, where the general form is the singular's; within the system the values
are chosen in order, the determinate dual and trial dividing the plural before the
indeterminate paucals and greater plural divide it further, so that the systems from
Russian's two values to Lihir's five are the sequences of binary choices, and a facultative
value, one whose use is not required, can only be a last choice, every choice after it
facultative too. Which nominals distinguish number follows the Animacy Hierarchy, from the
speaker through the addressee, the third person, kin and humans to animates and inanimates:
the likelihood of number being distinguished never increases rightwards, so that a value's
range is a top segment, each further choice has a range no wider than the choice before it,
and obligatory marking lies above facultative. Minor numbers, the Hebrew dual or the Avar
paucal, escape the hierarchy but only inside systems attested with and without them;
associativity is a category of its own; and a second system lower on the hierarchy may
conflate values or add a mass number no top system has. Number is expressed by words,
syntax, morphology and suppletion, and by three arrangements that add no values outside the
typology: inverse marking, minimal-augmented paradigms, and numbers constructed from two
coarser markings. In syntax, controller and target numbers may differ in system, in default,
or for particular controllers, the corporate nouns of English and the honorific plurals of
Slavonic taking semantic agreement in the measure the Agreement Hierarchy and the Predicate
Hierarchy allow; conjoined noun phrases take agreement with the nearest conjunct or with all,
resolved to the dual for two singulars where there is one and to the plural otherwise,
resolution favoured by animacy and precedence. Verbal number, of events or of participants,
is a category apart. The book's examples are the rows of `Data/Examples/Corbett2000.json`.

## Implementation notes

* A system is the book's sequence of binary choices: a shape, how many determinate and how
  many indeterminate choices are made and whether a greater plural is, with the kind of
  general number and how many final choices are facultative. The substrate's system, its
  values and its facultative list, is derived from the choices, and the substrate's
  implicational universals hold of every system by enumeration of the finite type of shapes.
* A range is a function from the substrate's animacy ranks, whose order puts the speaker at
  the top and whose discrete inanimates are the book's inanimate position, to a three-way
  marking; constraint III of chapter 3 is monotonicity, the top-segment constraint I a
  theorem of it, and constraints I–III of chapter 4 are read as a pointwise order between
  successive choices, which is stronger than their letter. The optional marking of chapter 3,
  Kannada's or Comanche's, is the general number of a second system in chapter 4, not a
  facultative value: the profiles carry chapter 3's presentation, the second systems chapter
  4's.
* Corporate nouns and the honorific plurals reuse the hybrid profiles and availabilities of
  Corbett's typology of gender; the Predicate Hierarchy is a linear order on the predicate's
  four sub-positions, and the rows of Table 6.11 are profiles over it.
* Number resolution is the book's rule and is shown to be the substrate's lattice
  resolution coarsened to the system; the corpus tables are typed here, in percentages,
  with the book's readings of them as theorems.
* Second systems and constructed numbers are represented by what their forms cover; the
  data of Kiowa, Hopi, Rembarrnga and the Slavonic honorifics live here for want of
  fragments.

## TODO

* Japanese's table of plural marking by referent and noun-phrase type, the count and mass
  effects of §3.6 and §3.7, distributives and collectives, agreement with quantified
  expressions, the special uses of chapter 7 and verbal number are prose only.
* Constraint IV, the relative size of a minor number, Table 5.22's defectives, the mass
  form of the dialects of north-west Spain, which has no value in the substrate, and the
  irregular plurals of Bayso are not modelled.

## References

* [G. G. Corbett, *Number* (2000)][corbett-2000]
* [G. G. Corbett, *Gender* (1991)][corbett-1991]
* [G. G. Corbett, *Morphology and agreement* (1998)][corbett-1998]
* [G. G. Corbett, *The agreement hierarchy* (1979)][corbett-1979]
* [B. Comrie, *Polite plurals and predicate agreement* (1975)][comrie-1975]
* [T. C. Smith-Stark, *The plurality split* (1974)][smith-stark-1974]
* [J. H. Greenberg, *Some universals of grammar* (1963)][greenberg-1963]
* [G. G. Corbett, R. J. Hayward, *Gender and number in Bayso* (1987)][corbett-hayward-1987]
-/

namespace Corbett2000

open Agreement Corbett1991 Features.Prominence

/-- Singular, dual and plural. -/
def sgDuPl : List Number := [.singular, .dual, .plural]

/-! ### Number values and systems (chapter 2) -/

/-- The shape of a system, the choices that fix its values: how many of the determinate
values, dual then trial, divide the plural; how many paucals, a paucal then a greater paucal,
divide it further; and whether a greater plural does. -/
structure Shape where
  /-- The determinate choices made, in order: none, the dual, the dual and the trial. -/
  determinate : Fin 3 := 0
  /-- The indeterminate choices: none, a paucal, a paucal and a greater paucal. -/
  indeterminate : Fin 3 := 0
  /-- Whether the plural is divided by a greater plural. -/
  greaterPlural : Bool := false
  deriving DecidableEq, Repr, Fintype

namespace Shape

/-- The values of a shape in order, the singular and plural with the choices between. -/
def values (s : Shape) : List Number :=
  .singular :: ([Number.dual, .trial].take s.determinate ++
    [Number.paucal, .greaterPaucal].take s.indeterminate ++
      .plural :: (if s.greaterPlural then [.greaterPlural] else []))

/-- The plural's lower bound: three or more with a dual, four or more with a trial. -/
def pluralFloor (s : Shape) : ℕ := 2 + s.determinate

/-- A determinate cardinality below the plural's floor has its own value. -/
theorem fromCard_mem_values (s : Shape) {n : ℕ} (h₀ : 0 < n) (h : n < s.pluralFloor) :
    Number.fromCard n ∈ s.values := by
  have h₄ : n < 4 := by have := s.determinate.isLt; unfold pluralFloor at h; omega
  obtain ⟨d, p, gp⟩ := s
  revert h₀ h
  interval_cases n <;> revert d p gp <;> decide

end Shape

/-- How general number, the meaning outside the number system, is expressed: not at all;
by a form of its own, as in Bayso; or by the singular's form, as in Japanese. General
meaning in the plural's form is found for particular nouns, in Arbore, never as a system. -/
inductive General where
  | none
  | separate
  | withSingular
  deriving DecidableEq, Repr, Fintype

/-- A number system as the book's sequence of binary choices: its shape, the kind of general
number, and how many of the choices, counted from the last, are facultative. -/
structure Choices extends Shape where
  /-- The kind of general number. -/
  general : General := .none
  /-- How many of the choices, from the last, are facultative; all of them when the count
  exceeds them. -/
  facultative : Fin 6 := 0
  deriving DecidableEq, Repr, Fintype

namespace Choices

/-- The values the choices carve from the plural, in the order they are made. -/
def divisions (c : Choices) : List Number :=
  c.values.filter λ v => v ≠ .singular ∧ v ≠ .plural

/-- The facultative values: the last choices. -/
def facultativeValues (c : Choices) : List Number :=
  c.divisions.drop (c.divisions.length - c.facultative)

/-- The substrate's system. -/
def toSystem (c : Choices) (name : String) : Number.System :=
  { name := name, values := c.values, hasGeneral := decide (c.general ≠ .none),
    facultative := c.facultativeValues }

/-- Facultative choices are the last ones. -/
theorem facultativeValues_suffix (c : Choices) : c.facultativeValues <:+ c.divisions :=
  List.drop_suffix _ _

/-- Greenberg's implicational universals of number, as the substrate states them: every
sequence of choices is a well-formed system ([greenberg-1963]). -/
theorem toSystem_wellFormed (c : Choices) (name : String) : (c.toSystem name).WellFormed := by
  obtain ⟨⟨d, p, gp⟩, g, f⟩ := c
  change ((Choices.mk ⟨d, p, gp⟩ .none 0).toSystem "").WellFormed
  fin_cases d <;> fin_cases p <;> cases gp <;> decide

/-- Facultative use works up from the last choice, which the count from the last builds in:
there could not be a language like Longgu with the plural for the dual but not for the
paucal. -/
theorem paucal_mem_facultativeValues_of_dual_mem (c : Choices)
    (hd : .dual ∈ c.facultativeValues) (hp : .paucal ∈ c.divisions) :
    .paucal ∈ c.facultativeValues := by
  obtain ⟨⟨d, p, gp⟩, g, f⟩ := c
  revert d p gp f hd hp
  cases g <;> decide

end Choices

/-- Russian: singular and plural, all obligatory. -/
def russian : Choices := {}

/-- English: Russian's system. -/
def english : Choices := russian

/-- Sanskrit: an obligatory dual. -/
def sanskrit : Choices := { determinate := 1 }

/-- Upper Sorbian: Sanskrit's system. -/
def upperSorbian : Choices := sanskrit

/-- Slovene: the dual facultative. -/
def slovene : Choices := { determinate := 1, facultative := 1 }

/-- Dual and trial, all obligatory: Maŋarayi, and Tuyuca's conflated system. -/
def dualTrial : Choices := { determinate := 2 }

/-- Ngan'gityemerri: dual and trial, the trial facultative. -/
def ngangityemerri : Choices := { determinate := 2, facultative := 1 }

/-- Larike: dual and trial, both facultative. -/
def larike : Choices := { determinate := 2, facultative := 2 }

/-- Yimas: dual and paucal. -/
def yimas : Choices := { determinate := 1, indeterminate := 1 }

/-- Longgu: dual and paucal, both facultative in the subject pronouns. -/
def longgu : Choices := { determinate := 1, indeterminate := 1, facultative := 2 }

/-- Walapai: paucal and plural, the system Bayso's nouns oppose to their general number. -/
def walapai : Choices := { indeterminate := 1 }

/-- Bayso: Walapai's values with a general number of its own. -/
def bayso : Choices := { walapai with general := .separate }

/-- Lihir: dual, trial and paucal. -/
def lihir : Choices := { determinate := 2, indeterminate := 1 }

/-- Marshallese: Lihir's system with every choice facultative. -/
def marshallese : Choices := { determinate := 2, indeterminate := 1, facultative := 3 }

/-- Sursurunga: dual and two paucals; Figure 2.7 misprints the greater paucal as a greater
plural, against §2.2.5 and the position of the branch. -/
def sursurunga : Choices := { determinate := 1, indeterminate := 2 }

/-- Mokilese: dual and a greater plural. -/
def mokilese : Choices := { determinate := 1, greaterPlural := true }

/-- Mele-Fila: dual, paucal and greater plural, constructed from article and pronoun. -/
def meleFila : Choices := { determinate := 1, indeterminate := 1, greaterPlural := true }

/-- Kaytetye: dual and greater plural, the general number sharing the singular's form. -/
def kaytetye : Choices := { determinate := 1, greaterPlural := true, general := .withSingular }

/-- Japanese: general number in the singular's form. -/
def japanese : Choices := { general := .withSingular }

/-- Hamer: a general form of its own, singular, plural and global plural. -/
def hamer : Choices := { greaterPlural := true, general := .separate }

/-- Pirahã: no number at all. -/
def piraha : Number.System := { name := "Pirahã", values := [] }

/-- Rembarrnga: minimal, unit augmented and augmented, Table 5.18. -/
def rembarrnga : Number.System :=
  { name := "Rembarrnga", values := [.minimal, .unitAugmented, .augmented] }

/-- Ilocano: minimal and augmented, Table 5.20. -/
def ilocano : Number.System := { name := "Ilocano", values := [.minimal, .augmented] }

/-! ### The Animacy Hierarchy (chapters 3 and 4) -/

/-- Whether a number value is distinguished at a position of the hierarchy: obligatorily,
optionally, or not at all, ordered by the likelihood of number being distinguished. -/
inductive Marking where
  | excluded
  | optional
  | obligatory
  deriving DecidableEq, Repr, Fintype

namespace Marking

/-- The position of a marking in the order of likelihood. -/
def toNat : Marking → ℕ
  | .excluded => 0
  | .optional => 1
  | .obligatory => 2

theorem toNat_injective : Function.Injective toNat := by decide

instance : LinearOrder Marking := LinearOrder.lift' toNat toNat_injective

instance : OrderBot Marking where
  bot := .excluded
  bot_le m := by cases m <;> decide

end Marking

/-- The range of a number value: its marking at each position of the hierarchy. -/
abbrev Range := AnimacyRank → Marking

namespace Range

/-- Constraint III: rightwards along the hierarchy, downwards in the substrate's order, the
likelihood of number being distinguished never increases. -/
abbrev Respects (r : Range) : Prop := Monotone r

/-- Constraint I follows: the positions where a value is distinguished form a top segment. -/
theorem Respects.isUpperSet {r : Range} (h : r.Respects) : IsUpperSet {p | ⊥ < r p} :=
  (isUpperSet_Ioi _).preimage h

/-- The range obligatory down to `o`, optional down to `f`, excluded below. -/
def downTo (o f : AnimacyRank) : Range :=
  λ p => if o ≤ p then .obligatory else if f ≤ p then .optional else ⊥

/-- Every such range respects the hierarchy. -/
theorem downTo_respects (o f : AnimacyRank) : (downTo o f).Respects := by
  revert o f; decide

end Range

/-- The ranges of a language's number values, from the plural on through its choices. -/
structure Profile where
  /-- The language. -/
  language : String
  /-- Its system. -/
  system : Choices
  /-- The range of each value. -/
  range : Number → Range

/-- Constraints I to III of chapter 4, with III of chapter 3: every range respects the
hierarchy, and each choice's range is nowhere wider than the previous choice's, facultative
use counting as narrower than obligatory. -/
def Profile.Respects (p : Profile) : Prop :=
  (∀ v ∈ (.plural :: p.system.divisions), (p.range v).Respects) ∧
    List.IsChain (λ v w => ∀ q, p.range w q ≤ p.range v q) (.plural :: p.system.divisions)

instance (p : Profile) : Decidable p.Respects := by unfold Profile.Respects; infer_instance

/-- The plural and the dual over the same nominals, Figure 4.2. -/
def mansi : Profile :=
  ⟨"Mansi", sanskrit,
    λ | .plural | .dual => .downTo .discreteInanimate .discreteInanimate | _ => ⊥⟩

/-- The dual in the first person only, Figure 4.3. -/
def arapesh : Profile :=
  ⟨"Arapesh", sanskrit,
    λ | .plural => .downTo .discreteInanimate .discreteInanimate
      | .dual => .downTo .speaker .speaker | _ => ⊥⟩

/-- Pronouns with three numbers, nine nouns, mainly kin, with two, Figure 4.4. -/
def maori : Profile :=
  ⟨"Maori", sanskrit,
    λ | .plural => .downTo .kin .kin | .dual => .downTo .thirdPerson .thirdPerson | _ => ⊥⟩

/-- The paucal on pronouns only, Figure 4.6. -/
def yimasProfile : Profile :=
  ⟨"Yimas", yimas,
    λ | .plural | .dual => .downTo .discreteInanimate .discreteInanimate
      | .paucal => .downTo .thirdPerson .thirdPerson | _ => ⊥⟩

/-- The dual and the paucal for humans and higher animals, Figure 4.7. -/
def manam : Profile :=
  ⟨"Manam", yimas,
    λ | .plural => .downTo .discreteInanimate .discreteInanimate
      | .dual | .paucal => .downTo .higherAnimal .higherAnimal | _ => ⊥⟩

/-- The dual obligatory for pronouns and facultative for nouns, Figure 4.8. -/
def sloveneProfile : Profile :=
  ⟨"Slovene", slovene,
    λ | .plural => .downTo .discreteInanimate .discreteInanimate
      | .dual => .downTo .thirdPerson .discreteInanimate | _ => ⊥⟩

/-- The plural obligatory down to humans and optional below. -/
def kannada : Profile :=
  ⟨"Kannada", russian, λ | .plural => .downTo .human .discreteInanimate | _ => ⊥⟩

/-- Pronouns obligatory; the plural suffix optional for humans, and for dogs as a lexical
exception the book declines to make a position. -/
def slave : Profile :=
  ⟨"Slave", russian, λ | .plural => .downTo .thirdPerson .human | _ => ⊥⟩

/-- Dual and plural obligatory for humans, optional for animates, seldom for inanimates. -/
def comanche : Profile :=
  ⟨"Comanche", sanskrit, λ | .plural | .dual => .downTo .human .discreteInanimate | _ => ⊥⟩

/-- The profiles of chapters 3 and 4. -/
def profiles : List Profile :=
  [mansi, arapesh, maori, yimasProfile, manam, sloveneProfile, kannada, slave, comanche]

theorem profiles_respect : ∀ p ∈ profiles, p.Respects := by decide

/-- Figure 4.5: a dual wider than the plural is impossible. -/
theorem not_respects_dual_wider :
    ¬ Profile.Respects ⟨"", sanskrit,
      λ | .plural => .downTo .speaker .speaker
        | .dual => .downTo .discreteInanimate .discreteInanimate | _ => ⊥⟩ := by
  decide

/-- A facultative value is optional somewhere in its range; optional marking is not thereby
facultative: Slovene's dual against Kannada's plural, which is general number below humans. -/
theorem facultative_optional :
    (∀ v ∈ sloveneProfile.system.facultativeValues, ∃ p, sloveneProfile.range v p = .optional) ∧
      (∃ p, kannada.range .plural p = .optional) ∧
        .plural ∉ kannada.system.facultativeValues := by
  decide

/-- Mayali: number on the verb for humans, the minimal form for the rest. -/
def mayaliAgreement : Range := .downTo .human .human

/-- Miya, Table 3.6: number marking obligatory for humans and higher animals and optional
below. -/
def miyaMarking : Range := .downTo .higherAnimal .discreteInanimate

/-- Miya, Table 3.6: number agreement obligatory for humans and higher animals and excluded
below. -/
def miyaAgreement : Range := .downTo .higherAnimal .higherAnimal

/-- Muna: plural agreement obligatory for humans, optional for animates, excluded for
inanimates, which may carry a plural marker. -/
def munaAgreement : Range := .downTo .human .lowerAnimal

/-- Marking and agreement may split at different points, each in accord with the
hierarchy. -/
theorem tests_respect :
    miyaMarking.Respects ∧ miyaAgreement.Respects ∧ munaAgreement.Respects ∧
      mayaliAgreement.Respects := by
  decide

/-! ### Minor numbers (§4.2) -/

/-- Constraints VI and VII: a minor number's system, and the system without it, are both
possible systems of values. -/
def Dispensable (c : Choices) (minor : List Number) : Prop :=
  (∀ v ∈ minor, v ∈ c.divisions) ∧ ∃ s : Shape, s.values = c.values.filter (· ∉ minor)

instance (c : Choices) (minor : List Number) : Decidable (Dispensable c minor) := by
  unfold Dispensable; infer_instance

/-- The Hebrew and Maltese minor dual, Figure 4.11. -/
theorem hebrew_dispensable : Dispensable sanskrit [.dual] := by decide

/-- The Avar minor paucal, within the system Walapai has at the top. -/
theorem avar_dispensable : Dispensable walapai [.paucal] := by decide

/-- The Maŋarayi minor trial. -/
theorem mangarayi_dispensable : Dispensable dualTrial [.trial] := by decide

/-- Constraint VII excludes a minor dual beside a major trial. -/
theorem not_dispensable_dual_of_trial : ¬ Dispensable dualTrial [.dual] := by decide

/-- The Hebrew dual, on a few nouns for measures of time and facultative there. -/
def hebrewDual : Range := λ p => if p = .discreteInanimate then .optional else ⊥

/-- A minor number is not a top segment, constraint V placing it within the plural's range. -/
theorem hebrewDual_not_respects :
    ¬ hebrewDual.Respects ∧
      ∀ p, hebrewDual p ≤ Range.downTo .discreteInanimate .discreteInanimate p := by
  decide

/-! ### Top and second systems (§4.5) -/

/-- A second system, operating below the top system on the hierarchy: one of chapter 2's
systems, general number included, as Yimas's dual–plural nouns, Qafar's, Japanese's,
Kaytetye's and Bayso's general number; one conflating every value but the plural, constraint
IX, as Pame's and Kala Lagaw Ya's inanimates, Tuyuca's, and Larike's non-humans; or the mass
number of the dialects of north-west Spain. Constraint VIII, that conflated systems are
second systems, holds by construction. -/
inductive Second where
  | regular (c : Choices)
  | conflated (c : Choices)
  | mass
  deriving DecidableEq, Repr

/-- What each form of a second system covers: the general form beside the values of the
system it is opposed to; the mass form has no value in the substrate and is not listed. -/
def Second.cells : Second → List (Finset Number)
  | .regular c => (if c.general = .none then [] else [{.general}]) ++ c.values.map (λ v => {v})
  | .conflated c => [c.values.toFinset.erase .plural, {.plural}]
  | .mass => [{.singular}, {.plural}]

/-- Qafar's nouns, Figure 4.18: general number against singular and plural. -/
theorem qafar_cells :
    (Second.regular japanese).cells = [{.general}, {.singular}, {.plural}] := by decide

/-- Tuyuca's inanimates conflate three numbers against the plural, Figure 4.16. -/
theorem tuyuca_cells :
    (Second.conflated dualTrial).cells = [{.singular, .dual, .trial}, {.plural}] := by decide

/-! ### The expression of number (chapter 5) -/

namespace Kiowa

/-- The two main classes of noun, Table 5.13. -/
inductive Class where
  | animate
  | inanimate
  deriving DecidableEq, Repr, Fintype

/-- The basic, unmarked numbers of each class: one and two for animates, two and more for
inanimates. -/
def basic : Class → List Number
  | .animate => [.singular, .dual]
  | .inanimate => [.dual, .plural]

/-- The inverse suffix marks the number outside the basic ones. -/
def Inverse (k : Class) (n : Number) : Prop := n ∉ basic k

instance (k : Class) (n : Number) : Decidable (Inverse k n) := by unfold Inverse; infer_instance

/-- The object marking of the verb, (21) to (23), over the three numbers: singular, dual, or
inverse for the plural. -/
inductive ObjectMarker where
  | sg
  | du
  | inv
  deriving DecidableEq, Repr, Fintype

/-- The verb's object marker for each of the three numbers. -/
def verbObject : Number → ObjectMarker
  | .singular => .sg
  | .dual => .du
  | _ => .inv

/-- The noun conflates singular with dual for animates and dual with plural for inanimates,
while the verb keeps the three apart: a noun may show a system the verb never does. -/
theorem noun_conflates_verb_not :
    ¬ (sgDuPl.map λ n => decide (Inverse .animate n)).Nodup ∧
      ¬ (sgDuPl.map λ n => decide (Inverse .inanimate n)).Nodup ∧
        (sgDuPl.map verbObject).Nodup := by
  decide

end Kiowa

/-- The Teop articles, Table 5.15: the two classes of the fragment invert, singular *a*
against plural *o* and singular *o* against plural *a*, an inverse system which in the
fragment's two classes has the shape of the Somali article's polarity, Table 5.16. -/
theorem teop_inverse :
    Corbett1998.Polar (λ (g : Teop.Gender) (pl : Bool) => Teop.articleForm ⟨g, pl, false⟩) := by
  decide

namespace Rembarrnga

/-- The persons of the pronoun, the inclusive counted as one. -/
inductive Person where
  | first
  | firstInclusive
  | second
  | third
  deriving DecidableEq, Repr, Fintype

/-- The logical minimum of referents: two for the inclusive, one otherwise. -/
def minimum : Person → ℕ
  | .firstInclusive => 2
  | _ => 1

/-- The minimal-augmented analysis, Table 5.18: for at least the minimum of referents, the
form counts those beyond it. -/
def relative (p : Person) (n : ℕ) : Number :=
  match n - minimum p with
  | 0 => .minimal
  | 1 => .unitAugmented
  | _ => .augmented

/-- *-bbarrah* marks one more than the minimum: three referents for the inclusive, two for
the other persons, which the traditional labels split between trial and dual. -/
theorem unitAugmented_one_more :
    relative .firstInclusive 3 = relative .first 2 ∧ Number.fromCard 3 ≠ Number.fromCard 2 := by
  decide

end Rembarrnga

namespace Hopi

/-- The pronoun sets the singular against dual and plural, (40) to (42). -/
def pronounPlural : Number → Bool
  | .singular => false
  | _ => true

/-- The verb sets singular and dual against the plural. -/
def verbPlural : Number → Bool
  | .plural => true
  | _ => false

/-- Neither marking distinguishes the three numbers; together they construct the dual. -/
theorem constructed :
    ¬ (sgDuPl.map pronounPlural).Nodup ∧ ¬ (sgDuPl.map verbPlural).Nodup ∧
      (sgDuPl.map λ n => (pronounPlural n, verbPlural n)).Nodup := by
  decide

end Hopi

/-- Whether a noun distinguishes number semantically, syntactically by agreement, and
morphologically, Table 5.21. -/
structure Differentiability where
  /-- Individuals against collections of them. -/
  semantic : Bool
  /-- Distinct agreements. -/
  syntactic : Bool
  /-- Distinct forms. -/
  morphological : Bool
  deriving DecidableEq, Repr, Fintype

namespace Differentiability

/-- Morphological differentiation entails syntactic, and syntactic semantic. -/
abbrev Valid (d : Differentiability) : Prop :=
  (d.morphological → d.syntactic) ∧ (d.syntactic → d.semantic)

/-- *dog*: differentiated in every way. -/
def dog : Differentiability := ⟨true, true, true⟩

/-- *sheep*: no distinct forms. -/
def sheep : Differentiability := ⟨true, true, false⟩

/-- *scissors*: countable, one form and one agreement. -/
def scissors : Differentiability := ⟨true, false, false⟩

/-- *friendliness*: off the scale. -/
def friendliness : Differentiability := ⟨false, false, false⟩

/-- The four types of the table are the only ones. -/
theorem valid_iff (d : Differentiability) : d.Valid ↔ d ∈ [dog, sheep, scissors, friendliness] := by
  revert d; decide

end Differentiability

/-! ### The syntax of number (chapter 6) -/

/-- Bayso, Table 6.5: the three concords are the pronouns', masculine, feminine and plural. -/
theorem bayso_pronounConcord_surjective :
    Function.Surjective (Function.uncurry Bayso.Gender.pronounConcord) := by decide

/-- Four controller numbers and two genders fall together on the three concords. -/
theorem bayso_concord_not_injective :
    ¬ Function.Injective (Function.uncurry Bayso.Gender.concord) := by decide

/-- The default number, where the controller has none, is the singular in language after
language; Godié and Kiowa use the plural. -/
def defaultNumber : List (String × Number) :=
  [("English", .singular), ("Russian", .singular), ("Godié", .plural), ("Kiowa", .plural)]

/-! ### The Agreement Hierarchy (§6.2) -/

/-- British English *committee*: syntactic agreement only in attributive position, either
agreement elsewhere, (19) to (22). -/
def britishCommittee : Hybrid :=
  ⟨"committee (British English)",
    λ | .attributive => some .syntacticOnly | .predicate | .relativePronoun => some .both
      | .personalPronoun => some .both | .verb => none⟩

/-- American English *committee*: plural agreement rare in the predicate, admitted in the
personal pronoun. -/
def americanCommittee : Hybrid :=
  ⟨"committee (American English)",
    λ | .attributive => some .syntacticOnly | .predicate => some .mostlySyntactic
      | .personalPronoun => some .both | _ => none⟩

theorem committee_respectHierarchy :
    britishCommittee.RespectsHierarchy ∧ americanCommittee.RespectsHierarchy := by decide

/-- Nixon's corpus: the percentage of plural agreement with corporate nouns, by target, the
pronouns pooling the possessive with the personal. -/
def nixon : Target → Option ℚ
  | .attributive => some 0
  | .predicate => some (122 / 10)
  | .personalPronoun => some (274 / 10)
  | _ => none

/-- The plural is likelier in the pronoun than in the predicate, as the hierarchy predicts. -/
theorem nixon_increases :
    ∀ t u : Target, t ≤ u → ∀ a ∈ nixon t, ∀ b ∈ nixon u, b ≤ a := by
  decide +kernel

/-- The varieties of English. -/
inductive Variety where
  | british
  | american
  | newZealand
  deriving DecidableEq, Repr, Fintype

/-- Table 6.10: the percentage of respondents accepting *the audience were enjoying*. -/
def acceptance : Variety → ℚ
  | .british => 772 / 10
  | .american => 54 / 10
  | .newZealand => 725 / 10

/-- Few speakers of American English concur, most British and New Zealand ones do. -/
theorem acceptance_diverges :
    acceptance .american < acceptance .newZealand ∧
      acceptance .newZealand < acceptance .british := by
  norm_num [acceptance]

/-! ### The Predicate Hierarchy (§6.4) -/

/-- The sub-positions of the predicate, ordered by the likelihood of semantic agreement:
finite verb, participle, adjective, noun. -/
inductive PredicateTarget where
  | verb
  | participle
  | adjective
  | noun
  deriving DecidableEq, Repr, Fintype

namespace PredicateTarget

/-- The position of a target in the Predicate Hierarchy. -/
def rank : PredicateTarget → ℕ
  | .verb => 0
  | .participle => 1
  | .adjective => 2
  | .noun => 3

theorem rank_injective : Function.Injective rank := by decide

instance : LinearOrder PredicateTarget := LinearOrder.lift' rank rank_injective

end PredicateTarget

/-- Agreement with the honorific plural *vy* in a Slavonic language, Table 6.11: the
availability of singular, semantic, agreement at each sub-position. -/
structure Honorific where
  /-- The language. -/
  language : String
  /-- The availability of semantic agreement at each sub-position. -/
  profile : PredicateTarget → Availability

namespace Honorific

/-- A row of the table: the language and its four sub-positions. -/
def ofRow (language : String) (v p a n : Availability) : Honorific :=
  ⟨language, λ | .verb => v | .participle => p | .adjective => a | .noun => n⟩

/-- The Predicate Hierarchy: rightwards, the likelihood of semantic agreement never
decreases. -/
abbrev Respects (h : Honorific) : Prop := Monotone h.profile

end Honorific

/-- Macedonian, (28) to (30): the verb and participle plural, the adjective singular for
preference, the noun singular. -/
def macedonian : Honorific :=
  .ofRow "Macedonian" .syntacticOnly .syntacticOnly .mostlySemantic .semanticOnly

/-- The rows of Table 6.11, the Russian adjective split into its short and long forms; the
table prints Slovene's adjective as *pl(SG)* for *pl/(SG)*. -/
def slavonic : List Honorific :=
  [.ofRow "Czech" .syntacticOnly .mostlySemantic .mostlySemantic .semanticOnly,
    .ofRow "Slovak" .syntacticOnly .mostlySyntactic .semanticOnly .semanticOnly,
    .ofRow "Lower Sorbian" .syntacticOnly .syntacticOnly .both .semanticOnly,
    .ofRow "Upper Sorbian" .syntacticOnly .mostlySemantic .mostlySemantic .semanticOnly,
    .ofRow "Polish dialects" .syntacticOnly .both .both .semanticOnly,
    .ofRow "Bulgarian" .syntacticOnly .mostlySyntactic .mostlySemantic .semanticOnly,
    macedonian,
    .ofRow "Serbo-Croat" .syntacticOnly .syntacticOnly .mostlySyntactic .semanticOnly,
    .ofRow "Slovene" .syntacticOnly .mostlySyntactic .mostlySyntactic .semanticOnly,
    .ofRow "Ukrainian" .syntacticOnly .mostlySyntactic .mostlySemantic .semanticOnly,
    .ofRow "Belarusian" .syntacticOnly .syntacticOnly .semanticOnly .semanticOnly,
    .ofRow "Russian, short-form adjective"
      .syntacticOnly .syntacticOnly .mostlySyntactic .semanticOnly,
    .ofRow "Russian, long-form adjective"
      .syntacticOnly .syntacticOnly .mostlySemantic .semanticOnly]

theorem slavonic_respect : ∀ h ∈ slavonic, h.Respects := by decide

/-! ### Conjoined noun phrases (§6.5) -/

/-- The options for agreement with conjoined noun phrases: with the nearest conjunct, with
the first when it is not the nearest, rarely, or with all conjuncts by resolution; never
with the last, most distant, conjunct. -/
inductive ConjunctAgreement where
  | nearest
  | first
  | all
  deriving DecidableEq, Repr, Fintype

/-- The number resolution rules: the dual for exactly two singular conjuncts where the
system has a dual, the plural in all other cases. -/
def resolveNumber (c : Choices) (ns : List Number) : Number :=
  if .dual ∈ c.values ∧ ns = [.singular, .singular] then .dual else .plural

/-- The rule is the substrate's lattice resolution coarsened to the system, in Slovene as in
English. -/
theorem resolveNumber_eq_resolve :
    (∀ a ∈ slovene.values, ∀ b ∈ slovene.values,
      resolveNumber slovene [a, b] = (slovene.toSystem "Slovene").resolve a b) ∧
      ∀ a ∈ english.values, ∀ b ∈ english.values,
        resolveNumber english [a, b] = (english.toSystem "English").resolve a b := by
  decide

/-- Table 6.12: the percentage of number resolution with Russian conjoined noun phrases, by
target. -/
def russianConjoined : Target → Option ℚ
  | .attributive => some 12
  | .predicate => some 70
  | .relativePronoun => some 100
  | .personalPronoun => some 100
  | .verb => none

/-- Resolved forms increase monotonically along the Agreement Hierarchy. -/
theorem russianConjoined_increases :
    ∀ t u : Target, t ≤ u → ∀ a ∈ russianConjoined t, ∀ b ∈ russianConjoined u, b ≤ a := by
  decide

/-- Table 6.13: the percentage of plural predicates with conjoined subjects, by the animacy
of the conjuncts and their position relative to the predicate. -/
structure Resolution where
  /-- The language. -/
  language : String
  /-- Animate conjuncts before the predicate. -/
  animateBefore : ℕ
  /-- Inanimate conjuncts before the predicate. -/
  inanimateBefore : ℕ
  /-- Animate conjuncts after the predicate. -/
  animateAfter : ℕ
  /-- Inanimate conjuncts after the predicate. -/
  inanimateAfter : ℕ
  deriving DecidableEq, Repr

/-- Medieval Spanish, Table 6.13. -/
def spanishResolution : Resolution := ⟨"Medieval Spanish", 96, 31, 69, 6⟩

/-- German, Table 6.13. -/
def germanResolution : Resolution := ⟨"German", 96, 67, 93, 40⟩

/-- Russian, Table 6.13. -/
def russianResolution : Resolution := ⟨"Russian", 100, 85, 84, 28⟩

/-- Serbo-Croat, Table 6.13. -/
def serboCroatResolution : Resolution := ⟨"Serbo-Croat", 100, 91, 70, 26⟩

/-- The rows of Table 6.13. -/
def resolutionRates : List Resolution :=
  [spanishResolution, germanResolution, russianResolution, serboCroatResolution]

/-- Animacy and precedence each favour resolution, in every language of the table. -/
theorem factors_favour_resolution :
    ∀ r ∈ resolutionRates,
      r.inanimateBefore < r.animateBefore ∧ r.animateAfter < r.animateBefore ∧
        r.inanimateAfter < r.animateAfter ∧ r.inanimateAfter < r.inanimateBefore := by
  decide

/-- Animacy outweighs precedence in Medieval Spanish and German, precedence animacy in
Serbo-Croat. -/
theorem animacy_vs_precedence :
    spanishResolution.inanimateBefore < spanishResolution.animateAfter ∧
      germanResolution.inanimateBefore < germanResolution.animateAfter ∧
        serboCroatResolution.animateAfter < serboCroatResolution.inanimateBefore := by
  decide

/-! ### The book's examples -/

/-- The controller numbers by name. -/
def numberNames : List (String × Number) :=
  [("general", .general), ("singular", .singular), ("dual", .dual), ("trial", .trial),
    ("paucal", .paucal), ("plural", .plural)]

/-- The positions of the hierarchy by name. -/
def rankNames : List (String × AnimacyRank) :=
  [("speaker", .speaker), ("addressee", .addressee), ("thirdPerson", .thirdPerson),
    ("kin", .kin), ("human", .human), ("higherAnimal", .higherAnimal),
    ("lowerAnimal", .lowerAnimal), ("discreteInanimate", .discreteInanimate),
    ("nondiscreteInanimate", .nondiscreteInanimate)]

/-- The markings by name. -/
def markingNames : List (String × Marking) :=
  [("obligatory", .obligatory), ("optional", .optional), ("excluded", .excluded)]

/-- Miya, (24) to (28): marking and agreement at each position are Table 3.6's. -/
theorem miya_rows : ∀ row ∈ Examples.all, row.language = "miya1266" →
    ∀ p ∈ row.parse? "position" rankNames,
      (∀ m ∈ row.parse? "marking" markingNames, m = miyaMarking p) ∧
        ∀ a ∈ row.parse? "agreement" markingNames, a = miyaAgreement p := by
  decide +kernel

/-- Muna, (21) to (23), and Mayali, (5) and (6): agreement at each position. -/
theorem agreement_rows : ∀ row ∈ Examples.all, ∀ p ∈ row.parse? "position" rankNames,
    ∀ a ∈ row.parse? "agreement" markingNames,
      (row.language = "muna1247" → a = munaAgreement p) ∧
        (row.language = "gunw1252" → a = mayaliAgreement p) := by
  decide +kernel

/-- Slave, (2) to (4): the optional plural suffix, for dogs as a lexical exception. -/
theorem slave_rows : ∀ row ∈ Examples.all, row.language = "slav1253" →
    ∀ p ∈ row.parse? "position" rankNames, ∀ m ∈ row.parse? "marking" markingNames,
      m = slave.range .plural p ∨ p = .higherAnimal := by
  decide +kernel

/-- Hebrew, (1) to (3) of chapter 4: the target's number is the controller's coarsened to the
pronouns' system. -/
theorem hebrew_rows : ∀ row ∈ Examples.all, row.language = "hebr1245" →
    ∀ c ∈ row.parse? "controller" numberNames, ∀ t ∈ row.parse? "target" numberNames,
      Number.coarsenTo [.singular, .plural] c = t := by
  decide +kernel

/-- The default number of English and Kiowa, (12) and (14) of chapter 6. -/
theorem default_rows : ∀ row ∈ Examples.all, ∀ d ∈ row.parse? "default" numberNames,
    ∀ l ∈ row.parse? "language" [("stan1293", "English"), ("kiow1266", "Kiowa")],
      (l, d) ∈ defaultNumber := by
  decide +kernel

/-- Bayso, (1) to (4) of chapter 2 and (4) to (11) of chapter 6: the noun's form in each
number, and the concord it takes. -/
theorem bayso_rows : ∀ row ∈ Examples.all, row.language = "bais1246" →
    ∀ n ∈ row.parse? "noun" (Bayso.allNouns.map λ n => (n.form, n)),
    ∀ v ∈ row.parse? "number" [("general", Bayso.Value.general), ("singular", .singular),
      ("paucal", .paucal), ("plural", .plural)],
      (∀ f ∈ row.feature? "form", f = n.formAt v) ∧
        ∀ c ∈ row.parse? "concord" [("masc", Bayso.Concord.masc), ("fem", .fem),
          ("plural", .plural)], c = n.gender.concord v := by
  decide +kernel

/-- Slovene, (34) to (37): the predicate's number is the resolution of the conjuncts'. -/
theorem slovene_rows : ∀ row ∈ Examples.all, row.language = "slov1268" →
    ∀ cs ∈ row.parse? "conjuncts" [("sg+sg", [Number.singular, .singular]),
      ("du+sg", [.dual, .singular]), ("sg+sg+sg", [.singular, .singular, .singular])],
    ∀ r ∈ row.parse? "resolved" numberNames, r = resolveNumber slovene cs := by
  decide +kernel

/-- Macedonian, (28) to (30): each sub-position's agreement is one its availability allows;
the book prints no starred form, so the rows are all acceptable. -/
theorem macedonian_rows : ∀ row ∈ Examples.all, row.language = "mace1250" →
    ∀ t ∈ row.parse? "target" [("verb", PredicateTarget.verb), ("participle", .participle),
      ("adjective", .adjective), ("noun", .noun)],
    ∀ k ∈ row.parse? "agreement" [("plural", AgreementKind.syntactic), ("singular", .semantic)],
      (row.judgment = .acceptable ↔ (macedonian.profile t).Allows k) := by
  decide +kernel

/-- British *committee*, (19) to (22): the agreement each target allows. -/
theorem committee_rows : ∀ row ∈ Examples.all, row.language = "stan1293" →
    ∀ t ∈ row.parse? "target" targetNames, ∀ k ∈ row.parse? "agreement" kindNames,
    ∀ a ∈ britishCommittee.profile t, (row.judgment = .acceptable ↔ a.Allows k) := by
  decide +kernel

/-- Hopi, (40) to (42): the number read off the pronoun's and the verb's marking. -/
theorem hopi_rows : ∀ row ∈ Examples.all, row.language = "hopi1249" →
    ∀ p ∈ row.parse? "pronoun" [("sg", false), ("pl", true)],
    ∀ v ∈ row.parse? "verb" [("sg", false), ("pl", true)],
    ∀ n ∈ row.parse? "number" numberNames,
      Hopi.pronounPlural n = p ∧ Hopi.verbPlural n = v := by
  decide +kernel

/-- Kiowa, (21) to (23): the inverse suffix appears off the class's basic numbers. -/
theorem kiowa_rows : ∀ row ∈ Examples.all, row.language = "kiow1266" →
    ∀ k ∈ row.parse? "class" [("animate", Kiowa.Class.animate), ("inanimate", .inanimate)],
    ∀ n ∈ row.parse? "number" numberNames,
    ∀ i ∈ row.parse? "inverse" [("yes", true), ("no", false)],
      (i = true ↔ Kiowa.Inverse k n) := by
  decide +kernel

/-- Hungarian, (40) and (41): plural resolution only with animate conjuncts. -/
theorem hungarian_rows : ∀ row ∈ Examples.all, row.language = "hung1274" →
    ∀ an ∈ row.parse? "animate" [("yes", true), ("no", false)],
    ∀ r ∈ row.parse? "agreement" numberNames,
      (row.judgment = .acceptable ↔ (r = .singular ∨ an = true)) := by
  decide +kernel

/-- Moroccan Arabic, (42) to (44): agreement with the nearer conjunct only when the verb
precedes. -/
theorem moroccan_rows : ∀ row ∈ Examples.all, row.language = "moro1292" →
    ∀ vf ∈ row.parse? "verbFirst" [("yes", true), ("no", false)],
    ∀ a ∈ row.parse? "conjunctAgreement" [("nearest", ConjunctAgreement.nearest), ("all", .all)],
      (row.judgment = .acceptable ↔ (a = .all ∨ vf = true)) := by
  decide +kernel

end Corbett2000
