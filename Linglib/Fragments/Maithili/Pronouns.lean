module

public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Maithili pronouns

The nominative and accusative personal pronouns of the Darbhanga variety of Maithili. The second
person has four honorific grades, of which the nonhonorific and the mid-honorific share *tõ* and
*tora*. The third person has two grades, which share the nominative *o* and differ in the
accusative.

## Main results

* `Maithili.Pronouns.gradeParadigm_addressee_eq_iff`: the second-person forms separate every pair
  of grades except the nonhonorific and the mid-honorific.
* `Maithili.Pronouns.gradeParadigm_other_inter`: the two third-person grades share only *o*.

## TODO

* The verbal agreement that separates the nonhonorific from the mid-honorific second person, and
  that *əpne* shares with *əhã*, is not recorded. With it, `gradeParadigm_addressee_eq_iff` gets
  its counterpart: the verb distinguishes the grades the pronouns do not.

## References

* [P. Kumari and P. Chandra, *Honorificity Feature as an Enabler: Bridging the Person Gap*
  (2026)][kumari-chandra-2026]
-/

@[expose] public section

namespace Maithili

/-- The honorific grades of Maithili, lowest first, with the addressees [kumari-chandra-2026] gives
for each (pp. 120–121 and fns. 9–10). -/
inductive Grade where
  /-- The nonhonorific grade, to a younger sibling. -/
  | nonhonorific
  /-- The mid-honorific grade, to a younger relative once grown up or a younger stranger. -/
  | midHonorific
  /-- The honorific grade, to parents, teachers and anyone older. -/
  | honorific
  /-- The high honorific grade, to someone addressed formally, such as a high official. -/
  | highHonorific
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

open PersonalPronoun

/-- *həm*, 1sg nominative. -/
def ham : PersonalPronoun Grade :=
  { form := "həm", person := some .first, number := some .singular, case_ := some .nom }

/-- *həmra*, 1sg accusative. -/
def hamra : PersonalPronoun Grade :=
  { form := "həmra", person := some .first, number := some .singular, case_ := some .acc }

/-- *tõ*, 2sg nominative, nonhonorific and mid-honorific. -/
def toN : PersonalPronoun Grade :=
  { form := "tõ", person := some .second, number := some .singular, case_ := some .nom,
    grades := {.nonhonorific, .midHonorific} }

/-- *tora*, 2sg accusative, nonhonorific and mid-honorific. -/
def tora : PersonalPronoun Grade :=
  { form := "tora", person := some .second, number := some .singular, case_ := some .acc,
    grades := {.nonhonorific, .midHonorific} }

/-- *əhã*, 2sg nominative, honorific. -/
def ahaN : PersonalPronoun Grade :=
  { form := "əhã", person := some .second, number := some .singular, case_ := some .nom,
    grades := {.honorific} }

/-- *əhãke*, 2sg accusative, honorific. -/
def ahaNke : PersonalPronoun Grade :=
  { form := "əhãke", person := some .second, number := some .singular, case_ := some .acc,
    grades := {.honorific} }

/-- *əpne*, 2sg nominative, high honorific ([kumari-chandra-2026] fn. 10). -/
def apne : PersonalPronoun Grade :=
  { form := "əpne", person := some .second, number := some .singular, case_ := some .nom,
    grades := {.highHonorific} }

/-- *o*, 3sg nominative, nonhonorific and honorific. -/
def o : PersonalPronoun Grade :=
  { form := "o", person := some .third, number := some .singular, case_ := some .nom,
    grades := {.nonhonorific, .honorific} }

/-- *okra*, 3sg accusative, nonhonorific. -/
def okra : PersonalPronoun Grade :=
  { form := "okra", person := some .third, number := some .singular, case_ := some .acc,
    grades := {.nonhonorific} }

/-- *hunka*, 3sg accusative, honorific. -/
def hunka : PersonalPronoun Grade :=
  { form := "hunka", person := some .third, number := some .singular, case_ := some .acc,
    grades := {.honorific} }

/-- The pronoun inventory, [kumari-chandra-2026]'s Table 3 with *əpne*. -/
def pronouns : Finset (PersonalPronoun Grade) :=
  {ham, hamra, toN, tora, ahaN, ahaNke, apne, o, okra, hunka}

/-- Two second-person grades receive the same forms exactly when both are below the honorific:
*tõ* and *tora* serve the nonhonorific and the mid-honorific alike. -/
theorem gradeParadigm_addressee_eq_iff (g h : Grade) :
    gradeParadigm pronouns .addressee g = gradeParadigm pronouns .addressee h ↔
      g = h ∨ g < .honorific ∧ h < .honorific := by
  revert g h; decide

/-- The two third-person grades share the nominative *o* and nothing else. -/
theorem gradeParadigm_other_inter :
    gradeParadigm pronouns .other .nonhonorific ∩ gradeParadigm pronouns .other .honorific =
      {"o"} := by
  decide

/-- The honorific pronouns are those that do not also serve the nonhonorific grade. -/
theorem filter_isHonorific :
    pronouns.filter IsHonorific = {ahaN, ahaNke, apne, hunka} := by
  decide

/-- The second person realizes all four grades and the third person only two. -/
theorem grades_addressee_other :
    (pronouns.filter (.addressee ∈ ·.referential)).biUnion (·.grades) = Finset.univ ∧
      (pronouns.filter (.other ∈ ·.referential)).biUnion (·.grades) =
        {.nonhonorific, .honorific} := by
  decide

end Pronouns

end Maithili
