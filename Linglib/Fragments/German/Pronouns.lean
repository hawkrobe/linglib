import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Fragments.German.Case

/-!
# German pronouns

This file defines the German personal pronouns and the case paradigms of the interrogative
pronouns *wer* 'who' and *was* 'what', which also head free relatives.

The second person distinguishes a familiar register, *du* and *ihr*, from a polite one with
the single form *Sie*. *Sie* takes the third person plural series for agreement and reflexive
binding (*sich*, not *dich* or *euch*) while denoting the addressee alone or with others, so its
`person` is third and its `referential` categories are those of *du* and *ihr* together. *wer*
declines for the four German cases; *was* has one form for the nominative and the accusative and
no dative.

## Main definitions

* `German.Pronouns.pronouns` — the personal pronoun inventory
* `German.Pronouns.wer`, `German.Pronouns.was` — the interrogative paradigms, a form for each case

## Main results

* `German.Pronouns.addressee_register`, `German.Pronouns.addressee_formal`,
  `German.Pronouns.sie_formal_referential` — the addressee pronouns come in two registers,
  and the single polite form denotes what the two familiar forms denote together
* `German.Pronouns.wer_isSome_iff`, `German.Pronouns.was_isSome_iff` — the paradigms are
  defined on the German case inventory, *was* lacking the dative

## References

* [L. J. Adamson and S. Zompì, *Polite pronouns and the PCC* (2025)][adamson-zompi-2025]
* [M. Dalrymple and R. M. Kaplan, *Feature indeterminacy and feature resolution*
  (2000)][dalrymple-kaplan-2000]
-/

namespace German.Pronouns

/-! ### Personal pronouns -/

/-- The first person singular *ich*. -/
def ich : PersonalPronoun := { form := "ich", person := some .first, number := some .singular }

/-- The familiar second person singular *du*. -/
def du : PersonalPronoun := { form := "du", person := some .second, number := some .singular }

/-- The polite second person *Sie*, for one or several addressees. Its agreement person and
number are those of the third person plural; it denotes the addressee alone or with others
([adamson-zompi-2025]). -/
def sie_formal : PersonalPronoun :=
  { form := "Sie", person := some .third, number := some .plural, register := .formal,
    referential := {.addressee, .addresseeOthers} }

/-- The third person singular masculine *er*. -/
def er : PersonalPronoun :=
  { form := "er", person := some .third, number := some .singular, gender := some .masculine }

/-- The third person singular feminine *sie*. -/
def sie_sg : PersonalPronoun :=
  { form := "sie", person := some .third, number := some .singular, gender := some .feminine }

/-- The third person singular neuter *es*. -/
def es : PersonalPronoun :=
  { form := "es", person := some .third, number := some .singular, gender := some .neuter }

/-- The first person plural *wir*. -/
def wir : PersonalPronoun := { form := "wir", person := some .first, number := some .plural }

/-- The familiar second person plural *ihr*. -/
def ihr : PersonalPronoun := { form := "ihr", person := some .second, number := some .plural }

/-- The third person plural *sie*. -/
def sie_pl : PersonalPronoun := { form := "sie", person := some .third, number := some .plural }

/-- The personal pronoun inventory. -/
def pronouns : Finset PersonalPronoun := {ich, du, sie_formal, er, sie_sg, es, wir, ihr, sie_pl}

/-- The pronouns referring to the addressee come in a familiar and a polite register. -/
theorem addressee_register :
    (pronouns.filter (·.referentialPerson = some .second)).image (·.register) =
      {.informal, .formal} := by
  decide

/-- *Sie* is the only polite addressee pronoun. -/
theorem addressee_formal :
    pronouns.filter (λ p => p.referentialPerson = some .second ∧ p.register = .formal) =
      {sie_formal} := by
  decide

/-- The polite form denotes exactly what the two familiar forms denote between them: *Sie* is
number-neutral where the familiar register distinguishes *du* from *ihr*. -/
theorem sie_formal_referential : sie_formal.referential = du.referential ∪ ihr.referential := by
  decide

/-! ### Interrogative pronouns

The animate *wer* declines for the four German cases; the inanimate *was* has one form for the
nominative and the accusative and no dative. Each paradigm is a partial map from case to form, so
`Morphology.formCells` reads the cases a form realizes straight off it. -/

/-- The paradigm of *wer* 'who'. -/
def wer : Case → Option String
  | .nom => some "wer"
  | .acc => some "wen"
  | .dat => some "wem"
  | .gen => some "wessen"
  | _ => none

/-- The paradigm of *was* 'what'. -/
def was : Case → Option String
  | .nom | .acc => some "was"
  | .gen => some "wessen"
  | _ => none

/-- *wer* has a form for exactly the German cases. -/
theorem wer_isSome_iff (c : Case) : (wer c).isSome ↔ c ∈ German.Case.inventory := by
  cases c <;> decide

/-- *was* has a form for exactly the German cases other than the dative. -/
theorem was_isSome_iff (c : Case) :
    (was c).isSome ↔ c ∈ German.Case.inventory.erase .dat := by
  cases c <;> decide

end German.Pronouns
