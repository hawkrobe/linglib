import Linglib.Syntax.Minimalist.Phi.PersonSpace
import Linglib.Morphology.Exponence.Select
import Linglib.Features.Person.Decomposition
import Linglib.Data.Examples.AckemaNeeleman2018

/-!
# Features of person

Ackema and Neeleman derive the inventory of persons from two privative features acting as
functions on a nested person space (`Minimalist.Phi.PersonSpace`): `DIST` selects the others
layer for the third person, `PROX` then `DIST` the addressee layer for the second, `PROX` twice the
innermost set for the first, and a single `PROX` the set of speaker and addressee for the
inclusive (`eval_third`, `eval_second`, `eval_first`, `eval_inclusive`). The reverse order is
incoherent and `PROX` cannot apply to the innermost set (`eval_incoherent`), so with number added
above person the seven attested pronouns are the structures the system generates; they map onto
Cysouw's categories with the inclusive undivided (`toCategory_inventory`), the inclusive has no
singular because `Sᵢ₊ᵤ` has two obligatory members (`inclusive_not_singular`), and every
number-blind spell-out rule treats the exclusive exactly as the first singular while one mentioning
two `PROX` separates them from the inclusive (`applies_exclusive_iff_first`,
`exists_applies_first_not_inclusive`).

Third person is a default without being featureless: `DIST` alone can deliver the empty set, so
only third person pronouns can be expletives (`exists_third_empty`, `first_second_nonempty`), and
plural is undefined on the empty set, so expletives are singular (`expletive_singular`); the
featureless pronoun denotes the whole space, whose two obligatory members keep it from being a
dummy and force number to apply above person (`whole_space_nontrivial`). Spell-out is governed by
Maximal Encoding — the applicable rule mentioning the most features wins (`realize`, through
`Morphology.Exponence.selectBy`): Dutch's strong subject pronouns realize the paradigm with one
form for both readings of the first plural (`dutch_paradigm`), whereas a vocabulary with a rule
mentioning two `PROX` splits the exclusive from the inclusive (`clusive_split`).

## References

* [ackema-neeleman-2018]
* [cysouw-2009]
* [harbour-2016]
* [bobaljik-2008]
-/

namespace AckemaNeeleman2018

open Minimalist.Phi Minimalist.Phi.PersonSpace Morphology.Exponence
open Person (Category)

variable {α : Type*}

/-! ### The inventory of persons -/

/-- Third person `[DIST]`. -/
def third : Spec := [.dist]

/-- Second person `[PROX–DIST]`. -/
def second : Spec := [.prox, .dist]

/-- First person `[PROX–PROX]`. -/
def first : Spec := [.prox, .prox]

/-- First person inclusive `[PROX]`. -/
def inclusive : Spec := [.prox]

theorem eval_third : third.eval = some .others := rfl

theorem eval_second : second.eval = some .addressees := rfl

theorem eval_first : first.eval = some .si := rfl

theorem eval_inclusive : inclusive.eval = some .siu := rfl

/-- `DIST` before `PROX` is incoherent, and `PROX` cannot apply to `Sᵢ`. -/
theorem eval_incoherent :
    Spec.eval [.dist, .prox] = none ∧ Spec.eval [.prox, .prox, .prox] = none :=
  ⟨rfl, rfl⟩

/-- `[PROX]` has no singular reading: `Sᵢ₊ᵤ` has two obligatory members. -/
theorem inclusive_not_singular (S : PersonSpace α) : ¬ (S.denote .siu).Subsingleton :=
  S.nontrivial_denote_siu.not_subsingleton

/-- A pronoun: a person structure under a number node, plural or not. -/
structure Pronoun where
  /-- The person feature structure. -/
  person : Spec
  /-- Whether the number node carries `PL`. -/
  plural : Bool
  deriving DecidableEq

/-- The seven attested pronouns: three singular, four plural. -/
def inventory : List Pronoun :=
  [⟨first, false⟩, ⟨second, false⟩, ⟨third, false⟩, ⟨inclusive, true⟩, ⟨first, true⟩,
    ⟨second, true⟩, ⟨third, true⟩]

/-- The typological category of a pronoun: Cysouw's inventory with the inclusive undivided,
its minimal/augmented split being a matter of number. -/
def Pronoun.toCategory (p : Pronoun) : Option Category :=
  p.person.eval.bind fun r =>
    match r, p.plural with
    | .si, false => some .s1
    | .si, true => some .excl
    | .siu, true => some .augIncl
    | .addressees, false => some .s2
    | .addressees, true => some .secondGrp
    | .others, false => some .s3
    | .others, true => some .thirdGrp
    | _, _ => none

/-- The inventory realizes every category but the minimal inclusive. -/
theorem toCategory_inventory :
    ∀ c ∈ Category.all, c ≠ .minIncl ↔ ∃ p ∈ inventory, p.toCategory = some c := by
  decide

theorem toCategory_inclusive_singular : (⟨inclusive, false⟩ : Pronoun).toCategory = none := rfl

/-! ### Third person as default -/

/-- `DIST` may deliver the empty set: expletives are third person. -/
theorem exists_third_empty : ∃ S : PersonSpace Bool, S.denote .others = ∅ :=
  exists_denote_others_eq_empty Bool.false_ne_true

/-- First and second person never denote the empty set. -/
theorem first_second_nonempty (S : PersonSpace α) :
    (S.denote .si).Nonempty ∧ (S.denote .addressees).Nonempty :=
  ⟨S.denote_nonempty (by decide), S.denote_nonempty (by decide)⟩

/-- Expletives are singular: plural is undefined on the empty set. -/
theorem expletive_singular (S : PersonSpace α) (h : S.denote .others = ∅) :
    ¬ S.PluralDefined .others :=
  S.not_pluralDefined_of_eq_empty h

theorem eval_nil : Spec.eval [] = some .siuo := rfl

/-- The featureless pronoun denotes the whole space, which has two obligatory members: it cannot
be a dummy, and number applied before person would always find a plurality, so plural is
undefined there. -/
theorem whole_space_nontrivial (S : PersonSpace α) :
    (S.denote .siuo).Nontrivial ∧ ¬ S.PluralDefined .siuo :=
  ⟨S.nontrivial_denote_siuo, S.not_pluralDefined_siuo⟩

/-! ### Spell-out and Maximal Encoding -/

/-- A spell-out rule: the person features it mentions, with multiplicity, whether it mentions
`PL`, and its form. -/
structure SpellOut (E : Type*) where
  /-- The person features mentioned. -/
  features : List Feature
  /-- Whether `PL` is mentioned. -/
  plural : Bool
  /-- The form inserted. -/
  form : E

variable {E : Type*}

/-- A rule applies to a pronoun whose structure contains every feature it mentions. -/
instance : Rule (SpellOut E) Pronoun E where
  exponent r := r.form
  Applies r p := (∀ f, r.features.count f ≤ p.person.count f) ∧ (r.plural = true → p.plural = true)

instance : DecidableRel (Applies : SpellOut E → Pronoun → Prop) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- Every number-blind rule applies to the exclusive exactly when it applies to the first
singular: the two share their person structure. -/
theorem applies_exclusive_iff_first (r : SpellOut E) (h : r.plural = false) :
    Applies r (⟨first, true⟩ : Pronoun) ↔ Applies r ⟨first, false⟩ := by
  simp [Applies, h]

/-- A rule mentioning two `PROX` applies to the first singular but not to the inclusive. -/
theorem exists_applies_first_not_inclusive (e : E) :
    ∃ r : SpellOut E, Applies r (⟨first, false⟩ : Pronoun) ∧ ¬ Applies r ⟨inclusive, true⟩ :=
  ⟨⟨[.prox, .prox], false, e⟩, ⟨fun _ => le_rfl, fun h => Bool.noConfusion h⟩, fun ⟨h, _⟩ =>
    absurd (h .prox) (show ¬ ([Feature.prox, .prox].count .prox ≤ inclusive.count .prox) by decide)⟩

/-- Maximal Encoding: the applicable rule mentioning the most features is used. -/
def realize (v : List (SpellOut E)) (p : Pronoun) : Option E :=
  Morphology.Exponence.realize (fun r => r.features.length + r.plural.toNat) v p

/-- The Dutch strong subject pronouns. -/
inductive DutchForm
  | ik
  | jij
  | hij
  | wij
  | jullie
  | zij
  deriving DecidableEq

/-- The Dutch spell-out rules: no rule mentions two `PROX`. -/
def dutch : List (SpellOut DutchForm) :=
  [⟨[.prox], false, .ik⟩, ⟨[.prox, .dist], false, .jij⟩, ⟨[.dist], false, .hij⟩,
    ⟨[.prox], true, .wij⟩, ⟨[.prox, .dist], true, .jullie⟩, ⟨[.dist], true, .zij⟩]

/-- The Dutch paradigm: the more specific rule blocks the less specific one, and one form
realizes both the inclusive and the exclusive. -/
theorem dutch_paradigm :
    inventory.map (realize dutch) =
      [some .ik, some .jij, some .hij, some .wij, some .wij, some .jullie, some .zij] := by
  decide

/-- A vocabulary distinguishing the readings of the first plural. -/
inductive ClusiveForm
  | exclusive
  | inclusive
  deriving DecidableEq

/-- Rules mentioning two and one `PROX` under `PL`. -/
def clusive : List (SpellOut ClusiveForm) :=
  [⟨[.prox, .prox], true, .exclusive⟩, ⟨[.prox], true, .inclusive⟩]

/-- The rule mentioning two `PROX` blocks the other on the exclusive and cannot apply to the
inclusive. -/
theorem clusive_split :
    realize clusive ⟨first, true⟩ = some .exclusive ∧
      realize clusive ⟨inclusive, true⟩ = some .inclusive := by
  decide

end AckemaNeeleman2018
