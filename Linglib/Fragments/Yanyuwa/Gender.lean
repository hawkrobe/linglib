module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Noun.Basic

/-!
# Yanyuwa gender

This file records the noun classes of Yanyuwa (Pama-Nyungan, Northern Territory), the prefixes
that agree with them, and the body-part nouns, after Kirton.

Kirton describes seven classes: female, male, feminine, masculine, food, arboreal and abstract.
Adjectives and numerals agree with a noun by a class prefix, and a body-part noun takes a prefix
for the person, number and class of its possessor. The prefixes depend on the sex of the speaker.
The female and feminine classes share their prefixes for every speaker, and in men's speech the
male and masculine classes do too. Only the female and male classes distinguish number.

## Implementation notes

* Prefixes are given in their nuclear forms. Kirton also lists referent and directive or
  accessory forms.
* The possessor prefixes are those of a third person singular possessor, which mark its class.

## References

* [kirton-1971a]
* [kirton-1971b]
-/

@[expose] public section

namespace Yanyuwa

/-- The noun classes, Kirton's classes 1 to 7. -/
inductive Gender where
  /-- Female humans, class 1. -/
  | female
  /-- Male humans, class 2. -/
  | male
  /-- Nonhuman females, among them many animals, class 3. -/
  | feminine
  /-- The masculine class, class 4. -/
  | masculine
  /-- Food, class 5. -/
  | food
  /-- Trees and plants, class 6. -/
  | arboreal
  /-- Abstract nouns, class 7. -/
  | abstract
  deriving DecidableEq, Repr, Fintype

/-- The female and male classes distinguish number; the others are invariant. -/
def Gender.HasNumber : Gender → Prop
  | .female | .male => True
  | _ => False

instance : DecidablePred Gender.HasNumber := fun g ↦ by cases g <;> unfold Gender.HasNumber <;>
  infer_instance

/-- The sex of the speaker. -/
inductive Speaker where
  | woman
  | man
  deriving DecidableEq, Repr, Fintype

/-- The class prefix of an adjective or numeral. The masculine class takes none, and in men's
speech neither does the male class. -/
def agreementPrefix : Speaker → Gender → String
  | _, .female | _, .feminine => "řa-"
  | .woman, .male => "nja-"
  | .man, .male | _, .masculine => ""
  | _, .food => "ma-"
  | _, .arboreal => "na-"
  | _, .abstract => "naṇu-"

/-- The prefix of a body-part noun for a possessor of each class. The abstract class has none.
Before a stem in *w* the male *niwa-* is *niya-*, and men also use *nula-* for the male class. -/
def possessorPrefix : Speaker → Gender → Option String
  | _, .female | _, .feminine => some "nanda-"
  | .woman, .male => some "niwa-"
  | .woman, .masculine => some "ni-"
  | .man, .male | .man, .masculine => some "na-"
  | _, .food => some "nu-"
  | _, .arboreal => some "nanu-"
  | _, .abstract => none

/-! ### Body-part nouns -/

/-- *malidji* 'finger'. -/
def malidji : Noun := ⟨"malidji", "finger"⟩

/-- *maṇḍa* 'foot'. -/
def «maṇḍa» : Noun := ⟨"maṇḍa", "foot"⟩

/-- *liřbi* 'scales'. -/
def «liřbi» : Noun := ⟨"liřbi", "scales"⟩

/-- *mulu* 'mouth'. -/
def mulu : Noun := ⟨"mulu", "mouth"⟩

/-- *wini* 'name'. -/
def wini : Noun := ⟨"wini", "name"⟩

/-- The body-part nouns, which take a possessor prefix, and *wini* 'name', which does too. -/
def bodyPartNouns : List Noun := [malidji, «maṇḍa», «liřbi», mulu, wini]

end Yanyuwa
