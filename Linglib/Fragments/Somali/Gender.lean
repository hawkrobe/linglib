import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Category.Noun.Basic

/-!
# Somali noun gender

Somali has two genders, masculine and feminine, shown on the definite article and on the
verb. The remote definite article is polar: the masculine singular and the feminine plural
take *-kii*, the feminine singular and the masculine plural *-tii*, so that changing gender
or number alone changes the article and changing both restores it. The verbal prefix is not:
*y-* for the masculine singular and for both plurals, *t-* for the feminine singular alone.
Masculine nouns with a reduplicated plural, *nin* ~ *niman* 'man', keep the singular article
in the plural ([saeed-1999]; [corbett-1998]).

## References

* [J. Saeed, *Somali* (1999)][saeed-1999]
* [G. G. Corbett, *Morphology and agreement* (1998)][corbett-1998]
-/

namespace Somali.Gender

/-- The two controller genders. -/
inductive Value where
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- The basic forms of the remote definite article; after a vowel other than *i*, *-kii* is
*-hii*, and after any vowel *-tii* is *-dii*. -/
inductive Article where
  | kii
  | tii
  deriving DecidableEq, Repr, Fintype

/-- The article by gender and number. -/
def Value.article : Value → Bool → Article
  | .masc, false | .fem, true => .kii
  | .fem, false | .masc, true => .tii

/-- The third-person subject prefix of the verb. -/
inductive VerbPrefix where
  | y
  | t
  deriving DecidableEq, Repr, Fintype

/-- The verbal prefix by gender and number. -/
def Value.verbPrefix : Value → Bool → VerbPrefix
  | .fem, false => .t
  | _, _ => .y

/-- A Somali noun with its gender, its plural stem, and whether that plural is reduplicated. -/
structure Noun extends GenderedNoun Value where
  /-- The plural stem. -/
  plural : String
  /-- Whether the plural is formed by reduplication, keeping the singular article. -/
  reduplicatedPlural : Bool
  deriving DecidableEq, Repr

/-- The article a noun takes in each number; a reduplicated plural keeps the singular's. -/
def Noun.article (n : Noun) (plural : Bool) : Article :=
  n.gender.article (plural && !n.reduplicatedPlural)

/-- *ìnan* 'boy'. -/
def inan : Noun := ⟨⟨⟨"ìnan", "boy"⟩, .masc, true⟩, "inammá", false⟩
/-- *inán* 'girl'. -/
def inan' : Noun := ⟨⟨⟨"inán", "girl"⟩, .fem, true⟩, "ináma", false⟩
/-- *nin* 'man', with the reduplicated plural *niman*. -/
def nin : Noun := ⟨⟨⟨"nin", "man"⟩, .masc, true⟩, "niman", true⟩

/-- The nouns the sources cite. -/
def allNouns : List Noun := [inan, inan', nin]

/-- The singular article alone distinguishes the two genders. -/
theorem faithful_article : Function.Injective (Value.article · false) := by decide

end Somali.Gender
