import Linglib.Syntax.Category.Determiner.Basic

/-!
# Thai determiner inventory

Thai patterns with Mandarin: bare nouns serve unique definites, the
demonstrative *nán* 'that' obligatorily expones anaphoric definites, and
possession is marked with *khɔ̌ɔng*.

## References

* [jenks-2015]
* [moroney-2021]
-/

namespace Thai.Determiners

/-- The Thai determiners are the demonstrative *nán*, the obligatory exponent
    of anaphoric definites, and the possessive *khɔ̌ɔng*. -/
def inventory : Determiner.Inventory :=
  [ .demonstrative { form := "nan", deictic := .distal, definiteUses := [.anaphoric] },
    .possessive { form := "khong" } ]

/-- Thai derives the `.markedAnaphoric` Moroney cell. -/
theorem marking : inventory.markingStrategy = .markedAnaphoric := by decide

end Thai.Determiners
