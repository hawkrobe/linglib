import Linglib.Syntax.Category.Determiner.Basic

/-!
# Czech determiner inventory

Czech has no articles: definiteness goes unmarked, and the demonstrative *ten* is not the
obligatory exponent of any definite use. The inventory holds the demonstrative and the
quantificational determiners, among them the concord item *žádný* 'no' and the positive
polarity item *nějaký* 'some', whose polarity behaviour is recorded on their
`Polarity.Item` entries in `PolarityItems.lean` and used by [stankova-2025] to diagnose
the position of negation in polar questions.

## References

* [stankova-2025]
-/

namespace Czech.Determiners

/-- *ten* 'that, the', the distance-neutral demonstrative. -/
def ten : DemonstrativeDeterminer := { form := "ten", deictic := .unspecified }

/-- *každý* 'every', universal over singular count nouns. -/
def kazdy : Quantifier := { form := "každý", numberRestriction := some .singular }

/-- *žádný* 'no', the negative concord determiner, accepting mass nouns. -/
def zadny : Quantifier := { form := "žádný", selectsMass := true }

/-- *nějaký* 'some', the positive polarity determiner, accepting mass nouns. -/
def nejaky : Quantifier := { form := "nějaký", selectsMass := true }

/-- *některý* 'some, certain', the partitive indefinite determiner. -/
def nektery : Quantifier := { form := "některý" }

/-- The Czech determiners: the demonstrative and the quantifiers, with no article. -/
def inventory : Determiner.Inventory :=
  [ .demonstrative ten, .quantifier kazdy, .quantifier zadny, .quantifier nejaky,
    .quantifier nektery ]

/-- Czech derives the `.unmarked` Moroney cell. -/
theorem marking : inventory.markingStrategy = .unmarked := by decide

end Czech.Determiners
