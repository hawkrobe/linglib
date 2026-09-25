module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Quantification.Counting
public import Linglib.Semantics.Denotation

/-!
# Czech determiner inventory

Czech has no articles, so definiteness goes unmarked, and the demonstrative *ten* is not the
obligatory exponent of any definite use. The inventory holds the demonstrative and the
quantificational determiners, the carrier `QuantityWord`, whose members project to a
`Quantifier` record and denote the readings available for them. Among them are the concord
item *žádný* 'no' and the positive polarity item *nějaký* 'some', whose polarity behaviour is
recorded on their `PolarityItem` entries in `PolarityItems.lean` and used by [stankova-2025]
to diagnose the position of negation in polar questions.

## References

* [stankova-2025]
-/

@[expose] public section

namespace Czech.Determiners

/-- *ten* 'that, the', the distance-neutral demonstrative. -/
def ten : DemonstrativeDeterminer := { form := "ten", deictic := .unspecified }

/-- The quantificational determiners: *každý* 'every', *žádný* 'no', *nějaký* 'some' and
*některý* 'some, certain'. -/
inductive QuantityWord where
  | kazdy | zadny | nejaky | nektery
  deriving DecidableEq, Repr, Fintype

namespace QuantityWord

/-- The surface form. -/
def form : QuantityWord → String
  | .kazdy => "každý"
  | .zadny => "žádný"
  | .nejaky => "nějaký"
  | .nektery => "některý"

/-- The grammatical number a word selects, which only *každý* fixes, to the singular. -/
def numberRestriction : QuantityWord → Option Number
  | .kazdy => some .singular
  | _ => none

/-- Whether a word selects mass nouns, which *žádný* and *nějaký* do. -/
def selectsMass : QuantityWord → Bool
  | .zadny | .nejaky => true
  | .kazdy | .nektery => false

/-- The word as a determiner record. -/
def toQuantifier (w : QuantityWord) : Quantifier :=
  { form := w.form, numberRestriction := w.numberRestriction, selectsMass := w.selectsMass }

/-- All the words. -/
def toList : List QuantityWord := [.kazdy, .zadny, .nejaky, .nektery]

universe u

/-- The readings available for a word. *Každý* reads as `every`, *žádný* as `no`, and *nějaký*
and *některý* as `Quantifier.GQ.some`, the partitive specificity of *některý* being no part of
its truth conditions. -/
instance : Semantics.Denotes QuantityWord (Set Quantifier.GQ.Family.{u}) where
  denote
    | .kazdy => {Quantifier.GQ.Family.every}
    | .zadny => {Quantifier.GQ.Family.no}
    | .nejaky | .nektery => {Quantifier.GQ.Family.some}

end QuantityWord

/-- The Czech determiners: the demonstrative and the quantifiers, with no article. -/
def inventory : Determiner.Inventory :=
  .demonstrative ten :: QuantityWord.toList.map (.quantifier ·.toQuantifier)

/-- Czech derives the `.unmarked` Moroney cell. -/
theorem marking : inventory.markingStrategy = .unmarked := by decide

end Czech.Determiners
