module

public import Linglib.Syntax.Category.Coordinator

/-!
# Turkish coordinators

Turkish conjoins with the free word *ve* 'and', an Arabic loan, before the second coordinand,
and with the enclitic *de*, *da* by vowel harmony, which follows the first word of the second
coordinand, as in the example Haspelmath cites from Kornfilt. The enclitic is also the additive
particle 'also, too'.

## Main definitions

* `Turkish.Coordination.ve`, `Turkish.Coordination.de`: the conjunctive coordinator and the
  conjunctive enclitic.

## References

* [haspelmath-2007]
* [kornfilt-1997]
-/

@[expose] public section

namespace Turkish.Coordination

/-- *ve* 'and'. -/
def ve : Coordinator :=
  { form := "ve", gloss := "and", role := .conjunctive, kind := .free }

/-- *de* 'and', enclitic in the second coordinand, also the additive 'also, too'. -/
def de : Coordinator :=
  { form := "de", gloss := "and; also", role := .conjunctive, kind := .bound .after .clitic,
    alsoAdditive := true }

/-- The coordinators. -/
def allEntries : List Coordinator := [ve, de]

end Turkish.Coordination
