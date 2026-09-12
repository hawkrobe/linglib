import Linglib.Semantics.Degree.Noun

/-!
# Morzycki (2009): Degree Modification of Gradable Nouns

This file formalizes the account in [morzycki-2009] of the degree readings of size
adjectives, *big idiot* as a very idiotic person. Gradable nouns denote measure functions
from individuals to degrees, and a size adjective in a degree reading is the argument of an
adnominal degree morpheme, the nominal counterpart of the head that licenses measure
phrases in adjectival projections: the resulting predicate requires the individual's degree
to reach both the least degree meeting the size adjective's standard and the noun's own
standard. Two generalizations follow. Only size adjectives predicating bigness license
degree readings, since antonyms measure along oppositely ordered scales, so the least degree
small enough to count as small is the bottom of the noun's scale and the requirement is
vacuous (`small_vacuous`), whereas the bigness requirement is a genuine restriction
(`big_restrictive`, `big_strictly_stronger`); and degree readings arise only attributively,
in the specifier of the nominal degree projection, a restriction the syntax imposes.

## Implementation notes

The measure-function semantics and the size adjectives live in `Semantics/Degree/Noun`, on
a discrete degree scale; the adnominal degree morphemes *real*, *true*, *total*, *complete*,
and *absolute*, and the restriction of *complete* to nouns whose scales have a maximum, are
not represented.

## References

* [morzycki-2009]
-/

namespace Morzycki2009

open Degree

/-- Smallness is vacuous: *small idiot* is *idiot*, wherever the standard of smallness lies. -/
theorem small_vacuous {E : Type} (noun : GradableNoun E) (x : E) :
    smallIdiot noun x = noun.pos x :=
  small_idiot_vacuous noun x

/-- Bigness restricts: a *big idiot* is an idiot. -/
theorem big_restrictive {E : Type} (noun : GradableNoun E) (h : noun.standard < deg 5)
    (x : E) (hx : bigIdiot noun x = true) : noun.pos x = true :=
  big_idiot_restrictive noun h x hx

/-- The restriction is proper: an idiot who is not a big idiot. -/
theorem big_strictly_stronger :
    exampleIdiot.pos .sarah = true ∧ bigIdiot exampleIdiot .sarah = false := by
  decide

end Morzycki2009
