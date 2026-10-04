module

public import Linglib.Syntax.Agreement.Paradigm
public import Linglib.Syntax.Negation

/-!
# Finnish negation

Finnish negates a clause with the negative auxiliary *e-*, cited in the third person singular
as *ei*. The auxiliary takes the person and number endings of the finite verb, and the lexical
verb stands in the connegative, a form without them: *nuku-n* 'I am sleeping', *e-n nuku* 'I am
not sleeping'. In the past the lexical verb is a participle, *en laulanut* 'I did not sing'.
The examples are those of [miestamo-2005].

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation Morphology

namespace Finnish.Negation

/-- The negative auxiliary *e-*. -/
def e : Marker := { pieces := [[.root "e"]] }

/-- The negative auxiliary takes the person and number endings of the present, giving *en*, *et*,
*ei*, *emme*, *ette* and *eivät*. -/
def ending : Agreement.Paradigm Morph :=
  [(.personNumber .first .singular, .suff "n"), (.personNumber .second .singular, .suff "t"),
   (.personNumber .third .singular, .suff "i"), (.personNumber .first .plural, .suff "mme"),
   (.personNumber .second .plural, .suff "tte"), (.personNumber .third .plural, .suff "ivät")]

/-- First person singular presents with their negatives. -/
def present : List Pair :=
  [⟨e, [.root "nuku", .suff "n"], [.root "e", .suff "n", .root "nuku"]⟩,
   ⟨e, [.root "juokse", .suff "n"], [.root "e", .suff "n", .root "juokse"]⟩]

end Finnish.Negation
