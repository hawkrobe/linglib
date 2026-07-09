import Linglib.Syntax.Category.Adposition.Order

/-!
# K'iche' Adposition Order

Grammar-grounded adposition-order classification for K'iche' (K'ichean
Mayan) from [mondloch-2017], who documents prepositional constructions
(preposition + NP order, consistent with the language's
verb-initial/head-initial profile per Greenberg's U3). K'iche' is not
coded in WALS Ch 85 (ISO `quc` is absent), so the value is a direct
override rather than via `AdpositionOrder.ofWALS`.

## Implementation notes

Mayanist literature debates whether K'iche' truly has *adpositions* or
only **relational nouns** filling an adposition-like role syntactically
(Aissen 1992, Coon 2010). Under the relational-noun analysis K'iche'
would arguably be coded `.noAdpositions` rather than `.prepositional`.
[clemens-coon-2018] surveys derivational accounts of Mayan
verb-initiality and the related head-direction debates. The Fragment
commits to `.prepositional` because Mondloch describes preposition-like
constructions; either choice is head-initial under
`AdpositionOrder.headDirection`.
-/

namespace Kiche

/-- K'iche' adposition order, grammar-grounded as `.prepositional` from
    [mondloch-2017]; not in WALS Ch 85, so a direct override. -/
def adposition : Adposition.AdpositionOrder := .prepositional

end Kiche
