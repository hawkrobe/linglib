import Linglib.Syntax.Adposition.Order

/-!
# K'iche' adposition order [mondloch-2017] [clemens-coon-2018]

K'iche' is not coded in WALS Ch 85 (ISO `quc` is absent), so the
classification is grammar-grounded from [mondloch-2017] rather
than via `AdpositionOrder.ofWALS`. Mondloch documents prepositional
constructions in K'iche' (preposition + NP order, consistent with the
language's verb-initial/head-initial profile per Greenberg's U3).

## A contested classification

Mayanist literature debates whether K'iche' truly has *adpositions* or
only **relational nouns** that fill an adposition-like role
syntactically (Aissen 1992, Coon 2010). Under the
relational-noun analysis, K'iche' would arguably be coded as
`.noAdpositions` rather than `.prepositional`. [clemens-coon-2018]
surveys derivational accounts of Mayan verb-initiality and the
related head-direction debates.

The Fragment commits to `.prepositional` because Mondloch describes
preposition-like constructions; the relational-noun reading would
give `.noAdpositions`. Either choice is consistent with the broader
head-initial profile (`.headInitial` either way under
`AdpositionOrder.headDirection`).
-/

namespace Kiche

/-- K'iche' adposition order, grammar-grounded from
    [mondloch-2017] (prepositional constructions). Not in WALS
    Ch 85 — direct override rather than `AdpositionOrder.ofWALS "quc"`
    (which would return `.notInWALS`). The `.prepositional` choice is
    contested across Mayanist literature; see module docstring. -/
def adposition : Adposition.AdpositionOrder := .prepositional

end Kiche
