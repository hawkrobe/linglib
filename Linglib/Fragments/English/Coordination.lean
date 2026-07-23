import Linglib.Syntax.Category.Coordinator

/-!
# English Coordination Morphemes
[haspelmath-2007] [mitrovic-sauerland-2016]

English has a sparse coordination inventory:

- *and* — J, free, prepositive: "A and B"
- *or* — disjunction, free, prepositive
- *but* — adversative, free, prepositive
- *both…and*, *either…or*, *neither…nor* — correlative bisyndetic uses

English is a canonical J-only language in the [mitrovic-sauerland-2016]
classification (no overt MU morpheme).

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.english`).
-/

namespace English.Coordination

/-- *and* — primary conjunction, J particle. Free, prepositive. -/
def and_ : Coordinator :=
  { form := "and", gloss := "and"
  , role := .j, kind := .free
  , correlative := true
  , note := "correlative use as 'both…and'" }

/-- *or* — disjunction. Free, prepositive; correlative as 'either…or'. -/
def or_ : Coordinator :=
  { form := "or", gloss := "or"
  , role := .disj, kind := .free
  , correlative := true }

/-- *but* — adversative. Free, prepositive. -/
def but_ : Coordinator :=
  { form := "but", gloss := "but"
  , role := .advers, kind := .free }

/-- *nor* — negative disjunction; correlative 'neither…nor'. -/
def nor_ : Coordinator :=
  { form := "nor", gloss := "nor"
  , role := .negDisj, kind := .free
  , correlative := true }

def allEntries : List Coordinator := [and_, or_, but_, nor_]

end English.Coordination
