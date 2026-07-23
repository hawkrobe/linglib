import Linglib.Syntax.Category.Coordinator

/-!
# Finnish Coordination Morphemes
[haspelmath-2007] [mitrovic-sauerland-2016]

Finnish has:

- *ja* — J, free, prepositive: "A ja B"
- *-kin* — MU, bound, additive ('also'): "koira-kin kissa-kin" = 'both the
  dog and the cat' (bisyndetic postpositive)

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.finnish`).
-/

namespace Finnish.Coordination

/-- *ja* — J particle. Free, prepositive medial. -/
def ja : Coordinator :=
  { form := "ja", gloss := "and"
  , role := .j, kind := .free }

/-- *-kin* — MU particle, also additive. Bound, postpositive on each
    coordinand for the bisyndetic 'both…and' pattern. -/
def kin : Coordinator :=
  { form := "-kin", gloss := "also, too; and (MU)"
  , role := .mu, kind := .bound .after .clitic, alsoAdditive := true }

def allEntries : List Coordinator := [ja, kin]

end Finnish.Coordination
