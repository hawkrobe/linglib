import Linglib.Semantics.Coordination.Defs

/-!
# Hindi-Urdu Coordination Morphemes
[haspelmath-2007] [mitrovic-sauerland-2016]

Hindi-Urdu has:

- *aur* — J, free, prepositive: "A aur B"
- *bhii* — MU, free, additive ('also'): "A bhii B bhii" = 'both A and B'

The bisyndetic *bhii…bhii* pattern is the canonical M&S μ-only construction
where the additive particle iterates on each coordinand.

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.hindiUrdu`).
-/

namespace HindiUrdu.Coordination

/-- *aur* — J particle. Free, prepositive medial. -/
def aur : Coordinator :=
  { form := "aur", gloss := "and"
  , role := .j, kind := .free }

/-- *bhii* — MU particle, also additive ('also/too').
    Free, used bisyndetically: "A bhii B bhii". -/
def bhii : Coordinator :=
  { form := "bhii", gloss := "also, too; and (MU)"
  , role := .mu, kind := .free, alsoAdditive := true
  , correlative := true }

def allEntries : List Coordinator := [aur, bhii]

end HindiUrdu.Coordination
