import Linglib.Features.Coordination

/-!
# Hindi-Urdu Coordination Morphemes
@cite{haspelmath-2007} @cite{mitrovic-sauerland-2016}

Hindi-Urdu has:

- *aur* — J, free, prepositive: "A aur B"
- *bhii* — MU, free, additive ('also'): "A bhii B bhii" = 'both A and B'

The bisyndetic *bhii…bhii* pattern is the canonical M&S μ-only construction
where the additive particle iterates on each coordinand.

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.hindiUrdu`).
-/

namespace Fragments.HindiUrdu.Coordination

open Features.Coordination

/-- *aur* — J particle. Free, prepositive medial. -/
def aur : CoordEntry :=
  { form := "aur", gloss := "and"
  , role := .j, boundness := .free }

/-- *bhii* — MU particle, also additive ('also/too').
    Free, used bisyndetically: "A bhii B bhii". -/
def bhii : CoordEntry :=
  { form := "bhii", gloss := "also, too; and (MU)"
  , role := .mu, boundness := .free, alsoAdditive := true
  , correlative := true }

def allEntries : List CoordEntry := [aur, bhii]

end Fragments.HindiUrdu.Coordination
