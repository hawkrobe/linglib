import Linglib.Features.Coordination

/-!
# Korean Coordination Morphemes
@cite{mitrovic-2021}

Korean has multiple postpositive bound coordinators with register/style
differences. The @cite{mitrovic-sauerland-2016} J-μ classification used
in `Studies/MitrovicSauerland2016.lean` treats *-(i)rang* as J and *-to*
as μ; the latter doubles as the additive ("also") particle.

- *-(i)rang* — J, bound, postpositive (informal): "A-(i)rang B"
- *-to* — MU, bound, additive: "A-to B-to" = 'A also, B also' = 'both A and B'
- *-(k)wa* and *-hako* are register variants of J (not formalised here).

Consumed by `Studies/Haspelmath2007.lean` (`Haspelmath2007.korean`).
-/

namespace Fragments.Korean.Coordination

open Features.Coordination

/-- *-(i)rang* — J particle, informal register. Bound, postpositive. -/
def irang : CoordEntry :=
  { form := "-(i)rang", gloss := "and"
  , role := .j, boundness := .bound
  , note := "informal register; -kwa/-hako are more formal alternatives" }

/-- *-to* — MU particle, additive. Bound, postpositive on each conjunct.
    Doubles as the additive focus particle ("also/too"). -/
def to_ : CoordEntry :=
  { form := "-to", gloss := "also, too; and (MU)"
  , role := .mu, boundness := .bound, alsoAdditive := true }

def allEntries : List CoordEntry := [irang, to_]

end Fragments.Korean.Coordination
