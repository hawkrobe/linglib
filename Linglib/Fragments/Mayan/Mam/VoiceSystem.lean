import Linglib.Syntax.Voice.Alternation

/-!
# Mam voice

Mam (Mamean Mayan) has an agentive voice, the basic transitive construction with an overt
agent, a passive, whose agent is implicit, and an antipassive, which demotes the object to an
oblique and marks the subject absolutive ([scott-2023]). Voice does not select a pivot for
extraction; the extraction morphology =(y)a' and the Minimalist Voice head that conditions it
are [elkins-torrence-brown-2026]'s and live in that study. San Juan Ostuncalco Mam
([elkins-torrence-brown-2026]) and San Juan Atitán Mam ([scott-2023]) are distinct varieties;
the inventory abstracts over the distinction.

## Main definitions

* `Mam.Voice`, `Voice.alternation`: the three voices and what each does to the transitive
  construction.

## References

* [elkins-torrence-brown-2026]
* [scott-2023]
-/

open Voice

namespace Mam

/-- The three voices. -/
inductive Voice where
  | agentive
  | passive
  | antipassive
  deriving DecidableEq, Repr

/-- What each voice does to the transitive construction: the agentive nothing, the passive
passivization, the antipassive antipassivization, both synthetically coded. -/
def Voice.alternation : Voice → ValencyAlternation
  | .agentive => .refl .np
  | .passive => { passivization with marking := .synthetic }
  | .antipassive => { antipassivization with marking := .synthetic }

end Mam
