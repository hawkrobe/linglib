import Linglib.Syntax.Voice.Alternation

/-!
# Mam voice

Mam (Mamean Mayan) derives from the agentive transitive construction a passive, whose agent
is implicit, and an antipassive, which demotes the object to an oblique and marks the subject
absolutive ([scott-2023]). Voice does not select a pivot for extraction; the extraction
morphology =(y)a' and the Minimalist Voice head that conditions it are
[elkins-torrence-brown-2026]'s and live in that study. San Juan Ostuncalco Mam
([elkins-torrence-brown-2026]) and San Juan Atitán Mam ([scott-2023]) are distinct varieties;
the inventory abstracts over the distinction.

## Main definitions

* `Mam.passive`, `Mam.antipassive`: the two coded alternations.

## References

* [elkins-torrence-brown-2026]
* [scott-2023]
-/

namespace Mam

/-- The passive: synthetically coded passivization, the agent implicit. -/
def passive : Voice.ValencyAlternation := { Voice.passivization with marking := .synthetic }

/-- The antipassive: synthetically coded antipassivization, the object an oblique. -/
def antipassive : Voice.ValencyAlternation :=
  { Voice.antipassivization with marking := .synthetic }

end Mam
