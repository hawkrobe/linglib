import Linglib.Syntax.Voice.Basic

/-!
# Mam voice

Mam (Mamean Mayan) has the active, a passive whose agent is implicit, and an antipassive
which demotes the object to an oblique and marks the subject absolutive, both marked by
verbal morphology ([scott-2023]). Voice does not select a pivot for extraction; the extraction morphology
=(y)a' and the Minimalist Voice head that conditions it are [elkins-torrence-brown-2026]'s
and live in that study. San Juan Ostuncalco Mam ([elkins-torrence-brown-2026]) and San Juan
Atitán Mam ([scott-2023]) are distinct varieties; the inventory abstracts over the
distinction.

## References

* [elkins-torrence-brown-2026]
* [scott-2023]
-/

namespace Mam

/-- The active, the passive and the antipassive, the last two marked on the verb. -/
def voices : Finset Voice := {.active, Voice.passive.synthetic, Voice.antipassive.synthetic}

end Mam
