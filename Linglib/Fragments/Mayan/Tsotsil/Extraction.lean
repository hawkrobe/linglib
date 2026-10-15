module

public import Linglib.Syntax.Reflex
public import Linglib.Syntax.Voice.Basic
public import Linglib.Fragments.Mayan.Extraction

/-!
# Tsotsil extraction marking

Tsotsil (Tseltalan Mayan) may put the verb in the Agent Focus form in *-on* when a transitive
subject is extracted. Aissen shows the form to be optional and governed by obviation, the form
of a clause whose object outranks its subject; no other extraction is marked.

## Main declarations

* `Tsotsil.agentFocus`: the Agent Focus voice.
* `Tsotsil.Extraction.realize`: the optional Agent Focus reflex of subject extraction.

## References

* [aissen-1999a]
-/

@[expose] public section

namespace Tsotsil

/-- Agent Focus keeps both core terms, as the active does, and is coded by *-on*. -/
def agentFocus : Voice := Voice.agentVoice.marked [.suff "on"]

/-- The extraction of a transitive subject may switch the verb to Agent Focus, used when the
object outranks the subject in obviation; no other extraction is marked. -/
def Extraction.realize : ArgumentRole → Finset (Reflex Mayan.Host)
  | .A => {.morpheme .verb agentFocus.marker}
  | _ => ∅

end Tsotsil
