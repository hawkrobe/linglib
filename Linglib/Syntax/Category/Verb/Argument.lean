module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Semantics.ArgumentStructure.ThetaRole
public import Linglib.Semantics.ArgumentStructure.Linking

/-!
# Verb arguments

The argument slots of a verb entry, read off its basic frame
(`ArgumentFrame.Slot`), and the entailment profile the entry records for each
(`Verb.entailments`). Role labels are derived classifications of the
slots: `Verb.thetaLabel` gives the Dowty cluster label of a slot's
profile, and `Verb.codingRole` the comparative S/A/P/R/T classification
of the basic frame (`ArgumentFrame.codingRole`), a function of the frame's
shape (A is *defined* as the more agent-like core argument of a two-place
frame), never a stored feature. `Verb.linkedFrame?` assembles the basic frame
and the derived labels into the verb's argument structure.

## References

* [comrie-1978]
* [dowty-1991]
* [haspelmath-2021]
-/

@[expose] public section

open ArgumentStructure

namespace Verb

variable (v : Verb)

/-- The core argument slots of the basic frame. -/
def coreSlots : List ArgumentFrame.Slot :=
  (v.valency.frames.head?.map ArgumentFrame.coreSlots).getD []

/-- The entailment profile of a slot of the basic frame is the subject profile on the external
    argument and the object profile on the object slot (`ArgumentFrame.objectSlot?`). -/
def entailments : ArgumentFrame.Slot → Option EntailmentProfile
  | .external => v.subjectProfile?
  | s@(.complement _) =>
    if v.valency.frames.head?.bind ArgumentFrame.objectSlot? = some s then v.objectProfile?
    else none

/-- `thetaLabel s` is the derived semantic-role label of the slot `s`, the cluster label of its
    entailment profile (`EntailmentProfile.toRole`). -/
def thetaLabel (s : ArgumentFrame.Slot) : Option ThetaRole :=
  (v.entailments s).bind EntailmentProfile.toRole

/-- The comparative classification of a core slot of the basic frame
    ([comrie-1978]); `Clause.Arguments.codingRole` classifies a clause
    token (a passive clause of the same verb has an S). -/
def codingRole (s : ArgumentFrame.Slot) : Option ArgumentRole :=
  v.valency.frames.head?.bind (·.codingRole s)

/-- The lexical argument structure of a verb entry is its basic frame, each slot linked to the
label read off its entailment profile and required when the frame expresses it. -/
def linkedFrame? : Option LinkedFrame :=
  v.valency.frames.head?.map fun fr ↦
    { frame := fr
      roles := fr.slots.map fun s ↦
        (s, { admits := (v.thetaLabel s).toList.toFinset
              obligatory := (fr.get? s).any fun p ↦ decide p.IsExpressed }) }

end Verb
