import Linglib.Syntax.Category.Verb.Basic
import Linglib.Semantics.ArgumentStructure.Linking

/-!
# Verb arguments

The argument slots of a verb entry, read off its citation frame
(`Frame.Slot`), and the entailment profile the entry records for each
(`Verb.entailments`). Role labels are derived classifications of the
slots: `Verb.thetaLabel` gives the Dowty cluster label of a slot's
profile, and `Verb.codingRole` the comparative S/A/P/R/T classification
of the citation frame (`Frame.codingRole`), a function of the frame's
shape (A is *defined* as the more agent-like core argument of a two-place
frame), never a stored feature.

## References

* [comrie-1978]
* [dowty-1991]
* [haspelmath-2021]
-/

open ArgumentStructure

namespace Verb

variable (v : Verb)

/-- The core argument slots of the citation frame. -/
def coreSlots : List Frame.Slot := (v.citationFrame?.map Frame.coreSlots).getD []

/-- The entailment profile the entry records for a slot of its citation
    frame: the subject profile on the external argument, the object
    profile on the object slot (`Frame.objectSlot?`). -/
def entailments : Frame.Slot → Option EntailmentProfile
  | .external => v.subjectProfile?
  | s@(.complement _) =>
    if v.citationFrame?.bind Frame.objectSlot? = some s then v.objectProfile? else none

/-- The derived semantic-role label of a slot: the cluster label of its
    entailment profile (`EntailmentProfile.toRole`). -/
def thetaLabel (s : Frame.Slot) : Option ThetaRole :=
  (v.entailments s).bind EntailmentProfile.toRole

/-- The comparative classification of a core slot of the citation frame
    ([comrie-1978]); `Clause.Arguments.codingRole` classifies a clause
    token (a passive clause of the same verb has an S). -/
def codingRole (s : Frame.Slot) : Option ArgumentRole :=
  v.citationFrame?.bind (·.codingRole s)

end Verb
