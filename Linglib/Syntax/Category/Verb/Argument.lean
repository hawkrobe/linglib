import Linglib.Syntax.Category.Verb.Basic
import Linglib.Semantics.ArgumentStructure.ThetaRole

/-!
# Verb arguments

The argument slots of a verb entry, read off its citation frame
(`ArgumentFrame.Slot`), and the entailment profile the entry records for each
(`Verb.entailments`). Role labels are derived classifications of the
slots: `Verb.thetaLabel` gives the Dowty cluster label of a slot's
profile, and `Verb.codingRole` the comparative S/A/P/R/T classification
of the citation frame (`ArgumentFrame.codingRole`), a function of the frame's
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
def coreSlots : List ArgumentFrame.Slot := (v.citationFrame?.map ArgumentFrame.coreSlots).getD []

/-- The entailment profile the entry records for a slot of its citation
    frame: the subject profile on the external argument, the object
    profile on the object slot (`ArgumentFrame.objectSlot?`). -/
def entailments : ArgumentFrame.Slot → Option EntailmentProfile
  | .external => v.subjectEntailments
  | s@(.complement _) =>
    if v.citationFrame?.bind ArgumentFrame.objectSlot? = some s then v.objectEntailments else none

/-- The derived semantic-role label of a slot: the cluster label of its
    entailment profile (`EntailmentProfile.toRole`). -/
def thetaLabel (s : ArgumentFrame.Slot) : Option ThetaRole :=
  (v.entailments s).bind EntailmentProfile.toRole

/-- The comparative classification of a core slot of the citation frame
    ([comrie-1978]); `Clause.Arguments.codingRole` classifies a clause
    token (a passive clause of the same verb has an S). -/
def codingRole (s : ArgumentFrame.Slot) : Option ArgumentRole :=
  v.citationFrame?.bind (·.codingRole s)

end Verb
