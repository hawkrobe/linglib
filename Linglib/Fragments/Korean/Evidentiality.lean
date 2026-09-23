module

public import Linglib.Semantics.Evidential.Defs

/-!
# Korean evidentiality

Korean has no grammatical evidentials: the retrospective mood is not a primarily evidential
form, and reported and inferential meanings are carried by sentence-final constructions, so
the inventory is empty. WALS codes the language as indirect-only. Lee's rival analysis of
the retrospective *-te* and of *-ney* as evidentials fixing the time of the speaker's sensory
evidence is in `Studies/Cumming2026.lean`.

## References

* [aikhenvald-2004], §7.2
* [de-haan-2013]
* [lee-2011]
* [cumming-2026]
-/

@[expose] public section

namespace Korean.Evidentiality

def evidentials : List Evidential := []

end Korean.Evidentiality
