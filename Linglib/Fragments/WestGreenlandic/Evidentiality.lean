module

public import Linglib.Semantics.Evidential.Defs

/-!
# West Greenlandic evidentiality

West Greenlandic has no evidentiality as a unitary grammatical category. [aikhenvald-2004]
describes its coding as scattered: evidential meanings are carried by verbal derivational
suffixes standing in opposition to derivational suffixes that have nothing to do with
information source, the sentential *-gunar-* 'it seems that', from sensory information or
logical inference, and *-sima-* 'apparently', inferred from report or from visible traces of
the event, beside non-sentential suffixes for what one can hear and for what something looks
or sounds like, together with the reported enclitic *-guuq* and an adverbial particle. As
with Japanese, at most the reported enclitic could be taken as an A3 system on its own, so the
inventory is empty. WALS codes the language as indirect-only
(`Data/WALS/Features/F77A.lean`).

## References

* [aikhenvald-2004]
* [de-haan-2013]
-/

@[expose] public section

namespace WestGreenlandic.Evidentiality

/-- West Greenlandic has no evidentials: its coding of information source is scattered. -/
def evidentials : List Evidential := []

end WestGreenlandic.Evidentiality
