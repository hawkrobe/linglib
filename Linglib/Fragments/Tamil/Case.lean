module

public import Linglib.Syntax.Case.Basic

/-!
# Tamil Case Inventory
[blake-1994]

Tamil (Dravidian) has **8 cases** with agglutinative suffixes:
NOM (∅), ACC (-ai), DAT (-ukku), GEN (-in / -uṭaiya), LOC (-il),
ABL (-ilirundu), INST / COM (-āl / -ōṭu), VOC (-ē).

The instrumental and comitative are sometimes syncretic (-ōṭu covers
both functions), a pattern documented cross-linguistically ([blake-1994];
WALS Ch. 52).

-/

@[expose] public section

namespace Tamil.Case

/-- Tamil 7-case core inventory (excluding VOC). -/
def inventory : Finset Case :=
  {.nom, .acc, .gen, .dat, .loc, .abl, .inst, .com}

end Tamil.Case
