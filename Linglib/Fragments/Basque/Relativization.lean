import Linglib.Syntax.RelativeClause.Basic

/-!
# Basque Relativization Fragment
[keenan-comrie-1977]

One relative clause marker: the invariable suffix *-n* at the juncture
of a prenominal RC, with gap in NP_rel (-case, covers SU/DO/IO). Basque
is the paper's witness that IO is a possible primary cut-off point —
it "does appear to discriminate indirect objects from both its
immediate neighbors on the AH" (§1.3.3 p. 72). Table 1 leaves
OBL, GEN, and OCOMP blank (no data).
-/

namespace Basque

open RelativeClause

/-- Invariable relativizer *-n* marking the juncture of a prenominal RC;
    NP_rel (cross-referenced by a verbal affix) is deleted. Covers SU,
    DO, IO ([keenan-comrie-1977] §1.3.3 p. 72, ex. (17); Table 1 p. 76).
    E.g., "emakumeari liburua eman dio-n gizona" 'the man who has given
    the book to the woman'. -/
def relN : Marker :=
  { form := "-n"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .preNominal
  , positions := [.subject, .directObject, .indirectObject]
  , notes := "Invariable juncture suffix -n; NP_rel deleted; OBL-OCOMP no data" }

/-- All Basque relative clause markers. -/
def relMarkers : List Marker := [relN]

end Basque
