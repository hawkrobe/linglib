import Linglib.Core.Relativization.Basic
import Linglib.Typology.Relativization.Defs

/-!
# Malagasy Relativization Fragment
@cite{keenan-comrie-1977}

One relative clause marker:
- Gap construction (-case, postnominal, covers SU only)

Malagasy is a predicate-initial Austronesian language where only the
pivot (subject/topic) can be directly relativized. Non-subjects require
voice alternation to promote the target to pivot position before
relativization.

Data from @cite{keenan-comrie-1977} Table 1.
-/

namespace Fragments.Malagasy

open Core

/-- Gap construction. Postnominal RC. Only the pivot (subject) can be
    relativized. Voice alternation required for underlying non-subjects.
    E.g., "ny lehilahy [izay nandao _]" 'the man [that left _]'. -/
def relGap : RelClauseMarker :=
  { form := "izay/∅"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.subject]
  , notes := "Only pivot (subject) relativizable; voice alternation for non-SU" }

/-- All Malagasy relative clause markers. -/
def relMarkers : List RelClauseMarker := [relGap]

/-- Malagasy relativization profile (typological summary). -/
def relativization : Typology.Relativization.RelativizationProfile :=
  { subjStrategy := .gap
  , oblStrategy := .notRelativizable
  , rcPosition := .postNominal
  , lowestRelativizable := .subject
  , notes := "Gap on subject only; voice alternation needed for "
          ++ "non-subject relativization; Austronesian pattern" }

end Fragments.Malagasy
