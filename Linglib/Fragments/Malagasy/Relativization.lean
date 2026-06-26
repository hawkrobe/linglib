import Linglib.Syntax.RelativeClause.Basic
import Linglib.Syntax.RelativeClause.WALS

/-!
# Malagasy Relativization Fragment
[keenan-comrie-1977]

One relative clause marker:
- Gap construction (-case, postnominal, covers SU only)

Malagasy is a predicate-initial Austronesian language where only the
pivot (subject/topic) can be directly relativized. Non-subjects require
voice alternation to promote the target to pivot position before
relativization.

Data from [keenan-comrie-1977] Table 1.
-/

namespace Malagasy

open RelativeClause

/-- Gap construction. Postnominal RC. Only the pivot (subject) can be
    relativized. Voice alternation required for underlying non-subjects.
    E.g., "ny lehilahy [izay nandao _]" 'the man [that left _]'. -/
def relGap : Marker :=
  { form := "izay/∅"
  , npRel := .gap
  , bearsCaseMarking := false
  , rcPosition := .postNominal
  , positions := [.subject]
  , notes := "Only pivot (subject) relativizable; voice alternation for non-SU" }

/-- All Malagasy relative clause markers. -/
def relMarkers : List Marker := [relGap]

/-! Malagasy relativization profile (typological summary): gap on subject
    only; voice alternation needed for non-subject relativization;
    Austronesian pattern. -/
namespace Relativization
def subjStrategy : SubjStrategy := .gap
def oblStrategy : OblStrategy := .notRelativizable
def rcPosition : RCPosition := .postNominal
def lowestRelativizable : AHPosition := .subject
end Relativization

end Malagasy
