import Linglib.Syntax.RelativeClause.Basic
import Linglib.Data.WALS.Features.F122A
import Linglib.Data.WALS.Features.F123A

/-!
# Relative clauses: typological survey (WALS)
[comrie-kuteva-2013a] [comrie-kuteva-2013b] [keenan-comrie-1977]

Aggregate distribution theorems over the WALS relativization chapters.
Ch 122 (subjects): 166 languages; gap dominates, reflecting subjects'
high accessibility on the [keenan-comrie-1977] hierarchy. Ch 123
(obliques): 112 languages; gap remains most common, but pronoun
retention is far more frequent than for subjects, and a sizeable
minority cannot relativize obliques at all. Per-language WALS values are
queried directly from the `Data/WALS` rows; per-language marker
inventories live in `Fragments/{Lang}/Relativization.lean`.
-/

set_option autoImplicit false

namespace RelativeClause

private abbrev ch122 := Data.WALS.F122A.allData
private abbrev ch123 := Data.WALS.F123A.allData

set_option maxRecDepth 2000 in
/-- WALS Ch 122: gap is the most common subject relativization strategy,
    followed by non-reduction, relative pronoun, and pronoun retention. -/
theorem gap_most_common_for_subjects :
    (ch122.filter (·.value == .gap)).length >
    (ch122.filter (·.value == .nonReduction)).length ∧
    (ch122.filter (·.value == .nonReduction)).length >
    (ch122.filter (·.value == .relativePronoun)).length ∧
    (ch122.filter (·.value == .relativePronoun)).length >
    (ch122.filter (·.value == .pronounRetention)).length := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 2000 in
/-- WALS Chs 122/123: pronoun retention is more common for obliques than
    for subjects — a key Accessibility-Hierarchy prediction
    ([keenan-comrie-1977]). -/
theorem retention_increases_for_obliques :
    (ch123.filter (·.value == .pronounRetention)).length >
    (ch122.filter (·.value == .pronounRetention)).length := by decide

set_option maxRecDepth 2000 in
/-- WALS Ch 123: some languages cannot relativize obliques at all,
    contrasting with subjects, where the Ch 122 enum has no "not
    possible" value. -/
theorem obliques_sometimes_not_relativizable :
    (ch123.filter (·.value == .notPossible)).length > 0 := by decide

end RelativeClause
