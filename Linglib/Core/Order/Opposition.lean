import Linglib.Core.Order.Relation
import Linglib.Core.Logic.Aristotelian.Basic

/-!
# Comparison categories as an Aristotelian diagram

The eight comparison categories (`Core.Order.Relation`) are the elements of the Boolean algebra
`𝒫 {lt, eq, gt}`; their logical oppositions are exactly the four Aristotelian relations
[demey-smessaert-2018] (`Core.Logic.Aristotelian`). This file is where the two finite-Boolean-algebra
developments meet: the comparison/point algebra (with `holds` its relation-algebra homomorphism) and
the theory of opposition (over any `[BooleanAlgebra α]`).

Because `Finset Ordering` *is* a `BooleanAlgebra`, the Aristotelian relations apply to the named
categories with no bridge construction — the classic square of opposition for `<`/`=`/`>` is a
`decide`-check over the eight-element carrier. Via `Tense.past = before` etc.
(`Semantics/Tense/Defs.lean`) these specialise to grammatical tense: past and nonpast are
contradictories, past and future contraries, `≤` and `≥` subcontraries.
-/

namespace Core.Order

open Aristotelian

/-! ### The square of opposition for `<`/`=`/`>` -/

/-- `<` and `≥` are **contradictories**: `before` and `notBefore` are complementary cells of
    `𝒫 {lt, eq, gt}` — exactly one holds of any pair. -/
theorem isContradictory_before_notBefore : IsContradictory before notBefore := by decide

/-- `>` and `≤` are **contradictories**. -/
theorem isContradictory_after_notAfter : IsContradictory after notAfter := by decide

/-- `<` and `>` are **contraries**: disjoint (never both) but not jointly exhaustive — both fail
    at `=`. -/
theorem isContrary_before_after : IsContrary before after := by decide

/-- `≤` and `≥` are **subcontraries**: jointly exhaustive (one always holds) but not disjoint —
    both hold at `=`. -/
theorem isSubcontrary_notAfter_notBefore : IsSubcontrary notAfter notBefore := by decide

/-- `<` is **subaltern** to `≤`: strict precedence implies weak precedence. -/
theorem isSubaltern_before_notAfter : IsSubaltern before notAfter := by decide

/-- `>` is **subaltern** to `≥`. -/
theorem isSubaltern_after_notBefore : IsSubaltern after notBefore := by decide

/-- The two-axis classifier agrees: `<` opposes `≥` as a contradictory. -/
theorem opposition_before_notBefore : opposition before notBefore = .contradictory := by decide

/-- `=` and `≠` are **contradictories**: `overlapping` and `distinct` partition the carrier. -/
theorem isContradictory_overlapping_distinct : IsContradictory overlapping distinct := by decide

end Core.Order
