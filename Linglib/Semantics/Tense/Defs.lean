import Mathlib.Order.Basic
import Linglib.Core.Order.Relation

/-!
# Grammatical tense as a comparison category

A grammatical tense is a **comparison category** between a reference time and a perspective time —
a `Finset Ordering` (`Core.Order`). There is no bespoke tense type: the four traditional labels name
four of the comparison cells `Core.Order` already provides, so tense, evidentials, and modal-base
time all share one Ordering-grounded spine.

* `past`    = `before`      (ref < perspective)
* `present` = `overlapping` (ref = perspective)
* `future`  = `after`       (ref > perspective)
* `nonpast` = `notBefore`   (ref ≥ perspective — the present-or-future union, [klecha-2016])

The constraint a tense imposes is `Core.Order.holds`, grounded in `Ordering` over the order on `T`.
The frame predicates (`ReichenbachFrame.isPast`/`isFuture`/`isNonpast`) and the compositional tense
operators are views of `holds` (with `Core.Order.holds_before` etc. reducing them to `<`/`=`/`≥`).

[klecha-2016] (the `nonpast` case) [kiparsky-2002]
-/

namespace Tense

open Core.Order (before after overlapping notBefore)

/-- **Past**: reference time before perspective time. -/
abbrev past : Finset Ordering := before

/-- **Present**: reference time overlaps (equals) perspective time. -/
abbrev present : Finset Ordering := overlapping

/-- **Future**: reference time after perspective time. -/
abbrev future : Finset Ordering := after

/-- **Nonpast** ([klecha-2016]): reference time at or after perspective time — the present-or-future
    union (`Core.Order.notBefore`), *not* a fourth atomic tense. Lets embedded tense under
    circumstantial modals have future-oriented readings (⟦NPST⟧ requires ref ≥ perspective). -/
abbrev nonpast : Finset Ordering := notBefore

end Tense
