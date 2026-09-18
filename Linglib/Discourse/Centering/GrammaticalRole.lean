import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype

/-!
# Ranking centers by grammatical role

The ranking of forward-looking centers that centering theory assumes for English, on which the
subject outranks the object, which outranks every other role. Kameyama argued for grammatical role over
Sidner's focus-based ranking, Grosz, Joshi, and Weinstein adopt it in their examples, and Gordon,
Grosz, and Gilliom's repeated-name penalty experiments support it.

## Main declarations

* `Discourse.Centering.GrammaticalRole`: subject, object, and other, linearly ordered in that
  order of prominence.

## References

* [kameyama-1986]
* [grosz-joshi-weinstein-1995]
* [gordon-grosz-gilliom-1993]
-/

namespace Discourse.Centering

/-- A grammatical role ranking the forward-looking centers, the subject over the object over the
rest. -/
inductive GrammaticalRole where
  | subject
  | object
  | other
  deriving DecidableEq, Repr, Fintype

namespace GrammaticalRole

/-- The prominence of a role, the subject the most prominent. -/
def rank : GrammaticalRole → ℕ
  | .subject => 2
  | .object => 1
  | .other => 0

instance : LinearOrder GrammaticalRole := LinearOrder.lift' rank (by decide)

theorem object_lt_subject : object < subject := by decide

theorem other_lt_object : other < object := by decide

end GrammaticalRole

end Discourse.Centering
