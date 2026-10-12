module

public import Linglib.Fragments.English.PolarityItems
public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Data.Examples.Szabolcsi2004

/-!
# Szabolcsi (2004): Positive Polarity – Negative Polarity

Szabolcsi observes that *someone* cannot take scope immediately below clausemate negation, a
negative quantifier or *without*, but can below *at most five*, and that what sets the first three
apart is that they are anti-additive while *at most five* is merely decreasing. With *someone*'s
Fragment entry, which is blocked by anti-additive operators, the licensing theory blocks exactly
the starred narrow-scope readings of her paradigm (`readings_predicted`), and over the paradigm's
operators being blocked is being anti-additive (`antiLicenses_someone_iff`).

## References

* [szabolcsi-2004]
-/

@[expose] public section

namespace Szabolcsi2004

open PolarityItem English.PolarityItems

/-- The operators of the paradigm, clausemate negation, *no one*, *without* and *at most five*. -/
inductive Operator where
  | not
  | noOne
  | without
  | atMostFive
  deriving DecidableEq, Repr

/-- The licensing context an operator is. -/
def Operator.toLicensingContext : Operator → LicensingContext
  | .not => .negation
  | .noOne => .nobody
  | .without => .withoutClause
  | .atMostFive => .atMost

instance (op : Operator) : DecidablePred op.toLicensingContext.AntiLicenses := by
  cases op <;> dsimp only [Operator.toLicensingContext] <;> infer_instance

/-- *Someone* is blocked immediately below an operator of the paradigm exactly when the operator
is anti-additive. -/
theorem antiLicenses_someone_iff (op : Operator) :
    op.toLicensingContext.AntiLicenses someone ↔ op.toLicensingContext.licenser.Holds .antiAdd := by
  cases op
  · exact iff_of_true (by decide) (LicensingContext.holds_negation .antiAdditive)
  · exact iff_of_true (by decide)
      (LicensingContext.holds_nobody_iff (s := .antiAdditive) |>.2 le_rfl)
  · exact iff_of_true (by decide)
      (LicensingContext.holds_withoutClause_iff (s := .antiAdditive) |>.2 le_rfl)
  · exact iff_of_false (by decide)
      fun h ↦ absurd (LicensingContext.holds_atMost_iff (s := .antiAdditive) |>.1 h) (by decide)

/-- The operator a row names. -/
def Operator.ofKey : String → Option Operator
  | "not" => some .not
  | "no one" => some .noOne
  | "without" => some .without
  | "at most five" => some .atMostFive
  | _ => none

/-- Every row is on *someone*, names its operator, and its reading with *someone* in the
operator's immediate scope is acceptable exactly when the operator does not block *someone*. -/
theorem readings_predicted :
    ∀ d ∈ Examples.all, d.feature? "item" = some "someone" ∧
      ∃ op ∈ (d.feature? "operator").bind Operator.ofKey, ∃ r ∈ d.readings.head?,
        (r.2 = .acceptable ↔ ¬ op.toLicensingContext.AntiLicenses someone) := by
  decide +kernel

end Szabolcsi2004
