import Mathlib.Order.Nat

/-!
# Logophoric roles

[sells-1987] replaces a single notion of logophoricity with three discourse roles: the source,
who makes the report; the self, whose mind is reported; and the pivot, from whose point of view
the report is made. His discourse environments predicate the roles of a sentence-internal
referent cumulatively: a third-person point of view makes only the pivot internal, a
psychological verb the self and the pivot, and a logophoric verb all three. So an internal source
is a self and a self is a pivot, and the roles form a chain `pivot ≤ self ≤ source`.

A logophoric form is licensed by an antecedent that reaches the role the form requires. Japanese
*zibun* needs a pivot and Icelandic *sig* a self ([sells-1987]); Ewe *yè* needs the bearer of an
attitude, a self ([pearson-2015]), where [sells-1987] suggests source-orientation for logophoric
pronouns. [pancheva-zubizarreta-2018] map their prominence values onto the same roles.

## Main definitions

* `Reference.LogophoricRole` — the three roles, a bounded linear order
* `Reference.Logophoric` — a carrier whose every element requires a role of its antecedent
* `Reference.Logophoric.LicensedBy` — the antecedent's role reaches the required one

## References

* [P. Sells, *Aspects of Logophoricity* (1987)][sells-1987]
* [H. Pearson, *The interpretation of the logophoric pronoun in Ewe* (2015)][pearson-2015]
* [R. Pancheva and M. L. Zubizarreta, *The Person Case Constraint: The Syntactic Encoding of
  Perspective* (2018)][pancheva-zubizarreta-2018]
-/

namespace Reference

/-- The discourse roles of [sells-1987], ordered by entailment with the pivot least. -/
inductive LogophoricRole where
  /-- The one from whose point of view the report is made. -/
  | pivot
  /-- The one whose mind is reported. -/
  | self
  /-- The one who makes the report. -/
  | source
  deriving DecidableEq, Repr

namespace LogophoricRole

/-- The rank of a role in the entailment order. -/
def toNat : LogophoricRole → ℕ
  | .pivot => 0
  | .self => 1
  | .source => 2

theorem toNat_injective : Function.Injective toNat := by
  intro a b h; cases a <;> cases b <;> simp_all [toNat]

instance : LinearOrder LogophoricRole := LinearOrder.lift' toNat toNat_injective

instance : BoundedOrder LogophoricRole where
  bot := .pivot
  bot_le r := by cases r <;> decide
  top := .source
  le_top r := by cases r <;> decide

end LogophoricRole

/-- A carrier whose every element is logophoric: `requiredRole` is the least role an antecedent
must fill to license the form. The capability is neutral as to word class, so a logophoric
pronoun and verbal logophoric marking are sibling carriers. -/
class Logophoric (α : Type*) where
  /-- The least role an antecedent must fill to license the form. -/
  requiredRole : α → LogophoricRole

namespace Logophoric

variable {α : Type*} [Logophoric α] {a : α} {r r' : LogophoricRole}

/-- The form is licensed by an antecedent filling the role `r`: `r` reaches the role the form
requires. -/
def LicensedBy (a : α) (r : LogophoricRole) : Prop := requiredRole a ≤ r

instance : Decidable (LicensedBy a r) := inferInstanceAs (Decidable (_ ≤ _))

/-- Every logophoric form is licensed by a source. -/
theorem source_licenses (a : α) : LicensedBy a .source := le_top (a := requiredRole a)

/-- Licensing is monotone in the antecedent's role. -/
theorem LicensedBy.mono (h : LicensedBy a r) (hr : r ≤ r') : LicensedBy a r' := h.trans hr

end Logophoric

end Reference
