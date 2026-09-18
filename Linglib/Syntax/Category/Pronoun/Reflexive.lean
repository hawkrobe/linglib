import Linglib.Semantics.Reference.Logophoricity
import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Reflexive pronouns

A reflexive pronoun is a pronoun whose kind fixes its binding class: it is an anaphor, bound in
its local domain. A long-distance reflexive such as Japanese *zibun* is also licensed outside
that domain, by an antecedent filling a perspectival role; `ReflexivePronoun.requiredRole`
records the least such role; it is `none` for a local reflexive such as English *himself*, and
where no role is recorded.

## Main declarations

* `ReflexivePronoun` — a pronoun with the role that licenses it at a distance, if any
* `ReflexivePronoun.LicensedBy` — licensing at a distance by an antecedent's role
* `ReflexivePronoun.bindingClassOf_toWord` — the word of a reflexive classifies as a reflexive

## References

* [N. Chomsky, *Lectures on Government and Binding* (1981)][chomsky-1981]
* [P. Sells, *Aspects of Logophoricity* (1987)][sells-1987]
-/

open Reference (LogophoricRole)

/-- A reflexive pronoun: the general `Pronoun` with the least perspectival role an antecedent
outside the local domain must fill, `none` when the form is only locally bound or no role is
recorded. -/
structure ReflexivePronoun extends Pronoun where
  /-- The least [sells-1987] role that licenses the form at a distance. -/
  requiredRole : Option LogophoricRole := none
  deriving DecidableEq, Repr

namespace ReflexivePronoun

variable (p : ReflexivePronoun)

instance : HasPhi ReflexivePronoun := ⟨fun p ↦ p.toPronoun.phi⟩

/-- The form is licensed at a distance by an antecedent filling the role `r`: it has a required
role and `r` reaches it. -/
def LicensedBy (r : LogophoricRole) : Prop := ∃ q ∈ p.requiredRole, q ≤ r

instance (r : LogophoricRole) : Decidable (p.LicensedBy r) :=
  inferInstanceAs (Decidable (∃ q ∈ p.requiredRole, q ≤ r))

/-- A reflexive with no required role is licensed at a distance by no antecedent. -/
theorem not_licensedBy_of_eq_none (h : p.requiredRole = none) (r : LogophoricRole) :
    ¬ p.LicensedBy r := by
  simp [LicensedBy, h]

variable {p} in
/-- Licensing is monotone in the antecedent's role. -/
theorem LicensedBy.mono {r r' : LogophoricRole} (h : p.LicensedBy r) (hr : r ≤ r') :
    p.LicensedBy r' :=
  let ⟨q, hq, hqr⟩ := h
  ⟨q, hq, hqr.trans hr⟩

/-- A reflexive's word is of UD pronoun type `Prs` and marked reflexive. -/
def toWord : Morphology.Word := p.toPronoun.toWord (some .Prs) true

/-- A reflexive pronoun is a reflexive anaphor. -/
@[simp]
theorem bindingClassOf_toWord : Binding.bindingClassOf p.toWord = some .reflexive :=
  Pronoun.bindingClassOf_toWord_reflex _ _

end ReflexivePronoun
