import Linglib.Morphology.Paradigm.Basic
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
* `ReflexivePronoun.paradigm` — the forms an inventory offers for each category its person and
  number realize
* `ReflexivePronoun.bindingClassOf_toWord` — the word of a reflexive classifies as a reflexive

## References

* [N. Chomsky, *Lectures on Government and Binding* (1981)][chomsky-1981]
* [P. Sells, *Aspects of Logophoricity* (1987)][sells-1987]
-/

/-- A reflexive pronoun: the general `Pronoun` with the least perspectival role an antecedent
outside the local domain must fill, `none` when the form is only locally bound or no role is
recorded. -/
structure ReflexivePronoun extends Pronoun where
  /-- The least [sells-1987] role that licenses the form at a distance. -/
  requiredRole : Option Reference.LogophoricRole := none
  deriving DecidableEq, Repr

namespace ReflexivePronoun

variable (p : ReflexivePronoun)

instance : HasPhi ReflexivePronoun := ⟨fun p ↦ p.toPronoun.phi⟩

/-- The form is licensed at a distance by an antecedent filling the role `r`: it has a required
role and `r` reaches it. -/
def LicensedBy (r : Reference.LogophoricRole) : Prop := ∃ q ∈ p.requiredRole, q ≤ r

instance (r : Reference.LogophoricRole) : Decidable (p.LicensedBy r) :=
  inferInstanceAs (Decidable (∃ q ∈ p.requiredRole, q ≤ r))

/-- A reflexive with no required role is licensed at a distance by no antecedent. -/
theorem not_licensedBy_of_eq_none (h : p.requiredRole = none) (r : Reference.LogophoricRole) :
    ¬ p.LicensedBy r := by
  simp [LicensedBy, h]

variable {p} in
/-- Licensing is monotone in the antecedent's role. -/
theorem LicensedBy.mono {r r' : Reference.LogophoricRole} (h : p.LicensedBy r) (hr : r ≤ r') :
    p.LicensedBy r' :=
  let ⟨q, hq, hqr⟩ := h
  ⟨q, hq, hqr.trans hr⟩

/-- The paradigm of an inventory assigns each category the forms of the reflexives whose person
and number realize it. A reflexive denotes what its antecedent does, so its cells are those of
its agreement features. -/
def paradigm : Finset ReflexivePronoun → Person.Category → Finset String :=
  Morphology.formsAt (·.categories) (·.form)

theorem mem_paradigm {I : Finset ReflexivePronoun} {c : Person.Category} {f : String} :
    f ∈ paradigm I c ↔ ∃ p ∈ I, c ∈ p.categories ∧ p.form = f :=
  Morphology.mem_formsAt

/-- A reflexive's word is of UD pronoun type `Prs` and marked reflexive. -/
def toWord : Morphology.Word := p.toPronoun.toWord (some .Prs) true

/-- A reflexive pronoun is a reflexive anaphor. -/
@[simp]
theorem bindingClassOf_toWord : Binding.bindingClassOf p.toWord = some .reflexive :=
  Pronoun.bindingClassOf_toWord_reflex _ _

end ReflexivePronoun
