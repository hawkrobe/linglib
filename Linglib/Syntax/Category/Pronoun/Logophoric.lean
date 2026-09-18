import Linglib.Semantics.Reference.Logophoricity
import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Logophoric pronouns

A logophoric pronoun is a personal pronoun reserved for an antecedent that fills a perspectival
role, the reported speaker or thinker of the clause it sits in: Ewe *yè*, Wan *mɔ̄*.
`LogophoricPronoun` extends `PersonalPronoun` with the least [sells-1987] role its antecedent
must fill, and is a carrier of the word-class-neutral `Logophoric` capability of
`Semantics/Reference/Logophoricity.lean`. A long-distance reflexive is role-oriented too, but it
is a reflexive; its role lives on `ReflexivePronoun`.

## Main declarations

* `LogophoricPronoun` — a personal pronoun with the role its antecedent must fill
* `instance : Logophoric LogophoricPronoun` — the pronoun carrier of the capability

## References

* [P. Sells, *Aspects of Logophoricity* (1987)][sells-1987]
-/

open Reference (LogophoricRole Logophoric)

/-- A logophoric pronoun: a `PersonalPronoun` with the least [sells-1987] role its antecedent
must fill. It is a pronominal, and what licenses it is the role, not a binding configuration. -/
structure LogophoricPronoun extends PersonalPronoun where
  /-- The least [sells-1987] role an antecedent must fill to license the form. -/
  requiredRole : LogophoricRole
  deriving DecidableEq

instance : HasPhi LogophoricPronoun := ⟨fun p ↦ p.toPronoun.phi⟩

instance : Logophoric LogophoricPronoun := ⟨LogophoricPronoun.requiredRole⟩

/-- Every logophoric pronoun is licensed by a source, the top of the role hierarchy. -/
theorem LogophoricPronoun.licensedBy_source (p : LogophoricPronoun) :
    Logophoric.LicensedBy p .source :=
  Logophoric.source_licenses p
