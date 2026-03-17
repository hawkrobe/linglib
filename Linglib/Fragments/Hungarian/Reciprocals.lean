import Linglib.Core.Lexical.Pronouns

/-!
# Hungarian Reciprocal Fragment
@cite{siloni-2008} @cite{dalrymple-haug-2024}

Hungarian uses the reciprocal pronoun "egymás" (literally 'one-another').
This is an NP/argument strategy (bivalent): the reciprocal occupies the
object position and preserves transitivity. It is distinct from the
reflexive "maga/maguk".

Hungarian reciprocals are lexically formed per @cite{siloni-2008} and
CAN form discontinuous reciprocals with the comitative "egymással".

## Singular Antecedents and Reciprocal Scope

@cite{dalrymple-haug-2024} §2 (citing @cite{rakosi-2019}) shows that the
antecedent of *egymás* in Hungarian can be a syntactically singular
null pronoun. When the matrix subject is a coordination of singulars
(e.g., "Péter és Éva"), singular agreement is optionally available in
Hungarian, and the embedded null pronoun must be interpreted as bound.
This forces a wide-scope (I-)reading of the reciprocal.

This contradicts the common generalization that reciprocals require a
syntactically plural antecedent. In Hungarian, the plurality requirement
is semantic (the matrix subject denotes a plurality) but the local
syntactic antecedent can be singular.
-/

namespace Fragments.Hungarian.Reciprocals

open Core.Pronouns

/-- egymás — reciprocal pronoun 'each other'. -/
def egymas : PronounEntry :=
  { form := "egymás", person := some .third, number := some .pl }

/-- maga — reflexive pronoun (3sg, for contrast). -/
def maga : PronounEntry :=
  { form := "maga", person := some .third, number := some .sg }

/-- Whether a singular null pronoun can serve as the local antecedent
    of the reciprocal. In Hungarian, coordinated singular subjects
    can trigger singular agreement, making the embedded null pronoun
    syntactically singular but semantically bound to a plural subject.
    @cite{dalrymple-haug-2024} §2, @cite{rakosi-2019}. -/
def allowsSingularAntecedent : Bool := true

/-- When the local antecedent is a singular bound pronoun, only the
    wide-scope (I-)reading is available: the singular pronoun denotes
    an individual, so group identity (∪) is impossible.
    @cite{dalrymple-haug-2024} §2, example (10). -/
def singularAntecedentForcesWideScope : Bool := true

/-- Hungarian reciprocal is formally distinct from reflexive. -/
theorem recip_distinct_from_reflexive :
    egymas.form ≠ maga.form := by decide

/-- Singular antecedent forces wide scope. -/
theorem singular_forces_wide :
    allowsSingularAntecedent = true ∧ singularAntecedentForcesWideScope = true := ⟨rfl, rfl⟩

end Fragments.Hungarian.Reciprocals
