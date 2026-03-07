import Linglib.Core.Lexical.Pronouns

/-!
# Hungarian Reciprocal Fragment
@cite{nordlinger-2023} @cite{siloni-2008}

Hungarian uses the reciprocal pronoun "egymás" (literally 'one-another').
This is an NP/argument strategy (bivalent): the reciprocal occupies the
object position and preserves transitivity. It is distinct from the
reflexive "maga/maguk".

Hungarian reciprocals are lexically formed per @cite{siloni-2008} and
CAN form discontinuous reciprocals with the comitative "egymással".
-/

namespace Fragments.Hungarian.Reciprocals

open Core.Pronouns

/-- egymás — reciprocal pronoun 'each other'. -/
def egymas : PronounEntry :=
  { form := "egymás", person := some .third, number := some .pl }

/-- maga — reflexive pronoun (3sg, for contrast). -/
def maga : PronounEntry :=
  { form := "maga", person := some .third, number := some .sg }

/-- Hungarian reciprocal is formally distinct from reflexive. -/
theorem recip_distinct_from_reflexive :
    egymas.form ≠ maga.form := by decide

end Fragments.Hungarian.Reciprocals
