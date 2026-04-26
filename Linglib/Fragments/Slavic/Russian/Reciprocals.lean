import Linglib.Core.Lexical.Pronouns

/-!
# Russian Reciprocal Fragment
@cite{nordlinger-2023} @cite{konig-kokutani-2006}

Russian uses a dedicated reciprocal pronoun "drug druga" (друг друга,
literally 'friend of friend'). This is an NP/argument strategy (bivalent):
it occupies the object position and preserves transitivity. It is formally
distinct from the reflexive "sebja" (себя).

The first element "drug" agrees in case with the subject, while "druga"
takes the case assigned by the verb.
-/

namespace Fragments.Slavic.Russian.Reciprocals

open Core.Pronouns

/-- друг друга *drug druga* — reciprocal pronoun 'each other'. -/
def drugDruga : PronounEntry :=
  { form := "drug druga", script := some "друг друга"
  , person := some .third, number := some .pl }

/-- себя *sebja* — reflexive pronoun (for contrast). -/
def sebja : PronounEntry :=
  { form := "sebja", script := some "себя"
  , person := some .third }

/-- Russian reciprocal is formally distinct from reflexive. -/
theorem recip_distinct_from_reflexive :
    drugDruga.form ≠ sebja.form := by decide

end Fragments.Slavic.Russian.Reciprocals
