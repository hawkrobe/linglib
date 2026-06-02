import Linglib.Syntax.Pronoun.Basic

/-!
# Russian Reciprocal Fragment
[nordlinger-2023] [konig-kokutani-2006]

Russian uses a dedicated reciprocal pronoun "drug druga" (друг друга,
literally 'friend of friend'). This is an NP/argument strategy (bivalent):
it occupies the object position and preserves transitivity. It is formally
distinct from the reflexive "sebja" (себя).

The first element "drug" agrees in case with the subject, while "druga"
takes the case assigned by the verb.
-/

namespace Russian.Reciprocals

open Pronoun

/-- друг друга *drug druga* — reciprocal pronoun 'each other'. -/
def drugDruga : PersonalPronoun :=
  { form := "drug druga", script := some "друг друга"
  , person := some .third, number := some .pl }

/-- себя *sebja* — reflexive pronoun (for contrast). -/
def sebja : PersonalPronoun :=
  { form := "sebja", script := some "себя"
  , person := some .third }

/-- Russian reciprocal is formally distinct from reflexive. -/
theorem recip_distinct_from_reflexive :
    drugDruga.form ≠ sebja.form := by decide

end Russian.Reciprocals
