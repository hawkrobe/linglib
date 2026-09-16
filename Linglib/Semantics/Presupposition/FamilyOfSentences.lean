import Linglib.Data.Examples.Schema
import Linglib.Data.UD.Basic
import Linglib.Semantics.Attitudes.Factivity

/-!
# The family of sentences

The family of sentences of a trigger is the atomic sentence with its embeddings under the
entailment-cancelling operators: negation, a polar question, the antecedent of a conditional
and an epistemic possibility modal ([matthewson-2004], [tonhauser-beaver-roberts-simons-2013]).
A content projects when the embedded members still carry it. Example rows record the member a
sentence instantiates, whether the content projected, and the person of the matrix subject, and
the readers here type those features. Karttunen's cancellation is the one lexical prediction
over the family: a semi-factive loses its presupposition in the first person under a question
or a conditional antecedent, while an emotive factive keeps it everywhere ([karttunen-1971]).

## References

* [tonhauser-beaver-roberts-simons-2013]
* [matthewson-2004]
* [karttunen-1971]
-/

namespace Presupposition

/-- A member of the family of sentences is the atomic sentence or one of its embeddings under
an entailment-cancelling operator. -/
inductive Family where
  | atomic
  | negation
  | question
  | conditionalAntecedent
  | epistemicModal
  deriving DecidableEq, Repr, Fintype

namespace Family

/-- The member embeds the atomic sentence under an entailment-cancelling operator. -/
def IsEmbedded (f : Family) : Prop := f ≠ atomic

instance : DecidablePred IsEmbedded := fun f ↦ inferInstanceAs (Decidable (f ≠ atomic))

/-- The names of the members as example rows record them. -/
def table : List (String × Family) :=
  [("atomic", atomic), ("negation", negation), ("question", question),
    ("conditional antecedent", conditionalAntecedent), ("epistemic modal", epistemicModal)]

end Family

/-- A factivity class loses its presupposition in a member of the family with a matrix subject
of the given person: the semi-factives in the first person under a question or a conditional
antecedent, and nothing else ([karttunen-1971]). -/
def _root_.Factivity.Cancelled : Factivity → Family → UD.Person → Prop
  | .semi, .question, .first => True
  | .semi, .conditionalAntecedent, .first => True
  | _, _, _ => False

instance (c : Factivity) (f : Family) (p : UD.Person) : Decidable (c.Cancelled f p) := by
  unfold Factivity.Cancelled; split <;> infer_instance

end Presupposition

namespace Data.Examples.LinguisticExample

open Presupposition

/-- The member of the family of sentences a row instantiates. -/
def family? (e : LinguisticExample) : Option Family := e.parse? "family" Family.table

/-- Whether the row's content projected, as the row records it. -/
def projective? (e : LinguisticExample) : Option Bool :=
  e.parse? "projective" [("yes", true), ("no", false)]

/-- The person of the row's matrix subject. -/
def person? (e : LinguisticExample) : Option UD.Person :=
  e.parse? "person" [("1", .first), ("2", .second), ("3", .third)]

end Data.Examples.LinguisticExample
