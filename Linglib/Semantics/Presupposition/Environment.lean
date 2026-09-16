import Linglib.Data.Examples.Schema
import Linglib.Data.UD.Basic
import Linglib.Semantics.Attitudes.Factivity

/-!
# Embedding environments

An environment is the position a sentence is embedded in: unembedded, or under one of the
entailment-cancelling operators, negation, a polar question, the antecedent of a conditional
and an epistemic possibility modal. The sentence in each environment is the family of sentences
of a trigger ([matthewson-2004], [tonhauser-beaver-roberts-simons-2013]), and a content projects
when the embedded members still carry it. Example rows record a sentence's environment, whether
the content projected, and the person of the matrix subject, and the readers here type those
features. Karttunen's cancellation is the one lexical prediction
over the family: a semi-factive loses its presupposition in the first person under a question
or a conditional antecedent, while an emotive factive keeps it everywhere ([karttunen-1971]).

## References

* [tonhauser-beaver-roberts-simons-2013]
* [matthewson-2004]
* [karttunen-1971]
-/

namespace Presupposition

/-- An environment is the position a sentence is embedded in: unembedded, or under an
entailment-cancelling operator. -/
inductive Environment where
  | atomic
  | negation
  | question
  | conditionalAntecedent
  | epistemicModal
  deriving DecidableEq, Repr, Fintype

namespace Environment

/-- The member embeds the atomic sentence under an entailment-cancelling operator. -/
def IsEmbedded (f : Environment) : Prop := f ≠ atomic

instance : DecidablePred IsEmbedded := fun f ↦ inferInstanceAs (Decidable (f ≠ atomic))

/-- The names of the environments as example rows record them. -/
def table : List (String × Environment) :=
  [("atomic", atomic), ("negation", negation), ("question", question),
    ("conditional antecedent", conditionalAntecedent), ("epistemic modal", epistemicModal)]

end Environment

/-- A factivity class loses its presupposition in an environment with a matrix subject of the
given person: the semi-factives in the first person under a question or a conditional
antecedent, and nothing else ([karttunen-1971]). -/
def _root_.Factivity.Cancelled : Factivity → Environment → UD.Person → Prop
  | .semi, .question, .first => True
  | .semi, .conditionalAntecedent, .first => True
  | _, _, _ => False

instance (c : Factivity) (f : Environment) (p : UD.Person) : Decidable (c.Cancelled f p) := by
  unfold Factivity.Cancelled; split <;> infer_instance

end Presupposition

namespace Data.Examples.LinguisticExample

open Presupposition

/-- The environment a row's sentence is embedded in. -/
def environment? (e : LinguisticExample) : Option Environment :=
  e.parse? "environment" Environment.table

/-- Whether the row's content projected, as the row records it. -/
def projective? (e : LinguisticExample) : Option Bool :=
  e.parse? "projective" [("yes", true), ("no", false)]

/-- The person of the row's matrix subject. -/
def person? (e : LinguisticExample) : Option UD.Person :=
  e.parse? "person" [("1", .first), ("2", .second), ("3", .third)]

end Data.Examples.LinguisticExample
