module

public import Linglib.Core.Relation.SetRel
public import Linglib.Data.Examples.Schema
public import Linglib.Data.UD.Features

/-!
# Embedding environments

An environment is the position a sentence is embedded in: unembedded, or under one of the
entailment-cancelling operators, negation, a polar question, the antecedent of a conditional
and an epistemic possibility modal. The sentence in each environment is the family of sentences
of a trigger, in the terms of Matthewson and of Tonhauser, Beaver, Roberts and Simons, and a
content projects when the embedded members still carry it. Each member evaluates its sentence
along a relation, the identity except under the modal (`Environment.rel`), and these relations
are reflexive when the modal's is, so that a requirement on the local context of the sentence is
a requirement on the context of the member. Example rows record a sentence's environment,
whether the content projected, and the person of the matrix subject, and the readers here type
those features.

## References

* [tonhauser-beaver-roberts-simons-2013]
* [matthewson-2004]
-/

@[expose] public section

namespace Presupposition

/-- An environment is the position a sentence is embedded in, unembedded or under an
entailment-cancelling operator. -/
inductive Environment where
  | atomic
  | negation
  | question
  | conditionalAntecedent
  | epistemicModal
  deriving DecidableEq, Repr, Fintype

namespace Environment

/-- The relation along which a member of the family evaluates its sentence, where `M` is the
accessibility of the possibility modal. The other members are holes, evaluating the sentence at
the world of the member itself. -/
def rel {W : Type*} (M : SetRel W W) : Environment → SetRel W W
  | epistemicModal => M
  | _ => .id

instance {W : Type*} (M : SetRel W W) [M.IsRefl] (e : Environment) : (e.rel M).IsRefl := by
  cases e
  case epistemicModal => exact ‹M.IsRefl›
  all_goals exact SetRel.isRefl_id

/-- Where the modal's accessibility is the identity, every member is a hole. -/
@[simp] theorem rel_id {W : Type*} (e : Environment) : e.rel (SetRel.id : SetRel W W) = .id := by
  cases e <;> rfl

/-- The names of the environments as example rows record them. -/
def table : List (String × Environment) :=
  [("atomic", atomic), ("negation", negation), ("question", question),
    ("conditional antecedent", conditionalAntecedent), ("epistemic modal", epistemicModal)]

end Environment

end Presupposition

namespace Datum

open Presupposition

/-- The environment a row's sentence is embedded in. -/
def environment? (e : Datum) : Option Environment :=
  e.parse? "environment" Environment.table

/-- Whether the row's content projected, as the row records it. -/
def projective? (e : Datum) : Option Bool :=
  e.parse? "projective" [("yes", true), ("no", false)]

/-- The person of the row's matrix subject. -/
def person? (e : Datum) : Option UD.Person :=
  e.parse? "person" [("1", .first), ("2", .second), ("3", .third)]

end Datum
