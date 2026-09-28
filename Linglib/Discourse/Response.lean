module

public import Linglib.Semantics.Polarity.Basic
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype

/-!
# Responses and their polarity features

A responding move reacts to a sentence on the Table, put there by an assertion or a polar
question. [farkas-bruce-2010] classify it by two polarity features: its relative polarity,
[same] when it confirms that sentence and [reverse] when it reverses it, and its absolute
polarity, [+] or [−], the polarity of the sentence it asserts. A `Discourse.Response` records
what fixes both: the move it reacts to, the polarity of the sentence on the Table, and its own
polarity. Its relative polarity is the quotient of the two polarities in the group of
polarities (`Response.relative`), positive for [same] and negative for [reverse].

A polarity particle is used in some responses and not others, so what a theory says about a
particle is a set of responses. Each framework interpreting the particles of a language assigns
them such sets, which form a Boolean algebra: rival interpretations of one particle are compared
by inclusion, and an interpretation is tested against the acceptable responses of the data.
Properties of a particle are properties of its set: the typology of answering negative questions
asks which particle confirms the negative alternative (`Response.ConfirmsNegativeQuestion`).

## Main definitions

* `Discourse.InitiatingMove`: an assertion or a polar question.
* `Discourse.Response`: the move a response reacts to, the antecedent polarity and its own.
* `Discourse.Response.relative`: the relative polarity of a response.
* `Discourse.Response.ConfirmsNegativeQuestion`: a set of responses includes the confirmation of
  a negative question, [same, −].

## References

* [farkas-bruce-2010]
* [sadock-zwicky-1985]
* [holmberg-2016]
-/

@[expose] public section

namespace Discourse

/-- A move that puts a sentence on the Table for a response to react to. -/
inductive InitiatingMove where
  /-- An assertion: a [reverse] response to it is a denial. -/
  | assertion
  /-- A polar question: a [reverse] response to it is a reverse answer. -/
  | polarQuestion
  deriving DecidableEq, Repr, Fintype

/-- A responding move: the move it reacts to, the polarity of the sentence radical on the Table,
and the polarity of the sentence it asserts. -/
structure Response where
  /-- The move responded to. -/
  reactsTo : InitiatingMove
  /-- The polarity of the sentence on the Table. -/
  antecedent : Polarity
  /-- The polarity of the response, its absolute polarity. -/
  polarity : Polarity
  deriving DecidableEq, Repr, Fintype

namespace Response

/-- The relative polarity of a response: positive, [same], when it shares the polarity of the
sentence on the Table, negative, [reverse], when it reverses it. -/
def relative (x : Response) : Polarity := x.polarity / x.antecedent

@[simp] theorem relative_mk (m : InitiatingMove) (a p : Polarity) :
    (⟨m, a, p⟩ : Response).relative = p / a := rfl

/-- A response is [same] iff it shares the polarity of the sentence on the Table. -/
theorem relative_eq_positive_iff {x : Response} :
    x.relative = .positive ↔ x.polarity = x.antecedent :=
  div_eq_one

/-- The responses `S` include the answer confirming the negative alternative of a negative polar
question, [same, −]. Which particle of a language does so tells its system of answering negative
questions: the affirmative one in a system of relative polarity particles, agree/disagree or
truth-based; the negative one in a system of absolute polarity particles, yes/no or
polarity-based ([farkas-bruce-2010], [sadock-zwicky-1985], [holmberg-2016]). -/
def ConfirmsNegativeQuestion (S : Set Response) : Prop :=
  ⟨.polarQuestion, .negative, .negative⟩ ∈ S

instance (S : Set Response) [h : Decidable (⟨.polarQuestion, .negative, .negative⟩ ∈ S)] :
    Decidable (ConfirmsNegativeQuestion S) :=
  h

end Response

end Discourse
