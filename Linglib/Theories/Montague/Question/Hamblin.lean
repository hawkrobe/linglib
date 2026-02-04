import Linglib.Theories.Montague.Question.Basic

/-!
# Questions/Hamblin.lean

Hamblin Semantics for Questions.

## The Hamblin View

Questions denote **sets of propositions** - their possible answers.
A question Q has type <<s,t>,t>, i.e., (W → Bool) → Bool.

This contrasts with G&S partition semantics where questions are equivalence
relations. The Hamblin view is:
- More directly compositional (questions are the same type as GQs)
- Naturally conjoinable (type ends in t)
- Foundation for alternative semantics (Kratzer & Shimoyama 2002)

## Coordination

Since <<s,t>,t> is conjoinable, we can directly apply Partee & Rooth's
generalized conjunction:
- Q₁ ∧ Q₂ = λp. Q₁(p) ∧ Q₂(p)
- Q₁ ∨ Q₂ = λp. Q₁(p) ∨ Q₂(p)

## References

- Hamblin (1973). Questions in Montague English. Foundations of Language.
- Karttunen (1977). Syntax and Semantics of Questions. L&P.
- Kratzer & Shimoyama (2002). Indeterminate Pronouns. SALT 12.
- Partee & Rooth (1983). Generalized Conjunction and Type Ambiguity.
-/

namespace Montague.Question.Hamblin

-- Hamblin Question Denotations

/-- Hamblin question denotation: a set of propositions (possible answers).

    A question Q is true of proposition p iff p is a possible answer to Q.
    Type: <<s,t>,t> in Montague notation. -/
abbrev QuestionDen (W : Type*) := (W → Bool) → Bool

/-- Construct a Hamblin question from a list of alternative propositions.
    A proposition p is an answer iff it matches one of the alternatives. -/
def fromAlternatives {W : Type*} [BEq W] (alts : List (W → Bool)) (worlds : List W) : QuestionDen W :=
  fun p => alts.any fun alt => worlds.all fun w => p w == alt w

/-- A polar question has two alternatives: p and ¬p -/
def polar {W : Type*} [BEq W] (p : W → Bool) (worlds : List W) : QuestionDen W :=
  fun ans => (worlds.all fun w => ans w == p w) || (worlds.all fun w => ans w == !p w)

/-- A wh-question over a domain: "which x satisfies P?" -/
def which {W E : Type*} [BEq W] (domain : List E) (pred : E → W → Bool) (worlds : List W) : QuestionDen W :=
  fun ans => domain.any fun e => worlds.all fun w => ans w == pred e w

-- Coordination (Partee & Rooth style)

/-- Conjoin two question denotations.
    (Q₁ ∧ Q₂)(P) = Q₁(P) ∧ Q₂(P)

    Semantically: P answers (Q₁ ∧ Q₂) iff P answers both Q₁ and Q₂. -/
def conj {W : Type*} (q1 q2 : QuestionDen W) : QuestionDen W :=
  fun p => q1 p && q2 p

/-- Disjoin two question denotations.
    (Q₁ ∨ Q₂)(P) = Q₁(P) ∨ Q₂(P)

    Semantically: P answers (Q₁ ∨ Q₂) iff P answers Q₁ or P answers Q₂. -/
def disj {W : Type*} (q1 q2 : QuestionDen W) : QuestionDen W :=
  fun p => q1 p || q2 p

instance {W : Type*} : Add (QuestionDen W) where add := conj
instance {W : Type*} : HAdd (QuestionDen W) (QuestionDen W) (QuestionDen W) where hAdd := conj

-- Algebraic Properties

/-- Conjunction of questions is commutative. -/
theorem conj_comm {W : Type*} (q1 q2 : QuestionDen W) (p : W → Bool) :
    conj q1 q2 p = conj q2 q1 p := Bool.and_comm _ _

/-- Disjunction of questions is commutative. -/
theorem disj_comm {W : Type*} (q1 q2 : QuestionDen W) (p : W → Bool) :
    disj q1 q2 p = disj q2 q1 p := Bool.or_comm _ _

/-- Conjunction is associative. -/
theorem conj_assoc {W : Type*} (q1 q2 q3 : QuestionDen W) (p : W → Bool) :
    conj (conj q1 q2) q3 p = conj q1 (conj q2 q3) p := Bool.and_assoc _ _ _

/-- Disjunction is associative. -/
theorem disj_assoc {W : Type*} (q1 q2 q3 : QuestionDen W) (p : W → Bool) :
    disj (disj q1 q2) q3 p = disj q1 (disj q2 q3) p := Bool.or_assoc _ _ _


-- Answerhood

/-- A proposition p is a complete answer to Q if Q(p) = true. -/
def isAnswer {W : Type*} (q : QuestionDen W) (p : W → Bool) : Bool := q p

/-- The tautology answers every question vacuously (if in the denotation). -/
def tautology {W : Type*} : W → Bool := fun _ => true

/-- The contradiction answers no question. -/
def contradiction {W : Type*} : W → Bool := fun _ => false

-- Connection to Partition Semantics

/-!
## Hamblin vs Partition Semantics

The two views are related but not equivalent:

**Hamblin**: Q = {p | p is a possible answer}
**Partition**: Q = equivalence relation where w ~ v iff same answer

A Hamblin question can be converted to a partition by taking the
equivalence relation induced by the alternatives. Conversely, a
partition can be viewed as a Hamblin question whose answers are
the characteristic functions of its cells.

See `Partition.lean` for the G&S partition semantics.
-/

end Montague.Question.Hamblin
