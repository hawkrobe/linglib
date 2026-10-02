module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Semantics.Polarity.Basic

/-!
# Implicative verbs

An implicative verb such as *manage* presupposes that its prerequisite is a condition for its
complement and asserts the prerequisite, so that the complement follows from the assertion or from
its denial. Karttunen types the condition as sufficient, necessary, or both
(`Implicative.Condition`) and pairs it with the polarity of the complement
(`Implicative.Schema`). Here the conditions are read through any relations of sufficiency and
necessity that are sound for truth at a world (`Implicative.Reading`), Karttunen's own reading
being the material conditional at the world (`Implicative.Reading.material`), and the complement
entailments are proved once for every reading.

## Main definitions

* `Implicative.Condition`, `Implicative.Schema`: the presupposed condition and the complement's
  polarity
* `Implicative.Reading`: relations of sufficiency and necessity between facts, sound at worlds
* `Implicative.Schema.sentence`: the presupposition–proposition pair of an implicative
* `Implicative.Schema.entailed`: the complement polarity a claim commits the speaker to

## Main results

* `Implicative.Schema.holds_imp`, `Implicative.Schema.neg_holds_imp`: an affirmed claim entails
  the complement when the condition is sufficient, a denied one its negation when it is necessary
* `Implicative.Schema.entailed_sound`: every commitment `entailed` records is an entailment

## References

* [karttunen-1971]
-/

@[expose] public section

open Presupposition

/-- Polarity acts on partial propositions by negation, the presupposition passing through. -/
instance {W : Type*} : MulAction Polarity (PartialProp W) where
  smul
    | .positive, p => p
    | .negative, p => p.neg
  one_smul _ := rfl
  mul_smul m n p := by
    cases m <;> cases n <;> first | rfl | exact (PartialProp.neg_neg p).symm

namespace Implicative

/-- The condition an implicative presupposes its prerequisite to be for its complement. -/
inductive Condition where
  /-- The prerequisite suffices for the complement, as for *force*. -/
  | sufficient
  /-- The prerequisite is necessary for the complement, as for *be able*. -/
  | necessary
  /-- The prerequisite is necessary and sufficient for the complement, as for *manage*. -/
  | necessaryAndSufficient
  deriving DecidableEq, Repr

namespace Condition

/-- The condition is at least sufficient. -/
def IsSufficient : Condition → Prop
  | .necessary => False
  | _ => True

/-- The condition is at least necessary. -/
def IsNecessary : Condition → Prop
  | .sufficient => False
  | _ => True

instance (c : Condition) : Decidable c.IsSufficient := by
  cases c <;> unfold IsSufficient <;> infer_instance

instance (c : Condition) : Decidable c.IsNecessary := by
  cases c <;> unfold IsNecessary <;> infer_instance

end Condition

/-- A reading of sufficiency and necessity between facts `F` that is sound for truth at the worlds
`W`. A fact sufficient for another at a world makes it true there when it is true, and a fact
necessary for another is true there when the other is. -/
structure Reading (F W : Type*) where
  /-- The fact holds at the world. -/
  Holds : F → W → Prop
  /-- The negation of a fact. -/
  neg : F → F
  holds_neg (a : F) (w : W) : Holds (neg a) w ↔ ¬ Holds a w
  /-- The first fact is sufficient for the second at the world. -/
  Sufficient : F → F → W → Prop
  /-- The first fact is necessary for the second at the world. -/
  Necessary : F → F → W → Prop
  holds_of_sufficient {a b : F} {w : W} : Sufficient a b w → Holds a w → Holds b w
  holds_of_necessary {a b : F} {w : W} : Necessary a b w → Holds b w → Holds a w

namespace Reading

/-- Karttunen's reading takes facts to be propositions and a condition to be the material
conditional at the world. -/
def material (W : Type*) : Reading (W → Prop) W where
  Holds a w := a w
  neg a w := ¬ a w
  holds_neg _ _ := Iff.rfl
  Sufficient a b w := a w → b w
  Necessary a b w := b w → a w
  holds_of_sufficient h := h
  holds_of_necessary h := h

variable {F W : Type*} (R : Reading F W)

/-- A fact or its negation, by polarity. -/
def signed : Polarity → F → F
  | .positive, a => a
  | .negative, a => R.neg a

variable {R}

theorem holds_signed_negative_mul {q : Polarity} {a : F} {w : W} :
    R.Holds (R.signed (.negative * q) a) w ↔ ¬ R.Holds (R.signed q a) w := by
  cases q
  · exact R.holds_neg a w
  · show R.Holds a w ↔ ¬ R.Holds (R.neg a) w
    rw [R.holds_neg]; exact not_not.symm

end Reading

/-- The lexical signature of an implicative is the condition it presupposes and the polarity of
the complement it speaks of. -/
structure Schema where
  /-- The presupposed condition. -/
  condition : Condition
  /-- Whether the complement is the embedded fact or its negation. -/
  polarity : Polarity
  deriving DecidableEq, Repr

namespace Schema

/-- The schema of the two-way implicatives *manage*, *remember* and *dare*. -/
def manage : Schema := ⟨.necessaryAndSufficient, .positive⟩

/-- The schema of the two-way negative implicatives *fail*, *forget* and *neglect*. -/
def fail : Schema := ⟨.necessaryAndSufficient, .negative⟩

/-- The schema of the one-way implicatives *be able* and *be possible*. -/
def beAble : Schema := ⟨.necessary, .positive⟩

/-- The schema of the one-way negative implicative *hesitate*. -/
def hesitate : Schema := ⟨.necessary, .negative⟩

/-- The schema of *force*, *cause* and *make*. -/
def force : Schema := ⟨.sufficient, .positive⟩

/-- The schema of *prevent*. -/
def prevent : Schema := ⟨.sufficient, .negative⟩

variable {F W : Type*} (R : Reading F W) (k : Schema)

/-- The presupposition–proposition pair of an implicative with prerequisite `v` and embedded fact
`S`. It presupposes that `v` stands in the condition to the complement and asserts `v`. -/
def sentence (v S : F) : PartialProp W where
  presup w := (k.condition.IsSufficient → R.Sufficient v (R.signed k.polarity S) w) ∧
    (k.condition.IsNecessary → R.Necessary v (R.signed k.polarity S) w)
  assertion := R.Holds v

variable {R k} {v S : F} {w : W}

/-- An affirmed implicative entails its complement when the condition is sufficient. -/
theorem holds_imp (h : k.condition.IsSufficient) (hs : (k.sentence R v S).holds w) :
    R.Holds (R.signed k.polarity S) w :=
  R.holds_of_sufficient (hs.1.1 h) hs.2

/-- A denied implicative entails the negation of its complement when the condition is
necessary. -/
theorem neg_holds_imp (h : k.condition.IsNecessary)
    (hs : (PartialProp.neg (k.sentence R v S)).holds w) : ¬ R.Holds (R.signed k.polarity S) w :=
  fun hS ↦ hs.2 (R.holds_of_necessary (hs.1.2 h) hS)

variable (k)

/-- A claim of matrix polarity `m` commits the speaker on the complement: an affirmed one when
the condition is sufficient, a denied one when it is necessary. -/
def Commits : Polarity → Prop
  | .positive => k.condition.IsSufficient
  | .negative => k.condition.IsNecessary

instance (m : Polarity) : Decidable (k.Commits m) := by
  cases m <;> unfold Commits <;> infer_instance

/-- The polarity of the embedded fact that a claim of matrix polarity `m` commits the speaker to,
if any, the product of the matrix polarity and the complement's. -/
def entailed (m : Polarity) : Option Polarity :=
  if k.Commits m then some (m * k.polarity) else none

variable {k}

/-- Each commitment that `entailed` records is entailed by the claim. -/
theorem entailed_sound {m q : Polarity} (he : k.entailed m = some q)
    (hs : (m • k.sentence R v S).holds w) : R.Holds (R.signed q S) w := by
  unfold entailed at he
  split_ifs at he with hc
  cases he
  cases m
  · exact holds_imp hc hs
  · exact Reading.holds_signed_negative_mul.2 (neg_holds_imp hc hs)

end Schema

end Implicative
