module

public import Linglib.Semantics.Presupposition.Basic
public import Linglib.Logic.Natural.ImplicationSignature

/-!
# Implicative verbs

Karttunen analyzes an implicative sentence as a presupposition–proposition pair: it asserts the
proposition `v(S)` and presupposes that `v(S)` is a condition for the complement, so that what it
implies about the complement follows from the assertion or from its denial. The condition is read
off the implication signature (`NaturalLogic.ImplicationSignature`): a verb implying a complement
in a positive context presupposes `v(S)` sufficient for it, and one implying a complement in a
negative context presupposes `v(S)` necessary for the complement's negation. Here the conditions
are read through any relations of sufficiency and necessity that are sound for truth at a world
(`Implicative.Reading`), Karttunen's own reading being the material conditional at the world
(`Implicative.Reading.material`), and under every reading an implicative sentence implies what its
signature says.

## Main definitions

* `Implicative.Reading`: relations of sufficiency and necessity between facts, sound at worlds
* `Implicative.sentence`: the presupposition–proposition pair of a verb with a given implication
  signature

## Main results

* `Implicative.holds_signed_of_mem_implied`: an affirmed or denied claim implies the polarity of
  the complement that its signature records for that context

## References

* [karttunen-1971]
-/

@[expose] public section

open Presupposition NaturalLogic

/-- Polarity acts on partial propositions by negation, the presupposition passing through. -/
instance {W : Type*} : MulAction Polarity (PartialProp W) where
  smul
    | .positive, p => p
    | .negative, p => p.neg
  one_smul _ := rfl
  mul_smul m n p := by
    cases m <;> cases n <;> first | rfl | exact (PartialProp.neg_neg p).symm

namespace Implicative

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

variable {F W : Type*} (R : Reading F W)

/-- The presupposition–proposition pair of a verb with implication signature `s`, asserted
proposition `v` and embedded fact `S`. It presupposes that `v` is sufficient for the complement
`s` implies in a positive context and necessary for the negation of the complement it implies in a
negative context, and it asserts `v`. -/
def sentence (s : ImplicationSignature) (v S : F) : PartialProp W where
  presup w := (∀ q ∈ s.positive, R.Sufficient v (R.signed q S) w) ∧
    ∀ q ∈ s.negative, R.Necessary v (R.signed (.negative * q) S) w
  assertion := R.Holds v

variable {R} {s : ImplicationSignature} {v S : F} {w : W}

/-- A claim of matrix polarity `m` implies the polarity of the complement that its signature
records for a context of that polarity. -/
theorem holds_signed_of_mem_implied {m q : Polarity} (hq : q ∈ s.implied m)
    (hs : (m • sentence R s v S).holds w) : R.Holds (R.signed q S) w := by
  cases m
  · exact R.holds_of_sufficient (hs.1.1 q hq) hs.2
  · by_contra h
    exact hs.2 (R.holds_of_necessary (hs.1.2 q hq) (Reading.holds_signed_negative_mul.2 h))

end Implicative
