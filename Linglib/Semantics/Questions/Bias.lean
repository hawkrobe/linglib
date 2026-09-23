module

public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Finset.Prod
public import Linglib.Semantics.Polarity.Basic

/-!
# Polar question bias

A polar question is sensitive to two bodies of information bearing on its prejacent `p`: the
contextual evidence available in the discourse ([buring-gunlogson-2000]) and the prior belief of
the speaker, original bias ([ladd-1981], [romero-han-2004]). Each supports `p`, supports `¬p`, or
neither, so its state is a sign, `1`, `-1` or `0`, and reading it relative to `¬p` negates it.

A bias value in the scheme of [sudo-2013] is the set of states a question is compatible with:
[+s] (`BiasValue.plus`), its complement [−s] (`BiasValue.minus`) and [neutral]. A `BiasProfile`
pairs an evidential and an epistemic value, and its `felicity` is the set of situations it admits.
`PQForm` names the three polar-question forms.

## References

* [buring-gunlogson-2000]
* [ladd-1981]
* [romero-han-2004]
* [sudo-2013]
* [romero-2024]
-/

@[expose] public section

namespace Question

/-- The three polar question forms ([romero-2024] §1). -/
inductive PQForm where
  /-- Positive question: [p?]. "Is Jane coming?" -/
  | posQ
  /-- Low negation question: [not p?]. "Is Jane not coming?" -/
  | loNQ
  /-- High negation question: [n't p?]. "Isn't Jane coming?" -/
  | hiNQ
  deriving DecidableEq, Repr, Fintype

/-- A bias value ([sudo-2013]): the states of a body of information, the sign of the prejacent
it supports, that a question is compatible with. -/
abbrev BiasValue := Finset SignType

namespace BiasValue

/-- [+s]: only a body of information supporting the `s` proposition. -/
def plus (s : Polarity) : BiasValue := {(s : SignType)}

/-- [−s]: any body of information not supporting the `s` proposition. -/
def minus (s : Polarity) : BiasValue := (plus s)ᶜ

/-- [neutral]: only a body of information supporting neither. -/
def neutral : BiasValue := {0}

end BiasValue

/-- A bias profile: the contextual evidence and the prior beliefs of the speaker a question is
compatible with. -/
structure BiasProfile where
  /-- The contextual evidence the question is compatible with. -/
  evidential : BiasValue
  /-- The prior beliefs of the speaker the question is compatible with. -/
  epistemic : BiasValue
  deriving DecidableEq

/-- The situations a profile admits: pairs of contextual evidence and prior belief. -/
def BiasProfile.felicity (b : BiasProfile) : Finset (SignType × SignType) :=
  b.evidential ×ˢ b.epistemic

end Question
