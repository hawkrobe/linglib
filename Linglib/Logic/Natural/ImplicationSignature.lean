module

public import Linglib.Semantics.Polarity.Basic

/-!
# Implication signatures

A complement-taking operator such as *manage*, *force* or *refuse* implies something about its
complement in a positive context, in a negative context, or in both. Nairn, Condoravdi and Karttunen
classify these operators by their implication signature, the polarity of the complement each
context implies, if any: *manage* is `+/−`, since *managed to leave* implies *left* and *didn't
manage to leave* implies *didn't leave*; *force* is `+/◦`, *refuse* `−/◦`, *hesitate* `◦/+`, and a
propositional attitude such as *want* is `◦/◦`. MacCartney and Manning count nine signatures,
covering the two-way and one-way implicatives, the factives and the attitudes.

## Main definitions

* `NaturalLogic.ImplicationSignature`: the complement's implied polarity in a positive and in a
  negative context
* `NaturalLogic.ImplicationSignature.implied`: the polarity implied in a context of a given
  polarity

## References

* [nairn-condoravdi-karttunen-2006]
* [maccartney-manning-2009]
-/

@[expose] public section

namespace NaturalLogic

/-- The implication signature of a complement-taking operator gives the polarity of the complement
it implies in a positive context and in a negative context, `none` where it implies nothing. -/
@[ext]
structure ImplicationSignature where
  /-- The complement's implied polarity in a positive context. -/
  positive : Option Polarity
  /-- The complement's implied polarity in a negative context. -/
  negative : Option Polarity
  deriving DecidableEq, Repr

namespace ImplicationSignature

/-- The polarity of the complement implied in a context of polarity `m`. -/
def implied (s : ImplicationSignature) : Polarity → Option Polarity
  | .positive => s.positive
  | .negative => s.negative

@[simp] theorem implied_positive (s : ImplicationSignature) : s.implied .positive = s.positive :=
  rfl

@[simp] theorem implied_negative (s : ImplicationSignature) : s.implied .negative = s.negative :=
  rfl

end ImplicationSignature

end NaturalLogic
