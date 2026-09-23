module

public import Linglib.Semantics.Reference.Deixis
public import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Demonstrative pronouns

A demonstrative pronoun is a pronoun with the deictic contrast it encodes: proximal, medial or
distal, or none for a distance-neutral form such as German *dieser*. What makes a form a
demonstrative is that deictic feature and not its traditional label. [patel-grosz-grosz-2017]
argue that German *der*, *die*, *das*, traditionally called demonstrative pronouns, are personal
pronouns built on the strong article and encode no deixis, so they are `PersonalPronoun`s here
(`Studies/PatelGroszGrosz2017.lean`). `DemonstrativePronoun` is one carrier of the
`Demonstrative` capability; a demonstrative determiner or pro-adverb would be a sibling carrier.

## Main declarations

* `DemonstrativePronoun` — a pronoun with its deictic contrast
* `DemonstrativePronoun.toWord` — its token, of UD pronoun type `Dem`

## References

* [P. Patel-Grosz and P. G. Grosz, *Revisiting Pronominal Typology*
  (2017)][patel-grosz-grosz-2017]
-/

@[expose] public section

/-- A demonstrative pronoun: the general `Pronoun` with the deictic contrast it encodes,
`unspecified` for a distance-neutral form. Its meaning is the deictic
`Reference.Description.demonstrative` over its restrictor. -/
structure DemonstrativePronoun extends Pronoun where
  /-- The deictic contrast the form encodes. -/
  deixis : Reference.Deixis
  deriving Repr, DecidableEq

instance : HasPhi DemonstrativePronoun := ⟨fun d ↦ d.toPronoun.phi⟩

/-- A demonstrative's token is of UD pronoun type `Dem`. -/
def DemonstrativePronoun.toWord (d : DemonstrativePronoun) : Morphology.Word :=
  d.toPronoun.toWord (some .Dem)

instance : Demonstrative DemonstrativePronoun := ⟨DemonstrativePronoun.deixis⟩
