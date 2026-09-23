module

public import Linglib.Syntax.Category.Pronoun.Basic
public import Linglib.Syntax.Reciprocal

/-!
# Reciprocal pronouns

A reciprocal pronoun is a pronoun that is the nominal exponent of reciprocity: it carries the
marker data of `Syntax/Reciprocal.lean`, the nominal strategy it realizes and the readings it
covers, and its kind fixes the reciprocal binding class. A fragment writes the pronoun once and
derives its `Reciprocal.Marker` with `toMarker`; Hungarian *egymás*, Japanese *otagai* and Wan
*ɔ̄ŋ̄* are such objects. Verbal and clitic reciprocal strategies are not pronouns and stay bare
markers.

## Main declarations

* `ReciprocalPronoun` — a pronoun with its reciprocal strategy and readings
* `ReciprocalPronoun.toMarker` — its entry in a marker inventory
* `ReciprocalPronoun.bindingClassOf_toWord` — its token classifies as a reciprocal anaphor

## References

* [R. Nordlinger, *The Typology of Reciprocal Constructions* (2023)][nordlinger-2023]
-/

@[expose] public section

/-- A reciprocal pronoun: the general `Pronoun` as the nominal exponent of reciprocity, with the
strategy it realizes and the readings it covers. -/
structure ReciprocalPronoun extends Pronoun where
  /-- The nominal strategy: a dedicated pronoun (*egymás*, *otagai*) or a two-part quantifier
  noun phrase (*each other*). -/
  strategy : Reciprocal.Strategy := .recipPronoun
  /-- The readings the form covers. -/
  readings : Finset Reciprocal.Reading := {.reciprocal}
  deriving DecidableEq

/-- The marker entry of a reciprocal pronoun. -/
def ReciprocalPronoun.toMarker (p : ReciprocalPronoun) : Reciprocal.Marker :=
  { form := p.form, script := p.script, strategy := p.strategy, readings := p.readings }

instance : HasPhi ReciprocalPronoun := ⟨fun p ↦ p.toPronoun.phi⟩

/-- A reciprocal's word is of UD pronoun type `Rcp`. -/
def ReciprocalPronoun.toWord (p : ReciprocalPronoun) : Morphology.Word :=
  p.toPronoun.toWord (some .Rcp)

/-- A reciprocal pronoun is a reciprocal anaphor. -/
@[simp]
theorem ReciprocalPronoun.bindingClassOf_toWord (p : ReciprocalPronoun) :
    Binding.bindingClassOf p.toWord = some .reciprocal :=
  Pronoun.bindingClassOf_toWord_rcp _

