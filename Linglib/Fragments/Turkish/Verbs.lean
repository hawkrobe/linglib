module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Fragments.Turkish.Morphotactics

/-!
# Turkish verbs

This file defines the Turkish verbs that the studies of Qing and colleagues and of Göksel and
Kerslake consume. The preferential attitudes are *kork-* 'fear', *um-* 'hope' and *endişelen-*
'worry', whose distributivity over alternatives follows from the kind of preference each
records. They take a nominalized clause, in the ablative under *kork-* and *endişelen-* and in
the accusative under *um-*, and the first two take it as a question as well. The intransitive
*dolan-* 'walk around' takes no complement. The causatives *öldür-* 'kill' and *yaptır-* 'have
done' are built on *öl-* 'die' and *yap-* 'do' by the voice suffix -DIr.

Turkish is agglutinating, so a verb records the segments of its root and the voice suffixes of
its stem. Its inflected forms are derived by `Turkish.realize`, the attachment of suffixes in
`Turkish.Morphotactics` followed by the surface forms of `Turkish.Phonology`, rather than
listed.

## Main definitions

* `Turkish.Verb`: a Turkish verb, the root `Verb` with its root segments and voice suffixes.
* `Turkish.Verb.suffixes`, `Turkish.Verb.inflect`: the suffix string of a verb under a string
  of inflectional suffixes, and its surface form.
* `Turkish.verbs`: the inventory of the entries.

## References

* [goksel-kerslake-2005]
* [qing-uegaki-2025]
-/

@[expose] public section

open Phonology

namespace Turkish

open ArgumentStructure Turkish.Phonology

/-- A Turkish verb is the root entry, whose `form` is the spelled stem, together with the
segments of its root and the voice suffixes that build its stem. -/
structure Verb extends _root_.Verb where
  /-- The segments of the root. -/
  rootSegments : List Segment
  /-- The voice suffixes of the stem, in order. -/
  voice : List (Verb.Exponent .voice) := []
  deriving BEq

namespace Verb

/-- `v.suffixes sfx` is the suffix string of the verb under the inflectional suffixes `sfx`,
its voice suffixes followed by `sfx`. -/
def suffixes (v : Verb) (sfx : List (Σ σ, Exponent σ)) : List (Σ σ, Exponent σ) :=
  v.voice.map (⟨.voice, ·⟩) ++ sfx

/-- `v.inflect sfx` is the surface form of the verb under the inflectional suffixes `sfx`,
which with no suffixes is the stem. -/
def inflect (v : Verb) (sfx : List (Σ σ, Exponent σ)) : List Segment :=
  realize v.rootSegments ((v.suffixes sfx).map fun e ↦ Exponent.form e.2)

end Verb

/-- The frame of a verb that takes a nominalized clause as a question. -/
def nominalizedQuestion : ArgumentFrame :=
  ⟨some .nominal, [.clausal (coding := some .nominalized) (types := .interrogatives)]⟩

/-! ### Preferential attitudes -/

/-- *kork-* 'fear', a negative preference by comparison of degrees. -/
def kork : Verb where
  form := "kork"
  rootSegments := [k, o, r, k]
  frames := [ArgumentFrame.gerund, nominalizedQuestion]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .negative))

/-- *um-* 'hope', a positive preference by comparison of degrees. -/
def um : Verb where
  form := "um"
  rootSegments := [u, m]
  frames := [ArgumentFrame.gerund]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential (.degreeComparison .positive))

/-- *endişelen-* 'worry', a preference relative to uncertainty. -/
def endişelen : Verb where
  form := "endişelen"
  rootSegments := [e, n, d, i, ş, e, l, e, n]
  frames := [ArgumentFrame.gerund, nominalizedQuestion]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .uncertaintyBased)

/-! ### Motion -/

/-- *dolan-* 'walk around', intransitive. -/
def dolan : Verb where
  form := "dolan"
  rootSegments := [d, o, l, a, n]
  frames := [ArgumentFrame.intransitive]
  passivizable := false

/-! ### Causatives -/

/-- *öldür-* 'kill', the causative of *öl-* 'die'. -/
def öldür : Verb where
  form := "öldür"
  rootSegments := [ö, l]
  voice := [.causative]
  frames := [ArgumentFrame.np]
  causative := some .make

/-- *yaptır-* 'have done, make do', the causative of *yap-* 'do, make'. -/
def yaptır : Verb where
  form := "yaptır"
  rootSegments := [y, a, p]
  voice := [.causative]
  frames := [ArgumentFrame.smallClause]
  readings := [{ frame := ArgumentFrame.smallClause, control := some .objectControl }]
  causative := some .make

/-- `verbs` lists the entries. -/
def verbs : List Verb := [kork, um, endişelen, dolan, öldür, yaptır]

end Turkish
