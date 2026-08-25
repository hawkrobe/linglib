import Linglib.Data.WALS.Features.F112A
import Linglib.Data.WALS.Features.F114A
import Linglib.Syntax.Category.Auxiliary.Constructions
import Linglib.Features.Grammaticalization
import Linglib.Morphology.Morph

/-!
# Standard negation

A language negates a declarative verbal main clause with an affix on the
verb, a free particle, or an inflecting negative auxiliary, and some
languages use two morphemes at once (French *ne … pas*). Beyond adding a
marker, negation may restructure the clause — imposing a nonfinite verb
form, neutralizing tense distinctions — which is the symmetric/asymmetric
divide of [miestamo-2005]. Expletive negation is a separate use of the
same morphemes, semantically vacuous under triggers like 'fear' and
'before'.

This file records a language's negation marker(s) and the strategy
classifying them, with per-ISO access to the WALS negation chapters.

## Main declarations

* `Marker`: a standard negation marker, as the morphs exponing it.
* `Strategy`: negative verb, affix, or particle — the grain at which
  negation meets auxiliary-verb constructions and the
  grammaticalization cline.
* `ExpletiveTrigger`: a lexical trigger of expletive negation with the
  negator it licenses.
* `asymmetrySubtypeOfISO`: a language's WALS Ch 114A value.

## Implementation notes

The WALS chapters are the source of truth for the typological values, so
the accessor returns the `Data.WALS` enum rather than a re-labelled
copy. An analysis reaching beyond WALS keeps its own
vocabulary in its study: [miestamo-2005]'s asymmetry subtypes, which
separate an emphasis subtype the atlas does not encode, live in
`Studies/Miestamo2005.lean`.

Polarity-sensitive items (n-words, NPIs, free-choice items) are not
marker-side data; they live in `Fragments/{Lang}/PolarityItems.lean`.

## TODO

* `ExpletiveTrigger.triggerClass` is free text. The taxonomy it
  approximates is `JinKoenig2021.TriggerSubclass`, whose cases the
  Fragment labels do not currently match.

## References

* [dryer-2013-wals], Ch 112A
* [miestamo-2013], Ch 114A
* [miestamo-2005]
* [anderson-2006], §1.7.2
* [heine-1993]
* [jin-koenig-2021]
-/

namespace Syntax.Negation

open Morphology (Morph)

/-! ### Markers and negation systems -/

/-- A standard sentential negation marker. -/
structure Marker where
  /-- The exponent, in surface order; a bipartite marker lists both
      pieces (Burmese *ma-…-bu*). Affixal alternants are recorded by an
      abstract citation form (Turkish *-mA-* for *-ma-* ~ *-me-*). -/
  morphs : List Morph
  /-- Standard interlinear gloss. -/
  gloss : String := "NEG"
  deriving Repr

/-- The surface form of a marker: its morphs with boundary notation,
discontinuous pieces separated by `…`. -/
def Marker.form (m : Marker) : String := toString m.morphs

/-! ### Per-language WALS values -/

/-- WALS Ch 114A: which domain the language's asymmetric negation
affects. -/
def asymmetrySubtypeOfISO (iso : String) :
    Option Data.WALS.F114A.AsymmetricNegationSubtype :=
  (Data.WALS.F114A.lookupISO iso).map (·.value)

/-! ### Expletive negation -/

/-- A lexical trigger of expletive negation together with the negator it
licenses: Italian *prima che … non*, Mandarin *pà … bié*. -/
structure ExpletiveTrigger where
  /-- The trigger's semantic class. -/
  triggerClass : String
  /-- The triggering lexical item. -/
  triggerForm : String
  /-- The negator appearing under the trigger. -/
  negatorForm : String
  /-- Gloss for that negator, when it differs from standard negation. -/
  negatorGloss : Option String := none
  /-- Whether the use is entrenched, when the source classifies it. -/
  highEntrenchment : Option Bool := none
  deriving Repr, BEq, DecidableEq

/-! ### Negation strategy

A **negative auxiliary verb** hosts the inflection its lexical verb
loses (Finnish *ei mene* 'NEG.3SG go'), making negation a special case of
the aux-headed auxiliary-verb construction; an affix or a particle does
not. `Strategy` classifies negation at that grain. -/

open AuxiliaryVerbs (InflPattern)
open Grammaticalization (GramStage)

/-- How a language expresses sentential negation. -/
inductive Strategy where
  /-- An inflecting negative auxiliary (Finnish *ei*, Komi *oz*). -/
  | negVerb
  /-- A bound negative morpheme (Turkish *-mA-*). -/
  | negAffix
  /-- A free negative particle (English *not*, Italian *non*). -/
  | negParticle
  deriving DecidableEq, Repr

/-- A negative verb heads an auxiliary-verb construction, so it is
expected to host the inflection; affixes and particles form no
construction to head. -/
def Strategy.expectedInflPattern : Strategy → Option InflPattern
  | .negVerb => some .auxHeaded
  | .negAffix | .negParticle => none

/-- The strategy is verbal: its negator is itself a verb. -/
def Strategy.IsVerbal : Strategy → Prop
  | .negVerb => True
  | .negAffix | .negParticle => False

instance : DecidablePred Strategy.IsVerbal
  | .negVerb => isTrue trivial
  | .negAffix | .negParticle => isFalse id

/-- The strategy's stage on the grammaticalization cline ([heine-1993];
[anderson-2006] ch. 7): a negative verb is an auxiliary, a negative affix
one stage further. A particle is not a bleached verb, so it is off the
cline entirely. -/
def Strategy.toGramStage : Strategy → Option GramStage
  | .negVerb => some .auxiliary
  | .negAffix => some .affix
  | .negParticle => none

/-- The strategy's negative morpheme in the WALS Ch 112A
classification. -/
def Strategy.morphemeType : Strategy → Data.WALS.F112A.NegativeMorphemeType
  | .negVerb => .negativeAuxiliaryVerb
  | .negAffix => .negativeAffix
  | .negParticle => .negativeParticle

/-- The two projections agree on which strategy is verbal: the cline stage
[anderson-2006] assigns and the morpheme type [miestamo-2005] assigns
partition the strategies identically. -/
theorem toGramStage_auxiliary_iff_morphemeType_auxVerb (s : Strategy) :
    s.toGramStage = some .auxiliary ↔
      s.morphemeType = .negativeAuxiliaryVerb := by
  cases s <;> decide

end Syntax.Negation
