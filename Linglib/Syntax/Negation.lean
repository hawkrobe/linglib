module

public import Linglib.Data.WALS.Features.F112A
public import Linglib.Data.WALS.Features.F114A
public import Linglib.Syntax.Category.Auxiliary.Constructions
public import Linglib.Morphology.Morph

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
classifying them, with per-ISO access to the WALS negation chapters. The
declarations share the root `Negation` namespace with the classification of
expletive negation in `Semantics/Polarity/ExpletiveNegation.lean`.

## Main declarations

* `Marker`: a standard negation marker, as the morphs exponing it.
* `Pair`: an affirmative and its negative counterpart, as morphs.
* `Strategy`: negative verb, affix, or particle — the grain at which
  negation meets auxiliary-verb constructions.
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

## References

* [dryer-2013-wals], Ch 112A
* [miestamo-2013], Ch 114A
* [miestamo-2005]
* [anderson-2006a], §1.7.2
* [jin-koenig-2021]
-/

@[expose] public section

namespace Negation

open Morphology (Morph)

/-! ### Markers and negation systems -/

/-- A standard sentential negation marker. -/
structure Marker where
  /-- The exponent as contiguous pieces in surface order; a bipartite
      marker has two (Burmese *ma-…-bu*). Affixal alternants are recorded by
      an abstract citation form (Turkish *-mA-* for *-ma-* ~ *-me-*). -/
  pieces : List (List Morph)
  /-- Standard interlinear gloss. -/
  gloss : String := "NEG"
  deriving Repr

/-- The surface form of a marker: its pieces in boundary notation, separated
by `…`. -/
def Marker.form (m : Marker) : String := String.intercalate "…" (m.pieces.map Morph.surface)

/-- The morphs of a marker, across its pieces. -/
def Marker.morphs (m : Marker) : List Morph := m.pieces.flatten

/-- An affirmative clause or verb form paired with its negative counterpart, each as its morphs
in surface order. Morphs are cited in one form across the pair, so that a phonologically
conditioned alternation, such as the buffer glide of Turkish *gel-me-yecek* beside *gel-ecek*,
does not distinguish them. -/
structure Pair where
  /-- The affirmative. -/
  affirmative : List Morph
  /-- The negative. -/
  negative : List Morph
  deriving DecidableEq, Repr

/-! ### Per-language WALS values -/

/-- WALS Ch 114A: which domain the language's asymmetric negation
affects. -/
def asymmetrySubtypeOfISO (iso : String) :
    Option Data.WALS.F114A.AsymmetricNegationSubtype :=
  (Data.WALS.F114A.lookupISO iso).map (·.value)

/-! ### Negation strategy

A **negative auxiliary verb** hosts the inflection its lexical verb
loses (Finnish *ei mene* 'NEG.3SG go'), making negation a special case of
the aux-headed auxiliary-verb construction; an affix or a particle does
not. `Strategy` classifies negation at that grain. -/

open AuxiliaryVerbs (InflectionPattern)

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
def Strategy.expectedInflectionPattern : Strategy → Option InflectionPattern
  | .negVerb => some .auxHeaded
  | .negAffix | .negParticle => none

/-- The strategy is verbal: its negator is itself a verb. -/
def Strategy.IsVerbal : Strategy → Prop
  | .negVerb => True
  | .negAffix | .negParticle => False

instance : DecidablePred Strategy.IsVerbal
  | .negVerb => isTrue trivial
  | .negAffix | .negParticle => isFalse id

/-- The strategy's negative morpheme in the WALS Ch 112A
classification. -/
def Strategy.morphemeType : Strategy → Data.WALS.F112A.NegativeMorphemeType
  | .negVerb => .negativeAuxiliaryVerb
  | .negAffix => .negativeAffix
  | .negParticle => .negativeParticle

/-- The verbal strategy is the one whose morpheme [miestamo-2005] types as a negative
auxiliary verb. -/
theorem isVerbal_iff_morphemeType_auxVerb (s : Strategy) :
    s.IsVerbal ↔ s.morphemeType = .negativeAuxiliaryVerb := by
  cases s <;> decide

end Negation
