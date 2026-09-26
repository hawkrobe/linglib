module

public import Linglib.Semantics.Polarity.Licensing

/-!
# Czech polarity items

Czech indefinites come in two polarity-sensitive series, typed by `PolarityItem`. The
*ni-* series (*nikdo*, *nic*, *nikdy*, *nikam*) and the determiner *žádný* are negative concord
items: "any negative subject or object pronoun or pronoun-adverb is reinforced by ne- in the
verb", as in *Nikdo to nekoupil* 'No one bought it' and *Petr nekoupil nic* 'Peter didn't buy
anything' ([short-1993-czech], p. 511), so that the concord holds whether the item precedes the
verb or follows it. The *ně-* series (*někdo*, the determiner *nějaký*), built on the prefix
*ně-* ([haspelmath-1997]), are positive polarity items, which escape the immediate scope of
clausemate negation; the two determiners therefore diagnose the position of negation in polar
questions ([stankova-2025], [stankova-2026]). The *ne-* prefix lives in the sibling
`Negation.lean`.

## References

* [short-1993-czech]
* [haspelmath-1997]
* [stankova-2025]
* [stankova-2026]
-/

@[expose] public section

namespace Czech.PolarityItems

open PolarityItem

/-! ### The *ni-* series -/

/-- *nikdo* 'nobody', the human concord item. -/
def nikdo : PolarityItem :=
  { form := "nikdo"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .indefPlusNeg }

/-- *nic* 'nothing', the non-human concord item. -/
def nic : PolarityItem :=
  { form := "nic"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .indefPlusNeg }

/-- *nikdy* 'never', the temporal concord item. -/
def nikdy : PolarityItem :=
  { form := "nikdy"
  , licensor := some .antiMorphic
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .indefPlusNeg }

/-- *nikam* 'nowhere (to)', the directional concord item. -/
def nikam : PolarityItem :=
  { form := "nikam"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .indefPlusNeg }

/-- *žádný* 'no', the determiner concord item, licensed by inner negation alone in polar
    questions ([stankova-2026]). -/
def zadny : PolarityItem :=
  { form := "žádný"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening }

/-- The strict concord items. -/
def niSeries : List PolarityItem := [nikdo, nic, nikdy, nikam, zadny]

/-! ### The *ně-* series -/

/-- *nějaký* 'some', the determiner positive polarity item, admitted by outer and medial
    negation in polar questions ([stankova-2025], [stankova-2026]). -/
def nejaky : PolarityItem :=
  { form := "nějaký"
  , ppi := true
  , baseForce := .existential
  , licensingContexts := [] }

/-- *někdo* 'someone', the human positive polarity item, which replaces *nikdo* under the
    non-propositional negation of a fear-predicate complement ([stankova-2025]). -/
def nekdo : PolarityItem :=
  { form := "někdo"
  , ppi := true
  , baseForce := .existential
  , licensingContexts := [] }

/-- The positive polarity items. -/
def neSeries : List PolarityItem := [nejaky, nekdo]

/-! ### Verification -/

/-- Strict concord: clausemate negation is the only context licensing a *ni-* item. -/
theorem niSeries_strict_concord :
    ∀ e ∈ niSeries, ∀ c : LicensingContext, c.licenses e ↔ c = .negation := by decide

/-- The *ni-* pronouns are morphologically indefinite plus negation. -/
theorem niSeries_morphology : ∀ e ∈ [nikdo, nic, nikdy, nikam], e.morphology = .indefPlusNeg := by
  decide

/-- The *ně-* items are positive polarity items, licensed by no context. -/
theorem neSeries_ppi : ∀ e ∈ neSeries, e.isPPI ∧ ∀ c : LicensingContext, ¬ c.licenses e := by
  decide

end Czech.PolarityItems
