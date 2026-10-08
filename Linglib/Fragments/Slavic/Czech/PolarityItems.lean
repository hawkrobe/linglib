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
  , licensingContexts := [.negation] }

/-- *nic* 'nothing', the non-human concord item. -/
def nic : PolarityItem :=
  { form := "nic"
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-- *nikdy* 'never', the temporal concord item. -/
def nikdy : PolarityItem :=
  { form := "nikdy"
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-- *nikam* 'nowhere (to)', the directional concord item. -/
def nikam : PolarityItem :=
  { form := "nikam"
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-- *žádný* 'no', the determiner concord item, licensed by inner negation alone in polar
    questions ([stankova-2026]). -/
def zadny : PolarityItem :=
  { form := "žádný"
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-- The strict concord items. -/
def niSeries : List PolarityItem := [nikdo, nic, nikdy, nikam, zadny]

/-! ### The *ně-* series -/

/-- *nějaký* 'some', the determiner positive polarity item, admitted by outer and medial
    negation in polar questions ([stankova-2025], [stankova-2026]). -/
def nejaky : PolarityItem :=
  { form := "nějaký"
  , antiLicensor := some .antiMorphic }

/-- *někdo* 'someone', the human positive polarity item, which replaces *nikdo* under the
    non-propositional negation of a fear-predicate complement ([stankova-2025]). -/
def nekdo : PolarityItem :=
  { form := "někdo"
  , antiLicensor := some .antiMorphic }

/-- The positive polarity items. -/
def neSeries : List PolarityItem := [nejaky, nekdo]

/-! ### Verification -/

/-- A *ni-* item is licensed exactly by the contexts carrying anti-morphic strength, clausal
negation alone among the named contexts: the strict concord of the series. -/
theorem niSeries_strict_concord :
    ∀ e ∈ niSeries, ∀ c : LicensingContext, c.Licenses e ↔ c.licenser.Carries .antiMorphic := by
  intro e he c
  simp only [niSeries, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
    exact LicensingContext.licenses_iff_carries rfl (by decide) (by decide)

/-- Clausemate negation blocks the *ně-* items. -/
theorem neSeries_antiLicensed : ∀ e ∈ neSeries, LicensingContext.negation.AntiLicenses e := by
  decide

end Czech.PolarityItems
