module

public import Linglib.Fragments.Slavic.Russian.Indefinites
public import Linglib.Semantics.Polarity.Licensing

/-!
# Russian polarity items

This file gives the Russian indefinite polarity items, typed by `PolarityItem`, the person row
taking its forms from `Russian.Indefinites`, after
[haspelmath-1997]'s map of the Russian series: the *-libo* series spans the functions of a weak
negative polarity item, questions, conditionals, comparatives and indirect negation; the *ni-*
series occupies direct negation as negative concord items, which co-occur with clausemate verbal
negation *ne* ([zeijlstra-2004], [giannakidou-1998]); and *kto ugodno* is a free-choice item.

The concord items carry `licensor := some .antiMorphic`, and clausemate *ne* being the only
anti-morphic environment, their licensing is characterized by it
(`niSeries_licensing_characterized`).

## References

* [haspelmath-1997]
* [zeijlstra-2004]
* [giannakidou-1998]
-/

@[expose] public section

namespace Russian.PolarityItems

open PolarityItem

/-! ### The *-libo* series -/

/-- *kto-libo* (кто-либо) 'anyone', a weak negative polarity item, licensed in questions,
conditionals, comparatives and under indirect negation. -/
def ktoLibo : PolarityItem :=
  { form := Indefinites.ktoLibo.form
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.question, .conditionalAntecedent, .negation, .clausalComparative]
  , scalarDirection := some .strengthening }

/-! ### The *ni-* series -/

/-- *nikto* (никто) 'nobody', a negative concord item that requires clausemate negation, *nikto
ne prišël* 'nobody came'. -/
def nikto : PolarityItem :=
  { form := Indefinites.nikto.form
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .indefPlusNeg }

/-- *ničego* (ничего) 'nothing', the non-human negative concord item, *ničego ne videl* '(he) saw
nothing'. -/
def nichego : PolarityItem :=
  { form := "ničego"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .indefPlusNeg }

/-- *nikogda* (никогда) 'never', the temporal negative concord item, *nikogda ne prixodil* '(he)
never came'. -/
def nikogda : PolarityItem :=
  { form := "nikogda"
  , licensor := some .antiMorphic
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .indefPlusNeg }

/-! ### Free choice -/

/-- *kto ugodno* (кто угодно) 'anyone at all', a free-choice item. -/
def ktoUgodno : PolarityItem :=
  { form := Indefinites.ktoUgodno.form
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic] }

/-! ### The entries -/

/-- The polarity items. -/
def items : List PolarityItem :=
  [ktoLibo, nikto, nichego, nikogda, ktoUgodno]

/-! ### Verification -/

/-- The negative concord items are licensed exactly in their attested contexts, clausemate
negation. -/
theorem niSeries_licensing_characterized :
    ∀ e ∈ [nikto, nichego, nikogda], ∀ c,
      c.licenses e ↔ c ∈ e.licensingContexts := by decide

/-- Every attested context of every entry is predicted licensed. -/
theorem russian_licensing_sound :
    ∀ e ∈ items, ∀ c ∈ e.licensingContexts, c.licenses e := by decide

/-- Every negative polarity item is scalar-strengthening. -/
theorem npis_strengthening :
    ∀ e ∈ items, e.isNPI → e.scalarDirection = some .strengthening := by
  decide

end Russian.PolarityItems
