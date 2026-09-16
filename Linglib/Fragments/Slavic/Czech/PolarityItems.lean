import Linglib.Semantics.Polarity.Licensing

/-!
# Czech polarity items
[haspelmath-1997] [stankova-2025] [stankova-2026]

Czech indefinites come in two polarity-sensitive series, typed by `Polarity.Item`. The
*ni-* series (*nikdo*, *nic*, *nikdy*, *nikam*) and the determiner *žádný* are strict
negative concord items: every one obligatorily co-occurs with the *ne-* prefixed verb,
*Nikdo nepřišel* 'Nobody NEG.came', *Neviděl nikoho* 'NEG.saw nobody', regardless of
position, unlike the position-dependent concord of Italian or Spanish. The *ně-* series
(*někdo*, the determiner *nějaký*) are positive polarity items, which cannot be
interpreted in the immediate scope of clausemate negation; the two determiners therefore
diagnose the position of negation in polar questions ([stankova-2025],
[stankova-2026]). The *ne-* prefix itself lives in the sibling `Negation.lean`.
-/

namespace Czech.PolarityItems

open Polarity

/-! ### The *ni-* series -/

/-- *nikdo* 'nobody', the human concord item. -/
def nikdo : Item :=
  { form := "nikdo"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .indefPlusNeg }

/-- *nic* 'nothing', the non-human concord item. -/
def nic : Item :=
  { form := "nic"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .indefPlusNeg }

/-- *nikdy* 'never', the temporal concord item. -/
def nikdy : Item :=
  { form := "nikdy"
  , licensor := some .antiMorphic
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .indefPlusNeg }

/-- *nikam* 'nowhere', the directional concord item. -/
def nikam : Item :=
  { form := "nikam"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .indefPlusNeg }

/-- *žádný* 'no', the determiner concord item, licensed by inner negation alone in polar
    questions ([stankova-2026]). -/
def zadny : Item :=
  { form := "žádný"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening }

/-! ### The *ně-* series -/

/-- *nějaký* 'some', the determiner positive polarity item, admitted by outer and medial
    negation in polar questions ([stankova-2025], [stankova-2026]). -/
def nejaky : Item :=
  { form := "nějaký"
  , ppi := true
  , baseForce := .existential
  , licensingContexts := [] }

/-- *někdo* 'someone', the human positive polarity item, which replaces *nikdo* under
    the non-propositional negation of a fear-predicate complement ([stankova-2025]). -/
def nekdo : Item :=
  { form := "někdo"
  , ppi := true
  , baseForce := .existential
  , licensingContexts := [] }

/-- The Czech polarity items. -/
def items : List Item := [nikdo, nic, nikdy, nikam, zadny, nejaky, nekdo]

/-! ### Verification -/

/-- Clausemate negation is the only licensing environment of the *ni-* series, and nothing
    licenses the *ně-* series. -/
theorem items_licensing_characterized :
    ∀ e ∈ items, ∀ c, c.licenses e ↔ c ∈ e.licensingContexts := by decide

/-- The *ni-* series is morphologically indefinite plus negation. -/
theorem niSeries_morphology :
    ∀ e ∈ [nikdo, nic, nikdy, nikam], e.morphology = .indefPlusNeg := by decide

end Czech.PolarityItems
