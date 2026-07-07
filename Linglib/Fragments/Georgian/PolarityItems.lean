import Linglib.Semantics.Polarity.Licensing

/-!
# Georgian Polarity-Sensitive Items
[haspelmath-1997]

Georgian indefinite pronoun polarity items, typed by the categories from
`Semantics.Polarity`.

- **aravin** (არავინ): Negative indefinite (ara- NEG prefix + vin 'who')
- **nebismieri** (ნებისმიერი): Free choice item

Forms and basic distribution verified against Ch. 4 §2:
aravin is morphologically NEG + wh (not NEG + indefinite), and Georgian is a
non-strict negative concord language (verbal negation *ar* is optional with
preverbal neg-words). Mood-conditioned variants: vera-vin (modal), nura-vin
(prohibitive). nebismieri confirmed as FC indefinite in questions/modals.

-/

namespace Georgian.PolarityItems

open Semantics.Polarity

/-! ### NPI -/

/-- *aravin* (არავინ) — Negative indefinite.
    Morphologically ara- (NEG) + vin (who): 'aravin (ar) mosula' (nobody came).
    Non-strict negative concord: verbal negation *ar* is optional. -/
def aravin : Item :=
  { form := "aravin (არავინ)"
  , licensor := some .antiAdditive
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody] }

/-! ### FCI -/

/-- *nebismieri* (ნებისმიერი) — Free choice item.
    'Any / whichever': 'nebismier matarebels' (any train). -/
def nebismieri : Item :=
  { form := "nebismieri (ნებისმიერი)"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic] }

/-! ### Verification -/

/-- Every attested context of every entry is predicted licensed. -/
theorem georgian_licensing_sound :
    ∀ e ∈ [aravin, nebismieri], ∀ c ∈ e.licensingContexts, c.licenses e := by
  decide

end Georgian.PolarityItems
