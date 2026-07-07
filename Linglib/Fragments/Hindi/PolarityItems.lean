import Linglib.Semantics.Polarity.Licensing

/-!
# Hindi Polarity-Sensitive Items
[haspelmath-1997]

Hindi indefinite pronoun polarity items, typed by the categories from
`Semantics.Polarity`.

Hindi builds polarity items from the general indefinite *koii* + particles:
- **koii nahiiN**: koii + negation → NPI (nobody)
- **koii bhii**: koii + bhii (even/also) → FCI (anyone at all)
-/

namespace Hindi.PolarityItems

open Semantics.Polarity

/-! ### NPI -/

/-- *koii nahiiN* — Negative indefinite.
    koii + negation: 'koii nahiiN aayaa' (nobody came). -/
def koiiNahiin : Item :=
  { form := "koii nahiiN"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg
  , alternativeType := .contextualProperty }

/-! ### FCI -/

/-- *koii bhii* — Free choice item.
    koii + bhii (even/also): 'koii bhii yah kar saktaa hai'
    (anyone can do this). [lahiri-1998] -/
def koiiBhii : Item :=
  { form := "koii bhii"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic]
  , morphology := .indefPlusEven
  , alternativeType := .contextualProperty }

/-! ### Verification -/

/-- Every attested context of every entry is predicted licensed. -/
theorem hindi_licensing_sound :
    ∀ e ∈ [koiiNahiin, koiiBhii], ∀ c ∈ e.licensingContexts, c.licenses e := by
  decide

end Hindi.PolarityItems
