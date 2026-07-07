import Linglib.Semantics.Polarity.Licensing

/-!
# Mandarin Polarity-Sensitive Items
[haspelmath-1997]

Mandarin indefinite pronoun polarity items, typed by the categories from
`Semantics.Polarity`.

Mandarin wh-words (*shéi* 谁, *shénme* 什么) double as indefinites in
non-interrogative uses, covering an exceptionally wide range on
[haspelmath-1997]'s map (7 of 9 functions):
- **shéi** (non-interrogative): NPI/FCI — questions through free choice
-/

namespace Mandarin.PolarityItems

open Semantics.Polarity

/-! ### NPI/FCI -/

/-- *shéi* (谁, non-interrogative) — NPI/FCI.
    Wh-word as indefinite covers 7 Haspelmath functions: irrealis through
    free choice. Functions as both NPI (under negation, in questions) and
    FCI (in modal/generic contexts). -/
def shei : Item :=
  { form := "shéi (谁, non-interrog.)"
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [ .negation, .nobody, .question, .conditionalAntecedent
      , .modalPossibility, .modalNecessity, .imperative, .generic
      , .comparativeS ]
  , scalarDirection := .strengthening }

/-! ### Verification -/

/-- Every attested context is predicted licensed. -/
theorem shei_licensing_sound :
    ∀ c ∈ shei.licensingContexts, c.licenses shei := by decide

end Mandarin.PolarityItems
