import Linglib.Semantics.Polarity.Licensing

/-!
# Hungarian Polarity-Sensitive Items
[haspelmath-1997]

Hungarian indefinite pronoun polarity items, typed by the categories from
`Semantics.Polarity`.

- **senki**: N-word, negative concord (with *sem* in direct negation)
- **akárki / bárki**: Free choice items
-/

namespace Hungarian.PolarityItems

open Semantics.Polarity

/-! ### NPI -/

/-- *senki* — strict-NC n-word, direct negation only ([haspelmath-1997]
    A.26): co-occurs with *nem/sem*, 'senki sem jött' (nobody came). -/
def senki : Item :=
  { form := "senki"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening }

/-! ### FCI -/

/-- *akárki / bárki* — Free choice items.
    'Anyone at all': 'akárki megteheti' (anyone can do it). -/
def akarki : Item :=
  { form := "akárki / bárki"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic] }

/-! ### Verification -/

/-- Strict negative concord characterized exactly: *senki* is predicted
    licensed precisely under clausal negation. -/
theorem senki_licensing_characterized :
    ∀ c, c.licenses senki ↔ c ∈ senki.licensingContexts := by decide

theorem akarki_licensing_sound :
    ∀ c ∈ akarki.licensingContexts, c.licenses akarki := by decide

end Hungarian.PolarityItems
