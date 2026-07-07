import Linglib.Semantics.Polarity.Licensing

/-!
# German Polarity-Sensitive Items
[haspelmath-1997] [chierchia-2006]

German *irgendein*, [chierchia-2006]'s existential FCI (EFCI): NPI uses in
questions and conditionals, FCI uses under modals, with the *irgend-*
prefix marking domain widening. The negative quantifier *niemand* negates
rather than being licensed, and bare *wer* is a plain colloquial
indefinite ([haspelmath-1997] A.1) — neither is a polarity item, so
neither has an entry here.
-/

namespace German.PolarityItems

open Semantics.Polarity

/-- *irgendein/irgendwer* — [chierchia-2006]'s EFCI class: existential FCI
    with NPI uses (questions, conditionals) and FCI uses (modals,
    imperatives); *irgend-* marks domain widening. -/
def irgendein : Item :=
  { form := "irgendein/irgendwer"
  , licensor := some .weak
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts :=
      [.question, .conditionalAntecedent, .modalPossibility, .modalNecessity, .imperative]
  , scalarDirection := .strengthening }

/-! ### Verification -/

/-- Every attested context is predicted licensed. -/
theorem irgendein_licensing_sound :
    ∀ c ∈ irgendein.licensingContexts, c.licenses irgendein := by decide

end German.PolarityItems
