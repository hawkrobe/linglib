import Linglib.Semantics.Polarity.Licensing
import Linglib.Fragments.German.TemporalConnectives

/-!
# German Polarity-Sensitive Items
[haspelmath-1997] [chierchia-2006] [karttunen-1974]

German *irgendein*, [chierchia-2006]'s existential FCI (EFCI): NPI uses in
questions and conditionals, FCI uses under modals, with the *irgend-*
prefix marking domain widening. The negative quantifier *niemand* negates
rather than being licensed, and bare *wer* is a plain colloquial
indefinite ([haspelmath-1997] A.1) — neither is a polarity item, so
neither has an entry here. *erst* 'only then' is the positive polarity
punctual *until*, the twin of Finnish *vasta* ([karttunen-1974]).
-/

namespace German.PolarityItems

open Polarity

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
  , scalarDirection := some .strengthening }

/-! ### PPI -/

/-- *erst* 'only then', the punctual *until* of a positive clause ([karttunen-1974], the paper's
(38)). Its connective entry is `German.TemporalConnectives.erst`. -/
def erst : Item :=
  { form := TemporalConnectives.erst.form
  , ppi := true
  , baseForce := .temporal
  , licensingContexts := [] }

/-! ### Verification -/

/-- Every attested context is predicted licensed. -/
theorem irgendein_licensing_sound :
    ∀ c ∈ irgendein.licensingContexts, c.licenses irgendein := by decide

end German.PolarityItems
