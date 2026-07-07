import Linglib.Semantics.Polarity.Item

/-!
# Korean Polarity-Sensitive Items
[haspelmath-1997]

Korean indefinite pronoun polarity items, typed by the categories from
`Semantics.Polarity`.

Korean, like Japanese, builds polarity items from wh-words + particles:
- **nwukwu** (bare): Weak NPI in non-interrogative uses
- **nwukwu-to** (with clausemate negation): wh + to → 'nobody'
- **nwukwu-na**: wh + na → FCI (anyone)
-/

namespace Korean.PolarityItems

open Semantics.Polarity

/-! ### NPIs -/

/-- *nwukwu* (누구, bare) — Weak NPI.
    Bare wh-word as indefinite in non-interrogative non-specific contexts
    (conditionals, irrealis). -/
def nwukwu : PolarityItemEntry :=
  { form := "nwukwu (누구)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.question, .conditionalAntecedent]
  , scalarDirection := .strengthening }

/-- *nwukwu-to* (누구도, with clausemate negation) — n-word: *nwukwu-to an
    wass-ta* 'nobody came'. wh + the additive/'even' particle *-to*, requiring
    clausemate negation — the strict-negative-concord parallel of Japanese
    *dare-mo* (see `Japanese.PolarityItems.dareMo`). -/
def nwukwuTo : PolarityItemEntry :=
  { form := "nwukwu-to (누구도, neg)"
  , polarityType := .npiStrong
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , morphology := .indefPlusEven
  , nWordStatus := some .nWord }

/-! ### FCI -/

/-- *nwukwu-na* (누구나) — Free choice item.
    wh + na: 'nwukwu-na hal su issda' (anyone can do it). -/
def nwukwuNa : PolarityItemEntry :=
  { form := "nwukwu-na (누구나)"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic]
  , morphology := .indefPlusEven }

/-! ### Verification -/

theorem korean_npis_strengthening :
    [nwukwu, nwukwuTo].all
      (λ e => e.scalarDirection == .strengthening) = true := by decide

end Korean.PolarityItems
