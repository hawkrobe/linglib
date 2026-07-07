import Linglib.Semantics.Polarity.Licensing

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
def nwukwu : Item :=
  { form := "nwukwu (누구)"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.question, .conditionalAntecedent]
  , scalarDirection := .strengthening }

/-- *nwukwu-to* (누구도, with clausemate negation) — n-word: *nwukwu-to an
    wass-ta* 'nobody came'. wh + the additive/'even' particle *-to*, requiring
    clausemate negation — the strict-negative-concord parallel of Japanese
    *dare-mo* (see `Japanese.PolarityItems.dareMo`). -/
def nwukwuTo : Item :=
  { form := "nwukwu-to (누구도, neg)"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , morphology := .indefPlusEven }

/-! ### FCI -/

/-- *nwukwu-na* (누구나) — Free choice item.
    wh + na: 'nwukwu-na hal su issda' (anyone can do it). The suffix *-na*
    derives from the adversative mood of *i-* 'be' ('whoever it may be')
    and also means 'or' ([haspelmath-1997] A.39.2) — an 'it may be'-type
    source, not an additive/'even' particle, so `morphology` stays
    `.plain` (the enum lacks a disjunctive-source case). -/
def nwukwuNa : Item :=
  { form := "nwukwu-na (누구나)"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic] }

/-! ### Verification -/

/-- The licensing keystone characterizes *nwukwu-to* exactly: as an n-word it
    requires an anti-morphic licensor, and clausal negation is the only such
    row — predicted distribution and attested list coincide. -/
theorem nwukwuTo_licensing_characterized :
    ∀ c, c.licenses nwukwuTo ↔ c ∈ nwukwuTo.licensingContexts := by decide

/-- Every attested context of every Korean entry is predicted licensed. -/
theorem korean_licensing_sound :
    ∀ e ∈ [nwukwu, nwukwuTo, nwukwuNa], ∀ c ∈ e.licensingContexts,
      c.licenses e := by decide

theorem korean_npis_strengthening :
    [nwukwu, nwukwuTo].all
      (λ e => e.scalarDirection == .strengthening) = true := by decide

end Korean.PolarityItems
