import Linglib.Semantics.Polarity.Licensing

/-!
# Korean polarity items

Korean builds its indefinites on the interrogative pronouns, as Japanese does: bare *nwukwu*
'who' is an indefinite in questions and conditionals; *nwukwu-to*, with the additive particle
*-to*, is the negative indefinite of *nwukwu-to an wass-ta* 'nobody came', which needs
clausemate negation, the counterpart of Japanese *dare-mo*; and *nwukwu-na*, whose *-na* is
the adversative mood of the copula and also means 'or', is the free-choice item of
*nwukwu-na hal su issta* 'anyone can do it'.

## Main results

* `Korean.PolarityItems.nwukwuTo_licensing_characterized`,
  `Korean.PolarityItems.korean_licensing_sound` — the predicted and attested licensing
  environments of the items agree

## References

* [haspelmath-1997]
-/

namespace Korean.PolarityItems

open Polarity

/-- Bare *nwukwu* 'who', an indefinite in questions and conditionals. -/
def nwukwu : Item :=
  { form := "nwukwu (누구)"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.question, .conditionalAntecedent]
  , scalarDirection := some .strengthening }

/-- *nwukwu-to* 'nobody' under clausemate negation, the interrogative with the additive
particle. -/
def nwukwuTo : Item :=
  { form := "nwukwu-to (누구도, neg)"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening
  , morphology := .indefPlusEven }

/-- *nwukwu-na* 'anyone', the free-choice item; *-na* is not an additive particle, so the
morphology is plain. -/
def nwukwuNa : Item :=
  { form := "nwukwu-na (누구나)"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic] }

/-- *Nwukwu-to* needs an anti-morphic licensor, and clausal negation is the only such
environment: predicted and attested distributions coincide. -/
theorem nwukwuTo_licensing_characterized :
    ∀ c, c.licenses nwukwuTo ↔ c ∈ nwukwuTo.licensingContexts := by decide

/-- Every attested environment of every item is predicted licensed. -/
theorem korean_licensing_sound :
    ∀ e ∈ [nwukwu, nwukwuTo, nwukwuNa], ∀ c ∈ e.licensingContexts,
      c.licenses e := by decide

end Korean.PolarityItems
