module

public import Linglib.Semantics.Polarity.Licensing

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

@[expose] public section

namespace Korean.PolarityItems

open PolarityItem

/-- Bare *nwukwu* 'who', an indefinite in questions and conditionals. -/
def nwukwu : PolarityItem :=
  { form := "nwukwu (누구)"
  , licensor := some .weak
  , licensingContexts := [.question, .conditionalAntecedent] }

/-- *nwukwu-to* 'nobody' under clausemate negation, the interrogative with the additive
particle. -/
def nwukwuTo : PolarityItem :=
  { form := "nwukwu-to (누구도, neg)"
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-- *nwukwu-na* 'anyone', the free-choice item; *-na* is not an additive particle. -/
def nwukwuNa : PolarityItem :=
  { form := "nwukwu-na (누구나)"
  , freeChoice := true
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic] }

/-- *Nwukwu-to* needs clausemate negation, so it is licensed exactly by the contexts carrying
anti-morphic strength, which among the named contexts is clausal negation alone. -/
theorem nwukwuTo_licensing_characterized (c : LicensingContext) :
    c.Licenses nwukwuTo ↔ c.licenser.Carries .antiMorphic :=
  LicensingContext.licenses_iff_carries rfl (by decide) (by decide)

/-- Every attested environment of every item admits it. -/
theorem korean_licensing_sound :
    ∀ e ∈ [nwukwu, nwukwuTo, nwukwuNa], ∀ c ∈ e.licensingContexts, c.Admits e := by
  simp only [nwukwu, nwukwuTo, nwukwuNa, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  and_intros <;> decide

end Korean.PolarityItems
