module

public import Linglib.Semantics.Polarity.Licensing
public import Linglib.Fragments.Japanese.Indefinites

/-!
# Japanese polarity items

The polarity items among the Japanese indefinites, typed by `PolarityItem`: *dare-mo* with
clausemate negation, a negative-concord item, and the free-choice *dare-demo*
([kratzer-shimoyama-2002]). Their forms are those of the series of `Japanese.Indefinites`.

## References

* [haspelmath-1997]
* [kratzer-shimoyama-2002]
* [shimoyama-2006]
* [shimoyama-2011]
* [watanabe-2004]
-/

@[expose] public section

namespace Japanese.PolarityItems

open PolarityItem

/-! ### NPI -/

/-- *dare-mo* (with clausemate negation) — n-word: *dare-mo ko-nakat-ta*
    'nobody came'. Requires clausemate sentential negation and is
    ungrammatical in weak-DE contexts like questions and conditionals, which
    take *dare-ka* or bare indeterminates instead ([shimoyama-2011]);
    [watanabe-2004] analyzes it as a negative-concord item.

    On the Hamblin-universal analysis of *-mo* ([shimoyama-2006],
    [kratzer-shimoyama-2002]; so also `Japanese.Determiners.dare_mo`)
    *dare-mo…nai* is ∀ scoping over negation; the rival negative-indefinite
    tradition posits ¬∃
    (truth-conditionally equivalent under plain clausemate negation, teased
    apart by the scope diagnostics of [shimoyama-2011]). The affirmative
    *dare-mo* 'everyone' is the same wh + mo formation without negation. -/
def dareMo : PolarityItem :=
  { form := Indefinites.dareMo.form
  , licensor := some .antiMorphic
  , licensingContexts := [.negation] }

/-! ### FCI -/

/-- *dare-demo* — free choice item: *dare-demo dekiru* 'anyone can do it'.
    wh + demo (built on the additive/'even' particle *mo*); free choice and
    concessive-conditional uses ([kratzer-shimoyama-2002]). -/
def dareDemo : PolarityItem :=
  { form := Indefinites.dareDemo.form
  , freeChoice := true
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic] }

/-! ### Licensing -/

/-- *Dare-mo* needs clausemate negation, so it is licensed exactly by the contexts carrying
anti-morphic strength, which among the named contexts is clausal negation alone. -/
theorem dareMo_licensing_characterized (c : LicensingContext) :
    c.Licenses dareMo ↔ c.licenser.Carries .antiMorphic :=
  LicensingContext.licenses_iff_carries rfl (by decide) (by decide)

/-- Every attested *dare-demo* context admits it: all four are generic contexts. -/
theorem dareDemo_licensing_sound :
    ∀ c ∈ dareDemo.licensingContexts, c.Admits dareDemo := by
  simp only [dareDemo, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  and_intros <;> decide

/-- The n-word and the free choice item are attested in disjoint contexts, clausemate negation
against the modal, imperative and generic ones. -/
theorem dareMo_dareDemo_licensing_disjoint :
    ∀ c ∈ dareMo.licensingContexts, c ∉ dareDemo.licensingContexts := by
  simp only [dareMo, dareDemo, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  rintro (h | h | h | h) <;> exact LicensingContext.ne_of_haspelmath_ne (by decide) h

end Japanese.PolarityItems
