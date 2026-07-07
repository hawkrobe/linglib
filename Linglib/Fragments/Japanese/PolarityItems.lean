import Linglib.Semantics.Polarity.Licensing

/-!
# Japanese Polarity-Sensitive Items
[haspelmath-1997] [kratzer-shimoyama-2002] [shimoyama-2011] [watanabe-2004]

Japanese indefinite pronoun polarity items, typed by the categories from
`Semantics.Polarity`.

Japanese builds polarity items from wh-indeterminates + particles
([kratzer-shimoyama-2002]):
- **dare-mo** (with clausemate negation): wh + mo → 'nobody'
- **dare-demo**: wh + demo → FCI (anyone/whoever)
-/

namespace Japanese.PolarityItems

open Semantics.Polarity

/-! ### NPI -/

/-- *dare-mo* (with clausemate negation) — n-word: *dare-mo ko-nakat-ta*
    'nobody came'. Requires clausemate sentential negation and is
    ungrammatical in weak-DE contexts like questions and conditionals, which
    take *dare-ka* or bare indeterminates instead ([shimoyama-2011]);
    [watanabe-2004] analyzes it as a negative-concord item.

    `baseForce` follows the Hamblin-universal analysis of *-mo*
    ([shimoyama-2006], [kratzer-shimoyama-2002]; so also
    `Japanese.Determiners.dare_mo`), on which *dare-mo…nai* is ∀ scoping over
    negation; the rival negative-indefinite tradition posits ¬∃
    (truth-conditionally equivalent under plain clausemate negation, teased
    apart by the scope diagnostics of [shimoyama-2011]). The affirmative
    *dare-mo* 'everyone' is the same wh + mo formation without negation. -/
def dareMo : Item :=
  { form := "dare-mo (誰も, neg)"
  , licensor := some .antiMorphic
  , baseForce := .universal
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , morphology := .indefPlusEven
  , alternativeType := .domain }

/-! ### FCI -/

/-- *dare-demo* — free choice item: *dare-demo dekiru* 'anyone can do it'.
    wh + demo (built on the additive/'even' particle *mo*); free choice and
    concessive-conditional uses ([kratzer-shimoyama-2002]). -/
def dareDemo : Item :=
  { form := "dare-demo (誰でも)"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic]
  , morphology := .indefPlusEven
  , alternativeType := .domain }

/-! ### Verification -/

/-- The licensing keystone characterizes *dare-mo* exactly: as an n-word it
    requires an anti-morphic licensor, and clausal negation is the only such
    row — predicted distribution and attested list coincide. -/
theorem dareMo_licensing_characterized :
    ∀ c, c.licenses dareMo ↔ c ∈ dareMo.licensingContexts := by decide

/-- Every attested *dare-demo* context is predicted licensed: all four rows
    license free choice items. -/
theorem dareDemo_licensing_sound :
    ∀ c ∈ dareDemo.licensingContexts, c.licenses dareDemo := by decide

/-- Complementary distribution: the n-word and the FCI are licensed in
    disjoint context sets (clausemate negation vs modal/imperative/generic). -/
theorem dareMo_dareDemo_licensing_disjoint :
    ∀ c ∈ dareMo.licensingContexts, c ∉ dareDemo.licensingContexts := by decide

end Japanese.PolarityItems
