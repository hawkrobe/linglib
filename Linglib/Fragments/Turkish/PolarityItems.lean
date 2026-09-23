module

public import Linglib.Semantics.Polarity.Licensing

/-!
# Turkish Polarity-Sensitive Items
[haspelmath-1997]

Turkish indefinite pronoun polarity items, typed by the categories from
`Polarity`.

- **kimse**: Weak NPI (questions, conditionals, indirect negation)
- **hiç kimse**: Emphatic negative indefinite (direct negation)
- **herhangi biri**: Free choice item
-/

@[expose] public section

namespace Turkish.PolarityItems

open PolarityItem

/-! ### NPIs -/

/-- *kimse* — Weak NPI.
    Historically 'person'; now polarity-sensitive in questions,
    conditionals, and indirect negation. -/
def kimse : PolarityItem :=
  { form := "kimse"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.question, .conditionalAntecedent, .negation]
  , scalarDirection := some .strengthening }

/-- *hiç kimse* — Emphatic negative indefinite.
    *hiç* intensifier + *kimse*; direct negation only. -/
def hicKimse : PolarityItem :=
  { form := "hiç kimse"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := some .strengthening }

/-! ### FCI -/

/-- *herhangi biri* — Free choice item.
    'Any person at all'. -/
def herhangiBiri : PolarityItem :=
  { form := "herhangi biri"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic] }

/-! ### Verification -/

theorem turkish_npis_strengthening :
    [kimse, hicKimse].all
      (λ e => e.scalarDirection == some .strengthening) = true := by decide

/-- *hiç kimse* characterized exactly: obligatory co-occurrence with verbal
    negation ([haspelmath-1997] A179). -/
theorem hicKimse_licensing_characterized :
    ∀ c, c.licenses hicKimse ↔ c ∈ hicKimse.licensingContexts := by decide

theorem turkish_licensing_sound :
    ∀ e ∈ [kimse, hicKimse, herhangiBiri], ∀ c ∈ e.licensingContexts,
      c.licenses e := by decide

end Turkish.PolarityItems
