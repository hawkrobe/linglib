import Linglib.Semantics.Polarity.Item

/-!
# Russian Polarity-Sensitive Items
[haspelmath-1997] [zeijlstra-2004] [giannakidou-1998]

Russian indefinite-pronoun polarity items, typed by the theory-neutral
categories from `Semantics.Polarity`. The classification follows
[haspelmath-1997]'s implicational map for the Russian series: the
*-либо* series spans the weak-NPI functions (irrealis non-specific,
question, conditional, comparative, indirect negation), while the *ни-*
series occupies the *direct negation* function as strict negative-concord
items, obligatorily co-occurring with clausemate verbal negation *не*.

- **кто-либо** (kto-libo): weak NPI — questions, conditionals,
  comparatives, indirect negation.
- **никто / ничего / никогда** (nikto / nichego / nikogda): strict-NC
  *ни-* words, obligatory clausemate *не* ([zeijlstra-2004],
  [giannakidou-1998]).
- **кто угодно** (kto ugodno): free-choice item.

The substrate has no dedicated n-word/negative-concord `PolarityType` case
(negative concord is a planned extension), so the strict-NC *ни-* series is
approximated as `.npiStrong` (anti-additive licensing) — the same choice the
Czech sibling fragment makes for its cognate *ni-* series.
-/

namespace Russian.PolarityItems

open Semantics.Polarity

/-! ### Weak NPI (the *-либо* series) -/

/-- *кто-либо* (kto-libo) — weak NPI. The *-либо* series is licensed across
    the DE functions of [haspelmath-1997]'s map: questions, conditionals,
    comparatives, and indirect (non-clausemate) negation — distinct from the
    direct-negation *ни-* series below. -/
def ktoLibo : PolarityItemEntry :=
  { form := "кто-либо (kto-libo)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.question, .conditionalAntecedent, .negation, .comparativeS]
  , scalarDirection := .strengthening
  , notes := "Polarity-sensitive indefinite; spans the weak-NPI functions" }

/-! ### Strict-NC *ни-* words (the direct-negation series) -/

/-- *никто* (nikto) — strict-NC n-word ('nobody'). Direct-negation series;
    requires clausemate negation: 'nikto ne prišël' (nobody NEG came). -/
def nikto : PolarityItemEntry :=
  { form := "никто (nikto)"
  , polarityType := .npiStrong
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg
  , nWordStatus := some .nWord
  , notes := "Strict-NC n-word; negative concord: 'nikto ne prišël'" }

/-- *ничего* (nichego) — non-human strict-NC n-word ('nothing').
    'Ničego ne videl' = '(I) saw nothing'. -/
def nichego : PolarityItemEntry :=
  { form := "ничего (nichego)"
  , polarityType := .npiStrong
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg
  , nWordStatus := some .nWord
  , notes := "Non-human n-word; genitive form ничего; co-occurs with не" }

/-- *никогда* (nikogda) — temporal strict-NC n-word ('never').
    'Nikogda ne prixodil' = '(He) never came'. -/
def nikogda : PolarityItemEntry :=
  { form := "никогда (nikogda)"
  , polarityType := .npiStrong
  , baseForce := .temporal
  , licensingContexts := [.negation, .nobody, .withoutClause]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg
  , nWordStatus := some .nWord
  , notes := "Temporal n-word; co-occurs with не" }

/-! ### Free choice item -/

/-- *кто угодно* (kto ugodno) — free choice item.
    Universal-like: 'anyone at all'. -/
def ktoUgodno : PolarityItemEntry :=
  { form := "кто угодно (kto ugodno)"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic]
  , notes := "Free choice: 'kto ugodno možet èto sdelat'' (anyone can do that)" }

/-! ### Inventory -/

/-- The Russian polarity-item inventory: the Fragment-side joint listing
    every polarity item this fragment defines. -/
def items : List PolarityItemEntry :=
  [ktoLibo, nikto, nichego, nikogda, ktoUgodno]

/-! ### Verification -/

/-- The strict-NC *ни-* word `nikto` and the free-choice `kto ugodno` have
    distinct polarity types. -/
theorem nikto_ktoUgodno_distinct :
    nikto.polarityType ≠ ktoUgodno.polarityType := by decide

/-- Every NPI in the inventory is scalar-strengthening. The free-choice
    `kto ugodno` is correctly excluded by the substrate `isNPI` guard rather
    than dropped from a hand-listed sublist. -/
theorem npis_strengthening :
    ∀ e ∈ items, e.isNPI → e.scalarDirection = .strengthening := by
  decide

/-- The strict-NC *ни-* series is classified as n-words via `nWordStatus`, no longer
    leaning on the strong-NPI `polarityType` slot: every `.npiStrong` entry in the
    inventory carries `some .nWord`. -/
theorem niSeries_are_nwords :
    ∀ e ∈ items, e.polarityType = .npiStrong → e.nWordStatus = some .nWord := by
  decide

end Russian.PolarityItems
