import Linglib.Semantics.Polarity.Licensing

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

The strict-NC *ни-* series carries `licensor := some .antiMorphic`:
clausemate *не* is the only anti-morphic environment, so strict concord is
characterized exactly by the licensing keystone
(`niSeries_licensing_characterized`).
-/

namespace Russian.PolarityItems

open Semantics.Polarity

/-! ### Weak NPI (the *-либо* series) -/

/-- *кто-либо* (kto-libo) — weak NPI. The *-либо* series is licensed across
    the DE functions of [haspelmath-1997]'s map: questions, conditionals,
    comparatives, and indirect (non-clausemate) negation — distinct from the
    direct-negation *ни-* series below. -/
def ktoLibo : Item :=
  { form := "кто-либо (kto-libo)"
  , licensor := some .weak
  , baseForce := .existential
  , licensingContexts := [.question, .conditionalAntecedent, .negation, .comparativeS]
  , scalarDirection := .strengthening }

/-! ### Strict-NC *ни-* words (the direct-negation series) -/

/-- *никто* (nikto) — strict-NC n-word ('nobody'). Direct-negation series;
    requires clausemate negation: 'nikto ne prišël' (nobody NEG came). -/
def nikto : Item :=
  { form := "никто (nikto)"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg }

/-- *ничего* (nichego) — non-human strict-NC n-word ('nothing').
    'Ničego ne videl' = '(I) saw nothing'. -/
def nichego : Item :=
  { form := "ничего (nichego)"
  , licensor := some .antiMorphic
  , baseForce := .existential
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg }

/-- *никогда* (nikogda) — temporal strict-NC n-word ('never').
    'Nikogda ne prixodil' = '(He) never came'. -/
def nikogda : Item :=
  { form := "никогда (nikogda)"
  , licensor := some .antiMorphic
  , baseForce := .temporal
  , licensingContexts := [.negation]
  , scalarDirection := .strengthening
  , morphology := .indefPlusNeg }

/-! ### Free choice item -/

/-- *кто угодно* (kto ugodno) — free choice item.
    Universal-like: 'anyone at all'. -/
def ktoUgodno : Item :=
  { form := "кто угодно (kto ugodno)"
  , freeChoice := true
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic] }

/-! ### Inventory -/

/-- The Russian polarity-item inventory: the Fragment-side joint listing
    every polarity item this fragment defines. -/
def items : List Item :=
  [ktoLibo, nikto, nichego, nikogda, ktoUgodno]

/-! ### Verification -/

/-- The strict-NC *ни-* series characterized exactly: clausemate *не* is
    the only licensing environment. -/
theorem niSeries_licensing_characterized :
    ∀ e ∈ [nikto, nichego, nikogda], ∀ c,
      c.licenses e ↔ c ∈ e.licensingContexts := by decide

/-- Every attested context of every entry is predicted licensed. -/
theorem russian_licensing_sound :
    ∀ e ∈ items, ∀ c ∈ e.licensingContexts, c.licenses e := by decide

/-- Every NPI in the inventory is scalar-strengthening. The free-choice
    `kto ugodno` is correctly excluded by the substrate `isNPI` guard rather
    than dropped from a hand-listed sublist. -/
theorem npis_strengthening :
    ∀ e ∈ items, e.isNPI → e.scalarDirection = .strengthening := by
  decide

end Russian.PolarityItems
