import Linglib.Semantics.Polarity.Item

/-!
# Finnish Polarity-Sensitive Items
[haspelmath-1997], [karlsson-2017]

Finnish indefinite pronoun polarity items, typed by the categories from
`Semantics.Polarity`.

Unlike Russian *nikto*, Italian *nessuno*, German *niemand*, or Hungarian
*senki* — all single-word negative quantifiers ("n-words") that have their own
sister-Fragment entries typed `.npiWeak` with `.negation, .nobody` licensing —
Finnish realizes "nobody" compositionally. *Kukaan* is the polarity-sensitive
indefinite (in [haspelmath-1997]'s terms, the *-kAArI*-series); *ei* is a
fully-conjugated negative auxiliary verb (en/et/ei/emme/ette/eivät) that takes
the connegative form of the lexical verb ([karlsson-2017] §19.5). The
direct-negation reading 'nobody came' is *ei kukaan tullut*, a syntactic
combination, not a single lexical entry.

- **kukaan**: Polarity-sensitive indefinite (questions, conditionals, negation)
- **kuka tahansa**: Free choice item ('whoever / anyone at all')
-/

namespace Finnish.PolarityItems

open Semantics.Polarity

-- ============================================================================
-- NPI
-- ============================================================================

/-- *kukaan* — Polarity-sensitive indefinite.
    Decomposes morphologically as *kuka* 'who' + *-kAAn* concessive clitic
    ([karlsson-2017] §25.6 on the *-kin* / *-kAAn* clitic pair); the
    *-kAAn*-series is [haspelmath-1997]'s A.27.1 Finnish series (i),
    parallel to Hindi *koii bhii* and Korean wh+*-do* / wh+*-na* — hence
    `morphology := .indefPlusEven`. In direct negation, co-occurs with the
    appropriate person/number form of the negation verb *ei*: 'ei kukaan
    tullut' (nobody came). -/
def kukaan : PolarityItemEntry :=
  { form := "kukaan"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.question, .conditionalAntecedent, .negation]
  , scalarDirection := .strengthening
  , morphology := .indefPlusEven
  , alternativeType := .domain
  , notes := "kuka 'who' + -kAAn concessive clitic; co-occurs with negation verb ei in direct negation (ei kukaan tullut 'nobody came')" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *kuka tahansa* — Free choice item.
    'Whoever / anyone at all'. One cell of a productive *X tahansa* paradigm
    over wh-words (also *mikä tahansa* 'whatever', *milloin tahansa* 'whenever',
    *missä tahansa* 'wherever'), with a literary *X hyvänsä* alternant.
    [haspelmath-1997] A.27 lists this as the *-hyvänsä*-series, used
    mainly in the free-choice function and predicted by his implicational map
    to extend to comparative. Not covered in [karlsson-2017]. -/
def kukaTahansa : PolarityItemEntry :=
  { form := "kuka tahansa"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic]
  , scalarDirection := .strengthening
  , notes := "Free choice: 'kuka tahansa voi tehdä sen' (anyone can do it); productive over wh-words (mikä/milloin/missä tahansa)" }

-- ============================================================================
-- Joint
-- ============================================================================

/-- All Finnish polarity-sensitive entries declared in this Fragment. -/
def items : List PolarityItemEntry := [kukaan, kukaTahansa]

-- ============================================================================
-- Verification
-- ============================================================================

theorem kukaan_kukaTahansa_distinct :
    kukaan.polarityType ≠ kukaTahansa.polarityType := by decide

end Finnish.PolarityItems
