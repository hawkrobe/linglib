import Linglib.Fragments.English.PolarityItems

/-!
# Finnish Polarity-Sensitive Items
@cite{haspelmath-1997}

Finnish indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

Finnish has a differentiated system with dedicated NPI and FCI forms:
- **kukaan**: Weak NPI (questions, conditionals, indirect negation)
- **ei kukaan**: Negative indefinite (with negative verb *ei*)
- **kuka tahansa**: FCI ('whoever')
-/

namespace Fragments.Finnish.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPIs
-- ============================================================================

/-- *kukaan* — Weak NPI.
    Polarity-sensitive indefinite: questions, conditionals,
    indirect negation. -/
def kukaan : PolarityItemEntry :=
  { form := "kukaan"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.question, .conditional_ant, .negation]
  , scalarDirection := .strengthening
  , notes := "Polarity-sensitive indefinite" }

/-- *ei kukaan* — Negative indefinite.
    Negative verb *ei* + *kukaan*: 'ei kukaan tullut' (nobody came). -/
def eiKukaan : PolarityItemEntry :=
  { form := "ei kukaan"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening
  , notes := "Negative verb ei + kukaan: nobody" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *kuka tahansa* — Free choice item.
    'Whoever / anyone at all'. -/
def kukaTahansa : PolarityItemEntry :=
  { form := "kuka tahansa"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative, .generic]
  , obligatoryDomainAlts := true
  , modalRescue := true
  , notes := "Free choice: 'kuka tahansa voi tehdä sen' (anyone can do it)" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem finnish_npis_strengthening :
    [kukaan, eiKukaan].all
      (λ e => e.scalarDirection == .strengthening) = true := by native_decide

theorem kukaTahansa_obligatory_domain_alts :
    kukaTahansa.obligatoryDomainAlts = true := rfl

end Fragments.Finnish.PolarityItems
