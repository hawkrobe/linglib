import Linglib.Fragments.English.PolarityItems

/-!
# Quechua (Imbabura) Polarity-Sensitive Items
@cite{haspelmath-1997}

Quechua indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

- **pi-pash**: Weak NPI (wh + pash in conditional/neg scope)
- **mana pi-pash**: Negative indefinite (negation + wh + pash)
- **maijan-pash**: Free choice item

Properties beyond the @cite{haspelmath-1997} function data (scalar direction,
domain alternatives, modal rescue) use conservative defaults. -- UNVERIFIED
-/

namespace Fragments.Quechua.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPIs
-- ============================================================================

/-- *pi-pash* — Weak NPI.
    wh + pash: used in conditional and indirect negation contexts. -/
def piPash : PolarityItemEntry :=
  { form := "pi-pash"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.conditional_ant, .negation]
  , scalarDirection := .strengthening  -- UNVERIFIED: conservative default
  , notes := "wh + pash: conditional/neg scope" }

/-- *mana pi-pash* — Negative indefinite.
    negation + wh + pash: nobody. -/
def manaPiPash : PolarityItemEntry :=
  { form := "mana pi-pash"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening  -- UNVERIFIED: conservative default
  , notes := "Negation + wh + pash: nobody" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *maijan-pash* — Free choice item.
    'Anyone': free choice use. -/
def maijanPash : PolarityItemEntry :=
  { form := "maijan-pash"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative, .generic]
  , obligatoryDomainAlts := true  -- UNVERIFIED: conservative default
  , modalRescue := true  -- UNVERIFIED: conservative default
  , notes := "Free choice: anyone" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem quechua_npis_strengthening :
    [piPash, manaPiPash].all
      (λ e => e.scalarDirection == .strengthening) = true := by native_decide

theorem maijanPash_obligatory_domain_alts :
    maijanPash.obligatoryDomainAlts = true := rfl

end Fragments.Quechua.PolarityItems
