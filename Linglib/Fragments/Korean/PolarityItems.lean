import Linglib.Fragments.English.PolarityItems

/-!
# Korean Polarity-Sensitive Items
@cite{haspelmath-1997}

Korean indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

Korean, like Japanese, builds polarity items from wh-words + particles:
- **nwukwu** (bare): Weak NPI in non-interrogative uses
- **nwukwu-to** (neg): wh + to under negation → NPI (nobody)
- **nwukwu-na**: wh + na → FCI (anyone)
-/

namespace Fragments.Korean.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPIs
-- ============================================================================

/-- *nwukwu* (누구, bare) — Weak NPI.
    Bare wh-word as indefinite in non-interrogative non-specific contexts
    (conditionals, irrealis). -/
def nwukwu : PolarityItemEntry :=
  { form := "nwukwu (누구)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.question, .conditional_ant]
  , scalarDirection := .strengthening
  , notes := "Bare wh-word as non-specific indefinite" }

/-- *nwukwu-to* (누구도, under negation) — N-word.
    wh + to under negation: 'nwukwu-to an wass-ta' (nobody came). -/
def nwukwuTo : PolarityItemEntry :=
  { form := "nwukwu-to (누구도, neg)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening
  , notes := "wh + to under negation: nobody" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *nwukwu-na* (누구나) — Free choice item.
    wh + na: 'nwukwu-na hal su issda' (anyone can do it). -/
def nwukwuNa : PolarityItemEntry :=
  { form := "nwukwu-na (누구나)"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative, .generic]
  , obligatoryDomainAlts := true
  , modalRescue := true
  , notes := "wh + na: free choice / universal" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem korean_npis_strengthening :
    [nwukwu, nwukwuTo].all
      (λ e => e.scalarDirection == .strengthening) = true := by native_decide

theorem nwukwuNa_obligatory_domain_alts :
    nwukwuNa.obligatoryDomainAlts = true := rfl

end Fragments.Korean.PolarityItems
