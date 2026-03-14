import Linglib.Fragments.English.PolarityItems

/-!
# Japanese Polarity-Sensitive Items
@cite{haspelmath-1997}

Japanese indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

Japanese builds polarity items compositionally from wh-words + particles:
- **dare-mo** (neg): wh + mo under negation → NPI (nobody)
- **dare-demo**: wh + demo → FCI (anyone/whoever)
-/

namespace Fragments.Japanese.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPI
-- ============================================================================

/-- *dare-mo* (under negation) — N-word.
    wh + mo under negation: 'dare-mo konakatta' (nobody came). -/
def dareMo : PolarityItemEntry :=
  { form := "dare-mo (誰も, neg)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , scalarDirection := .strengthening
  , notes := "wh + mo under negation: nobody" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *dare-demo* — Free choice item.
    wh + demo: 'dare-demo dekiru' (anyone can do it). -/
def dareDemo : PolarityItemEntry :=
  { form := "dare-demo (誰でも)"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative, .generic]
  , obligatoryDomainAlts := true
  , modalRescue := true
  , notes := "wh + demo: free choice / concessive conditional" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem dareMo_dareDemo_distinct :
    dareMo.polarityType ≠ dareDemo.polarityType := by decide

theorem dareDemo_obligatory_domain_alts :
    dareDemo.obligatoryDomainAlts = true := rfl

end Fragments.Japanese.PolarityItems
