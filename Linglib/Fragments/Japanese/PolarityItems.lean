import Linglib.Core.Lexical.PolarityItem

/-!
# Japanese Polarity-Sensitive Items
@cite{haspelmath-1997}

Japanese indefinite pronoun polarity items, typed by the categories from
`Core.Lexical.PolarityItem`.

Japanese builds polarity items compositionally from wh-words + particles:
- **dare-mo** (neg): wh + mo under negation → NPI (nobody)
- **dare-demo**: wh + demo → FCI (anyone/whoever)
-/

namespace Fragments.Japanese.PolarityItems

open Core.Lexical.PolarityItem

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
  , licensingContexts := [.modalPossibility, .modalNecessity, .imperative, .generic]
  , notes := "wh + demo: free choice / concessive conditional" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem dareMo_dareDemo_distinct :
    dareMo.polarityType ≠ dareDemo.polarityType := by decide

end Fragments.Japanese.PolarityItems
