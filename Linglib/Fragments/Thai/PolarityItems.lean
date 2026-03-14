import Linglib.Fragments.English.PolarityItems

/-!
# Thai Polarity-Sensitive Items
@cite{haspelmath-1997}

Thai indefinite pronoun polarity items, typed by the categories from
`Fragments.English.PolarityItems`.

- **mâj mii khraj** (ไม่มีใคร): Negative indefinite (NEG + exist + wh)
- **khraj kɔ̂** (ใครก็): FCI (wh + kɔ̂ particle)

-/

namespace Fragments.Thai.PolarityItems

open Fragments.English.PolarityItems

-- ============================================================================
-- NPI
-- ============================================================================

/-- *mâj mii khraj* (ไม่มีใคร) — Negative indefinite.
    NEG + exist + wh: 'mâj mii khraj maa' (nobody came). -/
def majMiiKhraj : PolarityItemEntry :=
  { form := "mâj mii khraj (ไม่มีใคร)"
  , polarityType := .npiWeak
  , baseForce := .existential
  , licensingContexts := [.negation, .nobody]
  , notes := "NEG + exist + wh: nobody" }

-- ============================================================================
-- FCI
-- ============================================================================

/-- *khraj kɔ̂* (ใครก็) — Free choice item.
    wh + kɔ̂ particle: 'khraj kɔ̂ tham dâj' (anyone can do it). -/
def khrajKo : PolarityItemEntry :=
  { form := "khraj kɔ̂ (ใครก็)"
  , polarityType := .fci
  , baseForce := .existential
  , licensingContexts := [.modal_possibility, .modal_necessity, .imperative, .generic]
  , notes := "wh + kɔ̂ particle: free choice" }

-- ============================================================================
-- Verification
-- ============================================================================

theorem majMiiKhraj_khrajKo_distinct :
    majMiiKhraj.polarityType ≠ khrajKo.polarityType := by decide

end Fragments.Thai.PolarityItems
