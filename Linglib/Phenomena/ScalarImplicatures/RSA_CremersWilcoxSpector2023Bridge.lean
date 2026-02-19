import Linglib.Phenomena.ScalarImplicatures.Studies.CremersWilcoxSpector2023

/-!
# Bridge: Cremers, Wilcox & Spector (2023) RSA Models → Scalar Implicature Phenomena

RSA models for exhaustivity and anti-exhaustivity. Baseline RSA predicts anti-exhaustivity
under biased priors, which contradicts human behavior. EXH-LU blocks this via exhaustification.

The model depends on `CWSConfig`, `CWSWorld`, `CWSUtterance`, etc. from
`Phenomena.ScalarImplicatures.Studies.CremersWilcoxSpector2023`, so the full
implementation lives here as a bridge file.

## Status

RSA evaluation infrastructure (basicL1, L1_world, getScore, normalize, boolToRat)
has been removed. Domain types, meaning functions (parseMeaning, lexiconMeaning,
exhLUMeaning, wonkyGoalProject), and structural definitions are preserved.
RSA computation stubs and prediction theorems remain with `sorry` for future
reimplementation.

## References

Cremers, A., Wilcox, E., & Spector, B. (2023). Exhaustivity and Anti-Exhaustivity
in the RSA Framework. Semantics & Pragmatics.
-/

namespace RSA.Implementations.CremersWilcoxSpector2023

open Phenomena.ScalarImplicatures.Studies.CremersWilcoxSpector2023


/-- Meaning with parse-dependent exhaustification.

    - literal parse: use literal semantics
    - exh parse: use exhaustified semantics (EXH(A) = A ∧ ¬B) -/
def parseMeaning : CWSParse → CWSWorld → CWSUtterance → Bool
  | .literal, w, u => literalTruth w u
  | .exh, w, u => exhMeaning w u

/-- BwRSA goal projection: how goals partition worlds.

    - informative: Full partition (distinguish all worlds)
    - wonky: Trivial partition (all worlds equivalent, speaker doesn't care) -/
def wonkyGoalProject : WonkyGoal → CWSWorld → CWSWorld → Bool
  | .informative, w1, w2 => w1 == w2  -- Standard: distinguish worlds
  | .wonky, _, _ => true              -- Wonky: all worlds equivalent


/-- Verify utterance count -/
theorem utterance_count : allUtterances.length = 3 := rfl

/-- Verify world count -/
theorem world_count : allWorlds.length = 2 := rfl

/-- Verify parse count -/
theorem parse_count : allParses.length = 2 := rfl

/-- Verify lexica count -/
theorem lexica_count : allLexica.length = 4 := rfl

/-- Verify wonky goals count -/
theorem wonky_goals_count : allWonkyGoals.length = 2 := rfl


/-- EXH meaning is only true in w_a.

    EXH blocks anti-exhaustivity because EXH(A) = A ∧ ¬B is false in w_ab. -/
theorem exh_meaning_blocks_wab :
    exhMeaning .w_ab .A = false := by rfl

end RSA.Implementations.CremersWilcoxSpector2023
