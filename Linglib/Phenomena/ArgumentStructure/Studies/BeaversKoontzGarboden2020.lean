import Linglib.Theories.Semantics.Verb.Roots.Typology

/-!
# Beavers & Koontz-Garboden (2020): The Roots of Verbal Meaning

@cite{beavers-koontz-garboden-2020} @cite{rappaport-hovav-levin-2010}

Six representative roots illustrating the four-feature typology of
@cite{beavers-koontz-garboden-2020}, and falsifying both the
Bifurcation Thesis of Roots and Manner/Result Complementarity
(@cite{rappaport-hovav-levin-2010}).

| Root      | state | manner | result | cause | violates B? | M ∧ R? |
|-----------|-------|--------|--------|-------|-------------|--------|
| √flat     |   ✓   |        |        |       |             |        |
| √jog      |       |   ✓    |        |       |             |        |
| √blossom  |       |        |   ✓    |       |     ✓       |        |
| √crack    |       |        |   ✓    |   ✓   |             |        |
| √hand     |   ✓   |   ✓    |   ✓    |   ✓   |     ✓       |   ✓    |
| √eat      |       |   ✓    |   ✓    |   ✓   |     ✓       |   ✓    |

The B-violation column flags ontological + eventive overlap. √hand and
√eat additionally violate Manner/Result Complementarity. (√blossom is
listed by B&K-G as eventive-only result; that is sufficient on its own
to falsify the strongest form of Bifurcation, since result is
*template* content under that thesis.)

This file is the Phase A vertical slice of a larger refactor that will
re-derive Levin classes (English) and Bohnemeyer's verb-stem classes
(Yukatek) as orbits under per-language derivational operators.
-/

namespace Phenomena.ArgumentStructure.Studies.BeaversKoontzGarboden2020

open Semantics.Verb.Roots

-- ════════════════════════════════════════════════════
-- § 1. Six Representative Roots
-- ════════════════════════════════════════════════════

/-- √flat — pure state (-manner, -result, -cause). -/
def flat : Root := ⟨"flat", [.hasState "flat"]⟩

/-- √jog — pure manner of motion. -/
def jog : Root := ⟨"jog", [.hasManner "jogging-gait", .motion]⟩

/-- √blossom — spontaneous result with no specified manner or cause
    (an "internally caused" change of state). -/
def blossom : Root := ⟨"blossom", [.becomesState "flowering"]⟩

/-- √crack — caused result without specified manner. -/
def crack : Root := ⟨"crack", [.becomesState "fissured", .hasCause]⟩

/-- √hand — full feature load: state, manner, result, cause.
    Falsifies both the Bifurcation Thesis and Manner/Result
    Complementarity (@cite{beavers-koontz-garboden-2020} ch. 5). -/
def hand : Root := ⟨"hand",
  [.hasState "in-recipient-possession",
   .hasManner "by-hand-transfer",
   .becomesState "possessed",
   .hasCause]⟩

/-- √eat — manner + result + cause. The Yukatek `haan` "eat" case:
    classified as inactive (state-change) yet internally caused, an
    awkward exception under simpler frameworks. -/
def eat : Root := ⟨"eat",
  [.hasManner "consumption", .becomesState "consumed", .hasCause]⟩

-- ════════════════════════════════════════════════════
-- § 2. Feature Signatures
-- ════════════════════════════════════════════════════

theorem flat_signature :
    flat.featureSignature = ⟨true, false, false, false⟩ := rfl

theorem jog_signature :
    jog.featureSignature = ⟨false, true, false, false⟩ := rfl

theorem blossom_signature :
    blossom.featureSignature = ⟨false, false, true, false⟩ := rfl

theorem crack_signature :
    crack.featureSignature = ⟨false, false, true, true⟩ := rfl

theorem hand_signature :
    hand.featureSignature = ⟨true, true, true, true⟩ := rfl

theorem eat_signature :
    eat.featureSignature = ⟨false, true, true, true⟩ := rfl

-- ════════════════════════════════════════════════════
-- § 3. Falsification of the Bifurcation Thesis
-- ════════════════════════════════════════════════════

/-- √hand carries both ontological (state, manner) and eventive
    (result, cause) entailments — a structural counterexample to the
    Bifurcation Thesis of Roots. -/
theorem hand_violates_bifurcation :
    hand.ViolatesBifurcation := by decide

/-- √eat is a second counterexample: manner *and* result+cause. -/
theorem eat_violates_bifurcation :
    eat.ViolatesBifurcation := by decide

/-- The universal closure of the Bifurcation Thesis is false. -/
theorem bifurcation_thesis_false :
    ¬ ∀ r : Root, r.RespectsBifurcation := fun h =>
  h hand hand_violates_bifurcation

-- ════════════════════════════════════════════════════
-- § 4. Falsification of Manner/Result Complementarity
-- ════════════════════════════════════════════════════

/-- √hand entails both manner ("by-hand-transfer") AND result
    ("possessed") — a counterexample to Manner/Result
    Complementarity (@cite{rappaport-hovav-levin-2010}). -/
theorem hand_has_manner_and_result :
    hand.HasMannerAndResult := by decide

/-- √eat is a second counterexample: manner ("consumption") + result
    ("consumed"). -/
theorem eat_has_manner_and_result :
    eat.HasMannerAndResult := by decide

/-- The universal closure of Manner/Result Complementarity is false. -/
theorem manner_result_complementarity_false :
    ¬ ∀ r : Root, r.RespectsMannerResultComplementarity := fun h =>
  h hand hand_has_manner_and_result

-- ════════════════════════════════════════════════════
-- § 5. Roots that DO respect each constraint
-- ════════════════════════════════════════════════════

/-- √flat (pure state) and √jog (pure manner) respect Bifurcation. -/
theorem pure_ontological_respects_bifurcation :
    flat.RespectsBifurcation ∧ jog.RespectsBifurcation := by
  refine ⟨?_, ?_⟩ <;> decide

/-- √crack (result + cause, no manner or state) respects Manner/Result
    Complementarity. -/
theorem crack_respects_manner_result :
    crack.RespectsMannerResultComplementarity := by decide

end Phenomena.ArgumentStructure.Studies.BeaversKoontzGarboden2020
