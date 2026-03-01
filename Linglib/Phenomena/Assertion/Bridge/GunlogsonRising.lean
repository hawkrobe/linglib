import Linglib.Phenomena.Assertion.Basic
import Linglib.Theories.Pragmatics.Assertion.Gunlogson
import Linglib.Theories.Pragmatics.Assertion.Stalnaker

/-!
# Gunlogson Bridge: Rising Declaratives
@cite{gunlogson-2001}

Connects Gunlogson's source-marking analysis to the rising declarative data.

## Prediction

Rising declaratives are assertions with **other-generated** source marking.
The speaker does not commit to the content; instead, they attribute it
to the addressee and invite confirmation or denial.

| Intonation | Gunlogson Operation | Source |
|------------|---------------------|--------|
| Falling ↓ | `fallingDeclarative` | self-generated |
| Rising ↑ | `risingDeclarative` | other-generated |

-/

namespace Phenomena.Assertion.Bridge.GunlogsonRising

open Theories.Pragmatics.Assertion.Gunlogson
open Core.Discourse.Commitment (CommitmentSource)
open Phenomena.Assertion

-- ════════════════════════════════════════════════════
-- § 1. Rising = Other-Generated Source
-- ════════════════════════════════════════════════════

/-- Rising declaratives are modeled as other-generated commitments.

    The data says: rising declaratives do not commit the speaker and
    attribute content to the addressee. Gunlogson's `risingDeclarative`
    adds an other-generated commitment to the addressee's slate,
    leaving the speaker's slate unchanged. -/
theorem rising_is_other_generated {W : Type*}
    (s : GunlogsonState W) (p : Core.Proposition.BProp W) :
    -- Rising adds other-generated commitment to addressee
    (s.risingDeclarative p).addresseeSlate.commitments.head?.map (·.source) =
      some CommitmentSource.otherGenerated ∧
    -- Speaker's slate unchanged
    (s.risingDeclarative p).speakerSlate = s.speakerSlate :=
  ⟨rfl, rfl⟩

/-- Falling declaratives are modeled as self-generated commitments.

    The data says: falling declaratives commit the speaker. Gunlogson's
    `fallingDeclarative` adds a self-generated commitment to the speaker's
    slate. -/
theorem falling_is_self_generated {W : Type*}
    (s : GunlogsonState W) (p : Core.Proposition.BProp W) :
    (s.fallingDeclarative p).speakerSlate.commitments.head?.map (·.source) =
      some CommitmentSource.selfGenerated :=
  rfl

-- ════════════════════════════════════════════════════
-- § 2. Data Bridge
-- ════════════════════════════════════════════════════

/-- The rising declarative data matches Gunlogson's prediction:
    rising → no speaker commitment, attributed to addressee. -/
theorem data_matches_theory :
    -- Data: rising declaratives don't commit the speaker
    (risingExamples.filter (·.isRising)).all (! ·.speakerCommits) = true ∧
    -- Theory: rising declaratives leave speaker's slate unchanged
    -- (captured by `rising_is_other_generated` above)
    -- Data: rising content is attributed to addressee
    (risingExamples.filter (·.isRising)).all (·.attributedToAddressee) = true :=
  ⟨rfl, rfl⟩

/-- The falling declarative data matches Gunlogson's prediction:
    falling → speaker commits. -/
theorem falling_data_matches :
    (risingExamples.filter (! ·.isRising)).all (·.speakerCommits) = true := rfl

-- ════════════════════════════════════════════════════
-- § 3. Stalnaker Cannot Model Rising Declaratives
-- ════════════════════════════════════════════════════

/-- Gunlogson's theory handles rising declaratives; Stalnaker's does not.

    This is because Gunlogson models source marking (the only theory to do so),
    and rising declaratives require distinguishing self- from other-generated
    commitments. -/
theorem gunlogson_advantage :
    Interfaces.AssertionTheory.modelsSourceMarking
      (T := GunlogsonTag) = true ∧
    Interfaces.AssertionTheory.modelsSourceMarking
      (T := Theories.Pragmatics.Assertion.Stalnaker.StalnakerTag) = false :=
  ⟨rfl, rfl⟩

end Phenomena.Assertion.Bridge.GunlogsonRising
