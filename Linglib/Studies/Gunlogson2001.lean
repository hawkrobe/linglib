import Linglib.Data.Examples.Gunlogson2001
import Linglib.Discourse.Commitment.SourceMarked
import Mathlib.Data.Set.Basic

/-!
# Gunlogson Bridge: Rising Declaratives
[gunlogson-2001]

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

namespace Gunlogson2001

open Discourse.Gunlogson
open Discourse.Commitment (CommitmentSource)

-- ════════════════════════════════════════════════════
-- § 1. Rising = Other-Generated Source
-- ════════════════════════════════════════════════════

/-- Rising declaratives are modeled as other-generated commitments.

    The data says: rising declaratives do not commit the speaker and
    attribute content to the addressee. Gunlogson's `risingDeclarative`
    adds an other-generated commitment to the addressee's slate,
    leaving the speaker's slate unchanged. -/
theorem rising_is_other_generated {W : Type*}
    (s : GunlogsonState W) (p : Set W) :
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
    (s : GunlogsonState W) (p : Set W) :
    (s.fallingDeclarative p).speakerSlate.commitments.head?.map (·.source) =
      some CommitmentSource.selfGenerated :=
  rfl

-- ════════════════════════════════════════════════════
-- § 2. Data Bridge
-- ════════════════════════════════════════════════════

/-- The rising row of the "It's raining" pair records no speaker
    commitment and attribution to the addressee — the profile
    `rising_is_other_generated` derives from the mechanism. -/
theorem data_matches_theory :
    Examples.rising_decl.paperFeatures.lookup "speaker_commits" = some "false" ∧
    Examples.rising_decl.paperFeatures.lookup "attributed_to_addressee" = some "true" := by
  decide

/-- The falling row records speaker commitment — the profile
    `falling_is_self_generated` derives from the mechanism. -/
theorem falling_data_matches :
    Examples.falling_decl.paperFeatures.lookup "speaker_commits" = some "true" := by
  decide

end Gunlogson2001
