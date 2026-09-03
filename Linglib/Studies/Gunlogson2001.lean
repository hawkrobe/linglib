import Linglib.Data.Examples.Gunlogson2001
import Linglib.Discourse.Commitment.Declarative

/-!
# Gunlogson 2001: rising declaratives

Rising and falling declaratives are the updates `Commitment.rising` and `Commitment.falling`
of [gunlogson-2001]: the same content enters the addressee's or the speaker's commitment set.
The paper's data on the pair *It's raining* / *It's raining?* record that only the falling
declarative commits the speaker and that the rising one attributes the content to the
addressee, which is what the two updates do.

## Main results

* `rising_addressee`, `falling_speaker` — which commitment set each intonation narrows.
* `data_matches_theory` — the data rows record the same profile.

## References

* [C. Gunlogson, *True to Form: Rising and Falling Declaratives as Questions in English*
  (2001)][gunlogson-2001]
-/

namespace Gunlogson2001

open Commitment
open Discourse (DiscourseRole)

variable {W : Type*} (K : Set (Commitment DiscourseRole W)) (p : Set W)

/-- A rising declarative narrows the addressee's commitment set, attributing `p`, and leaves the
speaker's untouched. -/
theorem rising_addressee :
    commitmentSet (rising K p) .addressee = p ∩ commitmentSet K .addressee ∧
      commitmentSet (rising K p) .speaker = commitmentSet K .speaker :=
  commitmentSet_rising K p

/-- A falling declarative narrows the speaker's commitment set and leaves the addressee's
untouched. -/
theorem falling_speaker :
    commitmentSet (falling K p) .speaker = p ∩ commitmentSet K .speaker ∧
      commitmentSet (falling K p) .addressee = commitmentSet K .addressee :=
  commitmentSet_falling K p

/-- The rising row records no speaker commitment and attribution to the addressee. -/
theorem data_matches_theory :
    Examples.rising_decl.paperFeatures.lookup "speaker_commits" = some "false" ∧
    Examples.rising_decl.paperFeatures.lookup "attributed_to_addressee" = some "true" ∧
    Examples.falling_decl.paperFeatures.lookup "speaker_commits" = some "true" := by
  decide

end Gunlogson2001
