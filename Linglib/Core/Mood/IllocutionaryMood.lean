import Linglib.Core.Discourse.Roles
import Mathlib.Tactic.DeriveFintype

/-!
# Illocutionary Mood — the Speech-Act Force Category

The category of speech-act force a clause is associated with: declarative,
interrogative, imperative, promissive, exclamative. This is the F in F(p).

Distinct from:
- `Core.Mood.GramMood` (indicative/subjunctive morphology — see `Basic.lean`)
- `Minimalist.SpeechActs.SAPMood` (Speas & Tenny's 2×2 configuration)

The pair `(IllocutionaryMood, GramMood)` is `Core.Mood.ClauseType`.

This file contains only the *category* — the enum + its sole intrinsic
property `moodAuthority` (which participant has epistemic authority). The
*act-side* extensions (Searle classes, direction of fit, preparatory
conditions) live in `Core/Discourse/IllocutionaryForce.lean`, which imports
this file. The split keeps `Core/Mood/` framework-agnostic and free of
pragmatic-act commitments.

The `DiscourseRole` type lives in `Core/Discourse/Roles.lean` because it is
about discourse participants (speaker/addressee), not about mood.
-/

namespace Core.Mood

open Core.Discourse (DiscourseRole)

/-- Illocutionary mood — the speech-act force of an utterance.

    Distinct from `GramMood` (indicative/subjunctive morphology) and the
    Minimalist `SAPMood` (configurational). This classifies the pragmatic
    act performed — the F in F(p). -/
inductive IllocutionaryMood where
  | declarative
  | interrogative
  | imperative
  | promissive
  | exclamative
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Which participant holds epistemic authority for a given illocutionary mood.

    @cite{lakoff-1970}: in declaratives, imperatives, and promissives the
    speaker is the seat of knowledge; in interrogatives the addressee is. -/
def moodAuthority : IllocutionaryMood → DiscourseRole
  | .declarative   => .speaker
  | .interrogative  => .addressee
  | .imperative     => .speaker
  | .promissive     => .speaker
  | .exclamative    => .speaker

end Core.Mood
