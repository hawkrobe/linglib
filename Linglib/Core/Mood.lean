import Linglib.Core.Mood.Basic
import Linglib.Core.Mood.IllocutionaryMood
import Linglib.Core.Mood.ClauseType
import Linglib.Core.Mood.POSW
import Linglib.Core.Mood.POSWQ
import Linglib.Core.Mood.POSWTarget
import Linglib.Core.Mood.InquisitiveContent
import Linglib.Core.Mood.PartitionAsInquiry

/-!
# Core.Mood — re-export hub

Imports the three mood-category files so that downstream code can write
`import Linglib.Core.Mood` instead of cherry-picking each subfile.

The split mirrors mathlib's "one concept per file" discipline:

- `Core/Mood/Basic.lean` — `GramMood` (indicative/subjunctive),
  `SubjunctiveType`, `MoodEffect`
- `Core/Mood/IllocutionaryMood.lean` — `IllocutionaryMood`
  (declarative/interrogative/imperative/promissive/exclamative) +
  `moodAuthority`
- `Core/Mood/ClauseType.lean` — `ClauseType = IllocutionaryMood × GramMood`,
  bridge from `UD.Mood`

The pragmatic-act extensions of force (Searle classes, direction of fit,
preparatory conditions) live in `Core/Discourse/IllocutionaryForce.lean`
because they are pragmatic-theoretic, not mood-categorial. The
`DiscourseRole` (speaker/addressee) lives in `Core/Discourse/Roles.lean`.
-/
