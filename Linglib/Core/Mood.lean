import Linglib.Semantics.Mood.Basic
import Linglib.Semantics.Mood.IllocutionaryMood
import Linglib.Semantics.Mood.ClauseType
import Linglib.Semantics.Mood.POSW
import Linglib.Semantics.Mood.POSWQ
import Linglib.Semantics.Mood.POSWTarget
import Linglib.Semantics.Mood.PartitionAsInquiry

/-!
# Semantics.Mood — re-export hub

Imports the three mood-category files so that downstream code can write
`import Linglib.Semantics.Mood` instead of cherry-picking each subfile.

The split mirrors mathlib's "one concept per file" discipline:

- `Semantics/Mood/Categories.lean` — `GramMood` (indicative/subjunctive),
  `SubjunctiveType`, `MoodEffect`
- `Semantics/Mood/IllocutionaryMood.lean` — `IllocutionaryMood`
  (declarative/interrogative/imperative/promissive/exclamative) +
  `moodAuthority`
- `Semantics/Mood/ClauseType.lean` — `ClauseType = IllocutionaryMood × GramMood`,
  bridge from `UD.Mood`

The pragmatic-act extensions of force (Searle classes, direction of fit,
preparatory conditions) live in `Discourse/IllocutionaryForce.lean`
because they are pragmatic-theoretic, not mood-categorial. The
`DiscourseRole` (speaker/addressee) lives in `Discourse/Roles.lean`.
-/
