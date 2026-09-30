module

/-!
# Stage-level and individual-level predicates

[milsark-1974] divides predicates into states, roughly temporary (*hungry*, *drunk*,
*available*), and properties, roughly permanent (*fat*, *tall*, *clever*). A bare plural subject
reads existentially with a state and generically with a property, and [carlson-1977] derives the
split by predicating a state of a stage of an individual, a temporally and spatially bounded
realization of it, and a property of the individual itself (`Studies/Carlson1977.lean`, where a
state is the image of a property of stages under the realization relation). The two classes are
now called stage-level and individual-level. `PredicateLevel` is the label the accounts share as
a lexical index: `Studies/Magri2009.lean` reads individual-level as permanence in common
knowledge, and `Studies/Solt2018b.lean` lets the level choose the measure functions a quantity
word may use.

## References

* [milsark-1974]
* [carlson-1977]
-/

@[expose] public section

namespace Genericity

/-- The level of a predicate: stage-level, [milsark-1974]'s states, or individual-level, his
properties. -/
inductive PredicateLevel where
  /-- A predicate of stages, such as *available*. -/
  | stageLevel
  /-- A predicate of individuals, such as *tall*. -/
  | individualLevel
  deriving DecidableEq, Repr

end Genericity
