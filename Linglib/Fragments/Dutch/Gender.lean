import Linglib.Syntax.Gender.Basic

/-!
# Dutch gender

Dutch has two controller genders: the common gender of the *de*-words, the merger of the
historical masculine and feminine, which Broekhuis and den Dikken's grammar calls non-neuter,
and the neuter of the *het*-words. The definite article and the demonstratives distinguish them
in the singular only; that evidence is `Dutch.Determiners.singular`.

## References

* [broekhuis-dendikken-2012]
-/

namespace Dutch.Gender

/-- The two controller genders. -/
inductive Value where
  | common
  | neuter
  deriving DecidableEq, Repr, Fintype

/-- The comparative label of each gender. -/
def Value.toLabel : Value → Gender
  | .common => .common
  | .neuter => .neuter

end Dutch.Gender
