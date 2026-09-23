module

public import Linglib.Syntax.Negation

/-!
# Hixkaryana negation

Hixkaryana, a Cariban language of Brazil, negates a verb with the suffix *-hɨra*, also *-hra*,
which deverbalizes it. The negated verb is the complement of the copula, and the
copula carries the person, tense, aspect, number and mood marking that the verb carries in the
affirmative: *kɨ-amryekɨ-no* 'I went hunting', *amryekɨ-hɨra w-ah-ko* 'I did not go hunting'.
The examples are those of [miestamo-2005], from Derbyshire's grammar.

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation Morphology

namespace Hixkaryana.Negation

/-- The deverbalizing negative suffix *-hɨra*. -/
def hira : Marker := { pieces := [[.suff "hɨra"]] }

/-- The immediate past of *amryekɨ* 'hunt', first person subject. -/
def pairs : List Pair :=
  [⟨[.pref "kɨ", .root "amryekɨ", .suff "no"],
    [.root "amryekɨ", .suff "hɨra", .pref "w", .root "ah", .suff "ko"]⟩]

end Hixkaryana.Negation
