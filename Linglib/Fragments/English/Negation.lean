module

public import Linglib.Syntax.Negation

/-!
# English negation

English negates a declarative verbal clause with the particle *not*, contracted *n't*, placed
after the first auxiliary: *chris is not dancing*. A clause in a simple tense has no auxiliary,
and its negative is built on *do*, which carries the tense and agreement while the lexical verb
is bare: *chris does not dance*. The same periphrasis serves in the affirmative for emphasis,
*chris does dance*, so a simple tense has two affirmatives, plain and emphatic, and one negative.
Miestamo's examples are rows of `Data.Examples.Miestamo2005`.

## References

* [miestamo-2005]
-/

@[expose] public section

open Negation

namespace English.Negation

/-- *not*, the standard negator. -/
def not : Marker := { pieces := [[.free "not"]] }

/-- *n't*, the contracted negator, an enclitic on the auxiliary. -/
def nt : Marker := { pieces := [[.encl "n't"]] }

/-- The standard negators. -/
def standard : List Marker := [not, nt]

end English.Negation
