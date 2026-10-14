module

public import Linglib.Syntax.Negation

/-!
# English negation

English negates a declarative verbal clause with the particle *not*, contracted *n't*, placed
after the first auxiliary: *chris is not dancing*. A clause in a simple tense has no auxiliary,
and its negative is built on *do*, which carries the tense and agreement while the lexical verb
is bare: *chris does not dance*. The same periphrasis serves in the affirmative for emphasis,
*chris does dance*, so a simple tense has two affirmatives, plain and emphatic, and one negative.
The examples are Miestamo's.

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

/-- The compound tenses, whose negative places *not* after the auxiliary. -/
def compoundTenses : List Pair :=
  [⟨not, ["chris", "is", "dancing"].map .free, ["chris", "is", "not", "dancing"].map .free⟩,
   ⟨not, ["chris", "will", "dance"].map .free, ["chris", "will", "not", "dance"].map .free⟩,
   ⟨not, ["chris", "has", "danced"].map .free, ["chris", "has", "not", "danced"].map .free⟩,
   ⟨not, ["chris", "had", "danced"].map .free, ["chris", "had", "not", "danced"].map .free⟩]

/-- The plain simple tenses with their negatives, built on *do*. -/
def simpleTenses : List Pair :=
  [⟨not, ["chris", "dances"].map .free, ["chris", "does", "not", "dance"].map .free⟩,
   ⟨not, ["chris", "danced"].map .free, ["chris", "did", "not", "dance"].map .free⟩]

/-- The emphatic simple tenses, built on *do* like their negatives. -/
def emphaticTenses : List Pair :=
  [⟨not, ["chris", "does", "dance"].map .free, ["chris", "does", "not", "dance"].map .free⟩,
   ⟨not, ["chris", "did", "dance"].map .free, ["chris", "did", "not", "dance"].map .free⟩]

end English.Negation
