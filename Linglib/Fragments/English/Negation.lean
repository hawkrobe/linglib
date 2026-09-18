import Linglib.Syntax.Negation

/-!
# English negation

English negates a declarative verbal clause with the particle *not*, contracted *n't*, placed
after the first auxiliary: *chris is not dancing*. A clause in a simple tense has no auxiliary,
and its negative is built on *do*, which carries the tense and agreement while the lexical verb
is bare: *chris does not dance*. The same periphrasis serves in the affirmative for emphasis,
*chris does dance*, so a simple tense has two affirmatives, plain and emphatic, and one negative.
The examples are those of [miestamo-2005].

## References

* [miestamo-2005]
-/

open Negation Morphology

namespace English.Negation

/-- *not*, the standard negator. -/
def not : Marker := { pieces := [[.free "not"]] }

/-- *n't*, the contracted negator, an enclitic on the auxiliary. -/
def nt : Marker := { pieces := [[.encl "n't"]] }

private def words (ws : List String) : List Morph := ws.map .free

/-- The compound tenses, whose negative places *not* after the auxiliary. -/
def compoundTenses : List Pair :=
  [⟨words ["chris", "is", "dancing"], words ["chris", "is", "not", "dancing"]⟩,
   ⟨words ["chris", "will", "dance"], words ["chris", "will", "not", "dance"]⟩,
   ⟨words ["chris", "has", "danced"], words ["chris", "has", "not", "danced"]⟩,
   ⟨words ["chris", "had", "danced"], words ["chris", "had", "not", "danced"]⟩]

/-- The plain simple tenses with their negatives, built on *do*. -/
def simpleTenses : List Pair :=
  [⟨words ["chris", "dances"], words ["chris", "does", "not", "dance"]⟩,
   ⟨words ["chris", "danced"], words ["chris", "did", "not", "dance"]⟩]

/-- The emphatic simple tenses, built on *do* like their negatives. -/
def emphaticTenses : List Pair :=
  [⟨words ["chris", "does", "dance"], words ["chris", "does", "not", "dance"]⟩,
   ⟨words ["chris", "did", "dance"], words ["chris", "did", "not", "dance"]⟩]

end English.Negation
