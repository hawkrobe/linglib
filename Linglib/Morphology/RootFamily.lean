/-!
# Root families: category-changing morphology
[marantz-1997]

A root family records the word forms a single (sub-morphemic) root projects
across lexical categories — the [marantz-1997] uncategorised-roots pattern:
the category of the surface word is determined by the morphological
environment, not by the root itself.

## Main declarations

- `Morphology.LexCat` — theory-neutral lexical category of a word form.
- `Morphology.RootFamily` — a root label with its category-stamped forms.

Consumers: `Studies/Panagiotidis2015.lean` (categoriser theory + the
English root-family sample), `Studies/McNallyDeSwart2011.lean`
(`AdjEntry.toRootFamily` adapter for Dutch adjective entries).
-/

namespace Morphology

/-- The lexical category of a word form (theory-neutral). -/
inductive LexCat where
  | noun
  | verb
  | adjective
  deriving Repr, DecidableEq

/-- A root family: a set of word forms derived from a common root,
    each appearing in a different lexical category. -/
structure RootFamily where
  /-- Label for the root (approximate; roots are sub-morphemic) -/
  rootLabel : String
  /-- Word forms and their categories -/
  forms : List (String × LexCat)
  deriving Repr

/-- Does this root family have a form in the given category? -/
def RootFamily.hasCategory (rf : RootFamily) (c : LexCat) : Bool :=
  rf.forms.any (·.2 == c)

end Morphology
