/-!
# Root families: category-changing morphology
[marantz-1997]

A root family records the word forms a single (sub-morphemic) root projects
across lexical categories — the [marantz-1997] uncategorised-roots pattern:
the category of the surface word is determined by the morphological
environment, not by the root itself. This is the *category-neutral lexical*
root, distinct from the consonantal melody `Morphology.Root` and the
lexical-semantic `Verb.Root`; identifying it with either is a framework
claim that lives in the study asserting it, not here.

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

/-- The family has a form in category `c`. -/
def RootFamily.HasCategory (rf : RootFamily) (c : LexCat) : Prop :=
  ∃ f ∈ rf.forms, f.2 = c

instance (rf : RootFamily) (c : LexCat) : Decidable (rf.HasCategory c) :=
  List.decidableBEx _ rf.forms

end Morphology
