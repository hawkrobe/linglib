module

public import Linglib.Syntax.Category.Verb.Defs

/-!
# Chichewa verbs

The verb roots *mang-* 'tie', which is transitive, and *uk-* 'wake up', which is intransitive.

## References

* [hyman-mchombo-1992]
-/

@[expose] public section

namespace Chichewa.Verbs

/-- *mang-* 'tie'. -/
def mang : Verb where
  form := "mang"
  frames := [ArgumentFrame.np]

/-- *uk-* 'wake up'. -/
def uk : Verb where
  form := "uk"
  frames := [ArgumentFrame.intransitive]

end Chichewa.Verbs
