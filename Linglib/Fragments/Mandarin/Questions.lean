import Linglib.Syntax.Category.ANDLModifier

/-!
# Mandarin questions

Mandarin leaves its wh-phrases in situ, and the aggressively non-D-linked modifier 到底
*daodi* 'on earth' need not sit next to the wh-phrase it modifies: it moves to matrix Spec-CP
on its own ([chou-2012]), which is where [chan-shen-2026] locate its difference from English
and Singlish *the-hell*.

## References

* [chou-2012]
* [chan-shen-2026]
-/

namespace Mandarin.Questions

open ANDLModifier

/-- 到底 *daodi* 'on earth': moves to its scope position on its own. -/
def daodi : ANDLModifier :=
  { form := "daodi", gloss := "on earth", mobility := .independent }

end Mandarin.Questions
