module

public import Linglib.Fragments.Slavic.Case

/-!
# Czech case inventory

This file defines the Czech cases, the seven of the Slavic inventory: "The full seven cases
survive" (Short, p. 465). About half the singular noun paradigms have a vocative "shared by no
other case", and "no adjectival, pronominal, numeral or plural noun paradigms have distinct
vocative forms (vocative = nominative)" (p. 465). A singular noun paradigm without a distinct
vocative may share it with a case other than the nominative, as *muži* 'man' and *stroji*
'machine' do with the dative and the locative (p. 466).

## References

* [short-1993-czech]
-/

@[expose] public section

namespace Czech.Case

/-- The Czech cases are the seven of the Slavic inventory. -/
abbrev inventory : Finset Case := Slavic.Case.fullInventory

end Czech.Case
