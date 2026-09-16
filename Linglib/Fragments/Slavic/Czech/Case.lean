import Linglib.Fragments.Slavic.Case

/-!
# Czech case inventory

Czech keeps the full seven cases of Slavic: the six-case core and a vocative that is
morphologically distinct in roughly half the singular noun paradigms and syncretic with the
nominative elsewhere ([short-1993-czech]).

## References

* [short-1993-czech]
-/

namespace Czech.Case

/-- The Czech cases: the seven-case Slavic inventory. -/
abbrev inventory : Finset Case := Slavic.Case.fullInventory

end Czech.Case
