import Linglib.Fragments.Slavic.Case

/-!
# Cassubian Case Inventory
[stone-1993-cassubian] [blake-1994]

Per [stone-1993-cassubian] (p. 769): "The seven cases are the
same as in Polish, but the tendency for the nominative to replace the
vocative is greater than in Polish. The locative never occurs without
a preposition, and there is a strong tendency for the instrumental to
acquire the preposition z(s)/ze(se) 'with', when used with its basic
function as an expression of instrument (but not in the complement of
the copula)."

Cassubian thus patterns with Polish, Czech, Serbo-Croat, and
Ukrainian as 7-case with productive (but eroding) VOC.
`caseInventory` aliases the shared 6-case core; the +VOC form is
`Slavic.Case.sevenCaseInventory`. The exception clause "but not in the
complement of the copula" confirms the cross-Slavic generalization
that bare predicative INST survives — Slovene/Sorbian are the marked
outliers in losing it.
-/

namespace Cassubian.Case

abbrev caseInventory : Finset Case := Slavic.Case.coreInventory

end Cassubian.Case
