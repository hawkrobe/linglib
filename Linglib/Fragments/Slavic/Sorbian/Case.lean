import Linglib.Fragments.Slavic.Case

/-!
# Sorbian Case Inventory (Upper and Lower)
[stone-1993-sorbian] [blake-1994]

Per [stone-1993-sorbian] (p. 614): "Upper Sorbian has seven cases
(nominative, vocative, accusative, genitive, dative, instrumental and
locative). Lower Sorbian, having lost the vocative, has only six
cases. All the dialects have at least six cases. ... Even in Upper
Sorbian it is only masculine nouns that have a separate vocative form
(and only in the singular). There is one exception to this rule: USo.
mać 'mother' has vocative singular maći."

Both varieties share the 6-case core (`coreInventory`); Upper Sorbian
adds a productive masc-sg VOC. The Lower Sorbian vocative is attested
"only in Jakubica's New Testament (1548)" — fossil only.

Stone (p. 614) also documents that "in both Upper and Lower Sorbian
the independent, prepositionless function of the instrumental has been
lost" — the marked Slavic INST-prepositional pattern (cf. Slovene per
[priestly-1993]; contrast with Russian [timberlake-1993] and
Cassubian [stone-1993-cassubian] where bare predicative INST is
robust).
-/

namespace Sorbian.Case

abbrev caseInventory : Finset Features.Case := Slavic.Case.coreInventory

end Sorbian.Case
