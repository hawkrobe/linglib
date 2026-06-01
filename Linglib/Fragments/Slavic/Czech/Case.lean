import Linglib.Fragments.Slavic.Case

/-!
# Czech Case Inventory
@cite{short-1993-czech} @cite{blake-1994}

Per @cite{short-1993-czech} (p. 466), the full seven cases survive in
Czech, with VOC morphologically distinct in roughly half the singular
noun paradigms (NOM-syncretic in plural, adjectives, pronouns,
numerals). `caseInventory` aliases the shared 6-case core;
`Slavic.Case.sevenCaseInventory` carries the +VOC form.
-/

namespace Czech.Case

abbrev caseInventory : Finset Features.Case := Slavic.Case.coreInventory

end Czech.Case
