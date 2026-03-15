import Linglib.Core.Case

/-!
# Hungarian Case Inventory @cite{blake-1994}

Hungarian has **18 morphological cases** (one of the largest in Europe),
with agglutinative suffixes. Beyond the common grammatical cases, Hungarian
has a rich local case system and several abstract cases.

Our 19-value `Core.Case` can represent 11 of the 18:
- **Grammatical**: NOM (∅), ACC (-t), DAT (-nak / -nek), GEN (= DAT form)
- **Local**: INE (-ban / -ben), ELA (-ból / -ből), ILL (-ba / -be),
  ADE (-nál / -nél), ABL (-tól / -től), ALL (-hoz / -hez / -höz),
  SUPE (-n / -on / -en / -ön), SUBL (-ra / -re), DELA (-ról / -ről)
- **Other**: INST (-val / -vel), COM (= INST form), TRANS (-vá / -vé),
  ESS (-ul / -ül), CAUS (-ért), TERM (-ig), DISTR (-nként)

Cases with no Core.Case equivalent: essive, translative, terminative,
distributive, superessive, sublative, delative. We collapse the
internal/external/surface local triads like Finnish.

-/

namespace Fragments.Hungarian.Case

/-- Hungarian case inventory mapped to Core.Case (11 of 18). -/
def caseInventory : List Core.Case :=
  [.nom, .acc, .dat, .gen, .loc, .abl, .all, .inst, .com, .caus]

/-- Contiguous on Blake's hierarchy (ranks 6 down to 0). -/
theorem inventory_valid :
    Core.validInventory caseInventory = true := by native_decide

end Fragments.Hungarian.Case
