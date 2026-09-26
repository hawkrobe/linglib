module

public import Linglib.Fragments.Slavic.Case

/-!
# Polish case inventory

This file defines the Polish cases, the seven of the Slavic inventory: "Polish has preserved the
full inherited case system, including the vocative, but there is a growing tendency to use the
nominative instead of the vocative for personal names. The vocative is consistently used with
titles and with personal names when they are used as part of a vocative phrase"
([rothstein-1993], p. 696), as in *panie Janku* and *kochana Basiu* 'dear Basia'.

## References

* [rothstein-1993]
-/

@[expose] public section

namespace Polish.Case

/-- The Polish cases are the seven of the Slavic inventory. -/
abbrev inventory : Finset Case := Slavic.Case.fullInventory

end Polish.Case
