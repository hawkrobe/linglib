import Linglib.Fragments.Slavic.Case

/-!
# Belarusian Case Inventory
[mayo-1993] [blake-1994]

Per [mayo-1993] (p. 901): "Modern standard Belorussian has two
numbers, six cases and three genders. ... The vocative case can no
longer be regarded as a living category in the standard language,
which has only the remnants божа/boža from бог/boh 'god', браце/brace
from брат/brat 'brother', дружа/druža from друг/druh 'friend' and
сынку/synku from сынок/synók 'son' (as modes of address)."

Belarusian thus patterns with Russian, Slovene, and Slovak as 6-case
without productive VOC. The directory uses the modern English
spelling `Belarusian`; Mayo's chapter title and the original Comrie &
Corbett 1993 volume use `Belorussian`.
-/

namespace Belarusian.Case

abbrev caseInventory : Finset Case := Slavic.Case.coreInventory

end Belarusian.Case
