import Linglib.Morphology.Root.Consonantal

/-!
# Amharic consonantal roots

The roots of the type A verbal paradigms of [leslau-1995]'s reference grammar that
[faust-2026] discusses ((5), (12)): a regular triradical, a root whose stems have identical
final consonants, a root whose second stem consonant is palatalized, and the [a]-final and
hollow roots traditionally analysed with a nonconsonantal radical. The root identities
follow [faust-2026]; [broselow-1984] analyses `wd` as √wdd and `fdj` as biradical.

## References

* [faust-2026]
* [broselow-1984]
* [leslau-1995]
-/

namespace Amharic

open Morphology

/-- √sbr `break`: [säbbär-ä] PFV.3MSG, [säbr-o] GRND, [mäsbär] INF ((5a), (12a)). -/
def sbr : ConsonantalRoot String := ⟨["s", "b", "r"]⟩

/-- √wd `like`: [wäddäd-ä] PFV.3MSG, [wädd-o] GRND, [mäwdäd] INF (5b). -/
def wd : ConsonantalRoot String := ⟨["w", "d"]⟩

/-- √fdj `scorch`: [fäʤʤ-ä] PFV.3MSG, [fäʤt-o] GRND, [mäfʤät] INF ((5c), (12b)). -/
def fdj : ConsonantalRoot String := ⟨["f", "d", "j"]⟩

/-- √sma `hear`: [sämm-a] PFV.3MSG, [sämt-o] GRND, [mäsmat] INF (12c). -/
def sma : ConsonantalRoot String := ⟨["s", "m", "a"]⟩

/-- √sam `kiss`: [sam-ä] PFV.3MSG, [sam-o] GRND, [mäsam] INF (12d). -/
def sam : ConsonantalRoot String := ⟨["s", "a", "m"]⟩

/-- √hid `go`: [hed-ä] PFV.3MSG, [hed-o] GRND, [mähed] INF (12e). -/
def hid : ConsonantalRoot String := ⟨["h", "i", "d"]⟩

end Amharic
