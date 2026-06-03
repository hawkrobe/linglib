import Linglib.Features.Person
import Linglib.Features.Number

/-!
# The Phi Kernel
[harbour-2016]

Every `Features.PhiFeatures` instance is equivalent to `PrivativePair` (`PhiFeatures.toEquiv`),
so any two are equivalent through that hub. `phiKernelEquiv` is the person/number edge,
`Person.Features ≃ Number.Features`; `Gender.Features`, Bantu animacy, and honorific level join
the same web for the same reason. The maps are of feature *carriers* (the bivalent two-feature
bundle).

[harbour-2016] singles this edge out as explanatorily central and names it the **phi kernel**
(Ch. 9); the emphasis is Harbour's, the equivalence the generic class fact. The two domains'
feature *values* denote differently — person's `±` are the operations `⊕`/`⊖` on the person
lattices, number's `+` the identity and `−` a type-flexible `¬` (§9.5.1) — so this equates
carriers, not denotations.

## Main declarations

* `phiKernelEquiv` — `Person.Features ≃ Number.Features`, composing each domain's `featuresEquiv`
  through the `PrivativePair` hub.
-/

namespace Features

/-- Person and number feature bundles are the same privative-pair skeleton, composed through
the `PrivativePair` hub: `1st ↔ singular`, `2nd ↔ dual`, `3rd ↔ plural`. One edge of the
generic φ-feature iso-web; [harbour-2016] singles it out as the **phi kernel** (Ch. 9).
Equates carriers, not denotations (§9.5.1). -/
def phiKernelEquiv : Person.Features ≃ Number.Features :=
  Person.featuresEquiv.trans Number.featuresEquiv.symm

end Features
