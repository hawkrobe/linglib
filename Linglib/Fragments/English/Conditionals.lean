import Linglib.Semantics.Conditionals.Construal
import Linglib.Semantics.Modality.Exclusion

/-!
# English conditional markers

The English conditional marker *if*, typed by `Conditionals.Marker`, and the language's
X-marking exponent ([iatridou-2000], [von-fintel-iatridou-2023]).

## References

* [iatridou-2000]
* [von-fintel-iatridou-2023]
-/

namespace English.Conditionals

/-- English *if* marks either construal; context decides between the hypothetical and the
premise reading. -/
def if_ : Conditionals.Marker := ⟨"if", {.hypothetical, .premise}⟩

/-- English X-marking: Fake Past ([iatridou-2000]); the consequent adds woll
    ([von-fintel-iatridou-2023] §2). -/
def xMarking : Option Modality.Exclusion.XMarkingExponent := some ⟨"Past", [.past, .future]⟩

end English.Conditionals
