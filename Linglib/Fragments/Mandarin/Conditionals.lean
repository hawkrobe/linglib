import Linglib.Semantics.Conditionals.Construal

/-!
# Mandarin conditional markers

The Mandarin conditional marker *ruguo* (如果), typed by `Conditionals.Marker`. It marks either
construal; the O-marking and X-marking of a Mandarin conditional is carried by perfective *le*
(了) in the consequent rather than by the marker ([mizuno-2024]).

## References

* [mizuno-2024]
-/

namespace Mandarin.Conditionals

/-- Mandarin *ruguo* (如果) marks either construal; in [mizuno-2024]'s Anderson conditionals
(ex. 13a) it heads both the O-marked and the X-marked variant. -/
def ruguo : Conditionals.Marker := ⟨"ruguo", {.hypothetical, .premise}⟩

end Mandarin.Conditionals
