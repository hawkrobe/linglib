module

public import Linglib.Semantics.Conditionals.Reading

/-!
# Mandarin conditional markers

The Mandarin conditional marker *rúguǒ* 如果, typed by `Conditional.Marker`. It marks either
reading; the O-marking and X-marking of a Mandarin conditional is carried by perfective *le* 了
in the consequent rather than by the marker ([mizuno-2024]).

## References

* [mizuno-2024]
-/

@[expose] public section

namespace Mandarin.Conditionals

/-- *rúguǒ* 如果 marks either reading; in [mizuno-2024]'s Anderson conditionals
(ex. 13a) it heads both the O-marked and the X-marked variant. -/
def ruguo : Conditional.Marker := ⟨"rúguǒ", {.hypothetical, .premise}⟩

end Mandarin.Conditionals
