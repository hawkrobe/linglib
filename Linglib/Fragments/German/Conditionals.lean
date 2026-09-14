import Linglib.Semantics.Conditionals.Reading

/-!
# German conditional markers

The German conditional markers *wenn* and *falls*, typed by `Conditional.Marker`. *Wenn* marks
either reading; *falls* marks only hypothetical conditionals ([lassiter-2025]).

## References

* [lassiter-2025]
-/

namespace German.Conditionals

/-- German *falls* 'in case' marks only hypothetical conditionals: it is unacceptable once the
antecedent has been asserted (22) and as the main marker of a bare left-nested conditional
(24) ([lassiter-2025]). -/
def falls : Conditional.Marker := ⟨"falls", {.hypothetical}⟩

/-- German *wenn* 'if, when' marks either reading, and heads a bare left-nested conditional
(23) ([lassiter-2025]). -/
def wenn : Conditional.Marker := ⟨"wenn", {.hypothetical, .premise}⟩

end German.Conditionals
