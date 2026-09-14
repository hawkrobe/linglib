import Linglib.Semantics.Conditionals.Construal
import Linglib.Semantics.Modality.Exclusion

/-!
# Japanese conditional markers

The Japanese conditional markers *-ra* ~ *-tara*, *nara*, and *-(e)ba*, typed by
`Conditionals.Marker`, and the language's X-marking exponent. *-ra* marks only hypothetical
conditionals; *nara*, which doubles as a topic marker, marks either ([lassiter-2025]); *-(e)ba*
marks either, its Anderson and counterfactual uses distinguished by the consequent's tense
rather than by the marker ([mizuno-2024]).

## References

* [lassiter-2025]
* [mizuno-2024]
* [ogihara-2014]
* [mizuno-kaufmann-2019]
-/

namespace Japanese.Conditionals

/-- Japanese *-ra* ~ *-tara* marks only hypothetical conditionals: it is unacceptable once the
antecedent has been asserted (17) and as the main marker of a bare left-nested conditional
(19) ([lassiter-2025]). -/
def ra : Conditionals.Marker := ⟨"-ra", {.hypothetical}⟩

/-- Japanese *nara* marks either construal: it takes the premise reading when the antecedent
has been asserted (16) and heads a bare left-nested conditional (18) ([lassiter-2025]). -/
def nara : Conditionals.Marker := ⟨"nara", {.hypothetical, .premise}⟩

/-- Japanese *-(e)ba* attaches to sentence radicals and marks either construal: premise use in
Anderson conditionals ([mizuno-2024], ex. 4a), hypothetical use in future less vivid
conditionals (ex. 9a). -/
def eba : Conditionals.Marker := ⟨"-(e)ba", {.hypothetical, .premise}⟩

/-- Japanese X-marking: Fake Past -ta ([ogihara-2014], [mizuno-kaufmann-2019];
    [mizuno-2024] ex. 3). -/
def xMarking : Option Modality.Exclusion.XMarkingExponent := some ⟨"-ta", [.past]⟩

end Japanese.Conditionals
