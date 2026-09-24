module

public import Linglib.Semantics.Polarity.Marking

/-!
# Spanish polarity marking

Spanish asserts a fact the speaker takes to have been contradicted or doubted, or sets it in
contrast, with *sí* 'yes' before the clause, often followed by *que*: *—María no vendrá. —Sí que
vendrá* '"María won't come." "She will come."' ([butt-benjamin-2019]).

## References

* [butt-benjamin-2019]
-/

@[expose] public section

namespace Spanish.PolarityMarking


/-- *sí (que)*, the clause-initial affirmation of a contradicted or contrasted fact. -/
abbrev siQue : PolarityMarker where
  label := "sí (que)"
  form := some "sí (que)"
  environments := {.correction, .contrast}
  strategy := .polarityReversal

/-- The polarity markers. -/
def allPolarityMarkings : List PolarityMarker := [siQue]

end Spanish.PolarityMarking
