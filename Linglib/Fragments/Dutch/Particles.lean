module

public import Linglib.Semantics.Polarity.Marking

/-!
# Dutch polarity particles

Dutch marks a switch from negative to positive polarity with the sentence-internal affirmative
particle *wel*, accented in that use, the counterpart of the negation *niet*, [sudhoff-2012],
[hogeweg-2009]. In the production study of [turco-braun-dimroth-2014] it is the dominant
strategy in polarity contrast and in polarity correction, where German uses Verum focus.

## References

* [turco-braun-dimroth-2014]
* [sudhoff-2012]
* [hogeweg-2009]
-/

@[expose] public section

namespace Dutch.Particles

open PolarityMarker

/-- *wel*, the affirmative polarity particle: sentence-internal, accented, available in contrast
and in correction. -/
abbrev wel : PolarityMarker where
  label := "wel"
  form := some "wel"
  prosodicTarget := some "particle"
  environments := {.sentenceInternal, .contrast, .correction}
  strategy := .particle

end Dutch.Particles
