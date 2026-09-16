import Linglib.Semantics.Tense.DurationAdverbial

/-!
# English duration adverbials

Lexical entries for the English duration adverbials typed by `Tense.DurationAdverbial`: telic *in
three hours*, atelic *for three hours*, the postposition *three days ago*, and *in years*, which
measures the gap from the last witnessing event to the right edge of the perfect time span. Each
entry records which interval the measure applies to and the Vendler class the adverbial selects
([vendler-1957]). The polarity sensitivity of *in years* is `English.PolarityItems.inYears`, and
paper-specific apparatus, such as [rouillard-2026]'s labels, the domain-widening profile of
[iatridou-zeijlstra-2021] or the perfect-level classification of
[iatridou-anagnostopoulou-izvorski-2001], lives in the study that uses it.

## References

* [vendler-1957]
-/

namespace English.DurationAdverbials

open Tense

/-- Telic *in three days*: *Mary wrote a paper in three days*. Selects telic VPs. -/
def inTelic : DurationAdverbial := { form := "in", kind := .completion, selects := some .telic }

/-- *in years*: *Mary hasn't been sick in years*. The same preposition as `inTelic`, told apart by
position and licensing environment. -/
def inGap : DurationAdverbial := { form := "in", kind := .gap }

/-- *for three hours*: *Mary was sick for three hours*. Selects atelic VPs. -/
def forDur : DurationAdverbial := { form := "for", kind := .duration, selects := some .atelic }

/-- *three days ago*, the postposition locating an event a measured duration before the utterance
time. -/
def ago : DurationAdverbial := { form := "ago", kind := .offset, postposition := True }

end English.DurationAdverbials
