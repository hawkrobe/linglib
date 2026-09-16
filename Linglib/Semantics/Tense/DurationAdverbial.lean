import Linglib.Semantics.Aspect.Basic

/-!
# Duration adverbials

This file defines the lexical entry of a duration adverbial, an adverbial that takes a measure
phrase and measures an interval rather than ordering two times: *for three hours*, *in three
hours*, *three days ago*, *in years*. An entry records the surface form, which interval the
measure applies to, whether the adverbial follows its measure phrase, and the aspectual class it
selects at the phrase it modifies, the *for* and *in* tests of [dowty-1979] being the diagnostics
(`Aspect.forXPrediction`, `Aspect.inXPrediction`).

An entry carries no truth conditions. How *in three hours* measures an event and what *in years*
measures from are contested, [rouillard-2026] against [iatridou-zeijlstra-2021], so a study
assigns denotations to the kinds it treats; a fragment says only which kind a word lexicalizes.
Polarity sensitivity is not recorded here either: *in years* is a `Polarity.Item` in its
language's polarity fragment.

## Main declarations

* `Tense.DurationAdverbial`: the lexical entry, with its `kind`, `postposition` flag and the
  telicity it `selects`.
* `Tense.DurationAdverbial.Kind`: the four intervals a duration adverbial can measure.

## References

* [dowty-1979]
* [vendler-1957]
* [rouillard-2026]
* [iatridou-zeijlstra-2021]
-/

namespace Tense

/-- The interval a duration adverbial measures: a telic event from onset to culmination
(*in three hours*), an atelic eventuality (*for three hours*), the offset from the utterance
time back to the event (*three days ago*), or the gap from the last event to the right edge of
the perfect time span (*in years*). -/
inductive DurationAdverbial.Kind where
  | completion
  | duration
  | offset
  | gap
  deriving DecidableEq, Repr

/-- A duration adverbial: a preposition or postposition taking a measure phrase and measuring an
interval. -/
structure DurationAdverbial where
  /-- The surface form. -/
  form : String
  /-- The interval the adverbial measures. -/
  kind : DurationAdverbial.Kind
  /-- Whether the adverbial follows its measure phrase, as *ago* does. -/
  postposition : Prop := False
  [decidablePostposition : Decidable postposition]
  /-- The aspectual class the adverbial selects at the phrase it modifies, if any. -/
  selects : Option Aspect.Telicity := none

instance (a : DurationAdverbial) : Decidable a.postposition := a.decidablePostposition

end Tense
