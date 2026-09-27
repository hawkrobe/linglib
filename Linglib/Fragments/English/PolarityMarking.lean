module

public import Linglib.Semantics.Polarity.Marking

/-!
# English polarity marking

English marks affirmative polarity focus with an accented finite auxiliary. A clause in a simple
tense has no auxiliary, so the accent falls on *do*: emphatic *do* is the finite auxiliary *do*
where neither negation, inversion nor an empty verb calls for it, and it is always accented,
*they DO want that* against the reduced *do* of *what do they want?*. The context supplies a
proposition the assertion contradicts or settles: a negative claim, *you're wrong, she DID leave
her husband*; a presupposed or modalised negative; or the same predication of another subject,
*Bill doesn't have a lot of patients, but Mary DOES*. [wilder-2013] distinguishes two sentence
types by what else is accented: in a Verum-focus sentence any further accent is a focus accent,
and in a contrastive-topic sentence the subject, verb phrase or object bears the fall-rise
contrastive-topic accent. Both types realise the same polarity focus, so the fragment records one
device; the contrastive-topic mark is a property of the sentence, and its consequences are the
subject of `Studies/Wilder2013.lean`.

## Main definitions

* `English.PolarityMarking.emphaticDo`: accented finite *do*, a Verum-focus device.

## References

* [wilder-2013]
-/

@[expose] public section

namespace English.PolarityMarking

open PolarityMarker

/-- Emphatic *do*: the accented finite auxiliary *do* of an affirmative simple-tense clause,
Verum focus on the auxiliary. It is sentence-internal, and available in correction, *she DID
leave her husband* after *Sue didn't leave her husband*, and in contrast, *Mary DOES have a lot
of patients* after *Bill doesn't have a lot of patients*. -/
abbrev emphaticDo : PolarityMarker where
  label := "emphatic do"
  prosodicTarget := some "finite auxiliary do"
  environments := {.sentenceInternal, .contrast, .correction}
  strategy := .verumFocus

/-- The polarity-marking devices. -/
def markers : List PolarityMarker := [emphaticDo]

end English.PolarityMarking
