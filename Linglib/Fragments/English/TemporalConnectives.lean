module

public import Linglib.Semantics.Tense.Connective

/-!
# English temporal connectives

Lexical entries for the English temporal connectives of [heinamaki-1974] and [karttunen-1974]:
*before*, *after*, *when*, *while*, *as long as*, *whenever*, *as soon as*, *since*, *until*
with its variant *till*, and the deadline preposition *by*. English has one *until* for both of
Karttunen's uses, the durative and, under negation, the punctual; the entry records the durative
one, and the punctual use is the polarity item `English.PolarityItems.until_`.

## References

* [heinamaki-1974]
* [karttunen-1974]
-/

@[expose] public section

namespace English.TemporalConnectives

open Tense

/-- *before*: *she left before he arrived*. -/
def before : Connective := { form := "before", relation := .before }

/-- *after*: *she left after he arrived*. -/
def after : Connective := { form := "after", relation := .after }

/-- *when*: *she arrived when he left*. -/
def when_ : Connective := { form := "when", relation := .when_ }

/-- *while*: *she read while he slept*. -/
def while_ : Connective := { form := "while", relation := .while_ }

/-- *as long as*, synonymous with *while*: *I'll stay as long as you need me*. -/
def asLongAs : Connective := { form := "as long as", relation := .while_ }

/-- *whenever*: *whenever it rains, I carry an umbrella*. -/
def whenever : Connective := { form := "whenever", relation := .whenever }

/-- *as soon as*, an *after* with a proximity implicature: *he left as soon as she arrived*. -/
def asSoonAs : Connective := { form := "as soon as", relation := .after }

/-- *since*: *he has been happy since she arrived*. -/
def since : Connective := { form := "since", relation := .since }

/-- Durative *until*: *John slept until three*. -/
def until_ : Connective := { form := "until", relation := .until_ }

/-- *till*, the variant of *until*. -/
def till : Connective := { form := "till", relation := .until_ }

/-- *by*, the deadline: *he arrived by three*, at or before three. -/
def by_ : Connective := { form := "by", relation := .by_ }

end English.TemporalConnectives
